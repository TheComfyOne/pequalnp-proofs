#!/usr/bin/env bash
# Guard a one-file proof before it is pushed.
# Fails if FILE contains inductive / sorry / axiom / native_decide, or if the
# branch diff vs upstream/main has more than that one Lean file (env paths
# under .cursor/ and .github/ are ignored).
set -euo pipefail

usage() {
  cat <<'EOF'
Usage: .cursor/tools/precheck.sh <file.lean>

Fails (exit 1) when:
  - FILE contains a whole-word inductive, sorry, axiom, or native_decide
  - the desk row is check/find and the theorem is ¬ of the posted statement
  - an import is not Mathlib / Mathlib.* / a module the desk row lists
  - the diff against upstream/main (plus the working tree) has more than
    one Lean file outside .cursor/ and .github/
EOF
}

if [ $# -lt 1 ] || [ "${1:-}" = "-h" ] || [ "${1:-}" = "--help" ]; then
  usage
  [ $# -ge 1 ] && [ "$1" = "-h" ] || [ "${1:-}" = "--help" ] && exit 0
  exit 2
fi

FILE="$1"
ROOT="$(git -C "$(dirname "$0")/../.." rev-parse --show-toplevel 2>/dev/null || true)"
if [ -z "${ROOT}" ]; then
  ROOT="$(cd "$(dirname "$0")/../.." && pwd)"
fi
UPSTREAM_REF="${UPSTREAM_REF:-upstream/main}"

if [ ! -f "${FILE}" ]; then
  echo "precheck: missing file ${FILE}" >&2
  exit 1
fi

# Resolve to a path relative to the repo root when possible.
REL="${FILE}"
case "${FILE}" in
  /*)
    REL="${FILE#"${ROOT}"/}"
    ;;
esac

python3 - "${FILE}" <<'PY'
import re, sys
path = sys.argv[1]
text = open(path, encoding="utf-8").read()
pat = re.compile(r"\b(inductive|sorry|axiom|native_decide)\b")
hits = []
for i, line in enumerate(text.splitlines(), 1):
    m = pat.search(line)
    if m:
        hits.append((i, m.group(1), line.strip()[:120]))
if hits:
    print("precheck: forbidden token in %s" % path, file=sys.stderr)
    for i, tok, snippet in hits[:20]:
        print("  %s:%d: %s  %s" % (path, i, tok, snippet), file=sys.stderr)
    sys.exit(1)
print("precheck: no inductive/sorry/axiom/native_decide in %s" % path, file=sys.stderr)
PY

# Desk kind: intake takes kind from GET /desk/row?gap=ID (find:true / missing
# kind => check). A check/find file must prove the posted statement, not ¬ S.
python3 - "${ROOT}" "${REL}" <<'PY'
import json, os, re, sys, urllib.request
from pathlib import Path

root, rel = sys.argv[1:]
rel = rel.replace("\\", "/")
stem = Path(rel).stem
if not stem.startswith("L_"):
    sys.exit(0)
gid = "L-" + stem[2:].replace("_", "-")
row_url = os.environ.get(
    "ROW_URL", "https://pequalnp-desk.pequalnp.workers.dev/desk/row?gap="
)
path = Path(root) / rel
if not path.is_file():
    path = Path(rel)
text = path.read_text(encoding="utf-8")

def last_thm_type(s: str):
    idx = s.rfind("theorem PEqualNP.Outside.")
    if idx < 0:
        return None
    rest = s[idx:]
    m = re.search(r"\s:=\s*by\b|\s:=", rest)
    if not m:
        return None
    head = rest[: m.start()]
    colon = head.find(":")
    if colon < 0:
        return None
    return head[colon + 1 :].strip()

thm = last_thm_type(text) or ""
thm_neg = thm.lstrip().startswith("¬") or thm.lstrip().startswith("(¬")

try:
    req = urllib.request.Request(row_url + gid, headers={"User-Agent": "precheck/1"})
    with urllib.request.urlopen(req, timeout=30) as r:
        blob = json.load(r)
except Exception as e:
    has_pnp = any(
        ln.startswith("import PEqualNP.") for ln in text.splitlines()
    )
    if thm_neg or has_pnp:
        print("precheck: cannot fetch desk row for %s (%s); refusing" % (gid, e), file=sys.stderr)
        sys.exit(1)
    print("precheck: desk row fetch failed for %s; no PEqualNP import and theorem is not a negation, continuing" % gid, file=sys.stderr)
    sys.exit(0)

row = None
for g in blob.get("gaps") or []:
    if g.get("id") == gid:
        row = g
        break
if not row:
    if thm_neg:
        print("precheck: desk has no open row for %s; refusing ¬ theorem" % gid, file=sys.stderr)
        sys.exit(1)
    print("precheck: desk has no open row for %s; theorem is not a negation, continuing" % gid, file=sys.stderr)
    sys.exit(0)

k = row.get("kind")
desk_kind = "refute" if k == "refute" else "check"
find = row.get("find") is True
posted = (row.get("statement") or "").strip()
posted_neg = posted.lstrip().startswith("¬") or posted.lstrip().startswith("(¬")
listed = [str(x) for x in (row.get("imports") or [])]
print("precheck: desk %s kind=%s find=%s imports=%s" % (gid, desk_kind, find, listed), file=sys.stderr)

import_rx = re.compile(r"^import ([A-Za-z][A-Za-z0-9_]*(?:\.[A-Za-z][A-Za-z0-9_]*)*)[ \t]*$")
for i, line in enumerate(text.splitlines(), 1):
    if not line.strip():
        continue
    m = import_rx.match(line)
    if not m:
        break
    name = m.group(1)
    if name == "Mathlib" or name.startswith("Mathlib."):
        continue
    if name not in listed:
        print(
            "precheck: line %d: import %s is not allowed (only Mathlib and the modules the gap lists)"
            % (i, name),
            file=sys.stderr,
        )
        sys.exit(1)
print("precheck: imports match desk whitelist", file=sys.stderr)

if desk_kind != "refute":
    if thm_neg and not posted_neg:
        print(
            "precheck: desk posts %s as kind %s (find=%s); the file must prove the posted statement, not its negation"
            % (gid, desk_kind, find),
            file=sys.stderr,
        )
        sys.exit(1)
    pn = re.sub(r"\s+", "", posted)
    tn = re.sub(r"\s+", "", thm)
    if pn and (tn.startswith("¬(" + pn) or tn.startswith("(¬(" + pn)):
        print(
            "precheck: theorem wraps ¬ around the posted statement of check/find row %s"
            % gid,
            file=sys.stderr,
        )
        sys.exit(1)
else:
    if not thm_neg:
        print(
            "precheck: desk posts %s as kind refute; the theorem must be ¬ of the posted statement"
            % gid,
            file=sys.stderr,
        )
        sys.exit(1)
print("precheck: desk kind %s matches theorem" % desk_kind, file=sys.stderr)
PY

python3 - "${ROOT}" "${UPSTREAM_REF}" "${REL}" <<'PY'
import os, subprocess, sys
root, upstream, rel = sys.argv[1:]
rel = rel.replace("\\", "/")
if rel.startswith("./"):
    rel = rel[2:]

def run(args):
    p = subprocess.run(args, cwd=root, capture_output=True, text=True)
    return p.returncode, p.stdout, p.stderr

def git_ok(args):
    code, out, err = run(["git"] + args)
    return code == 0, out, err

ok, _, _ = git_ok(["rev-parse", "--verify", upstream])
if not ok:
    # Fall back to origin/main only for the merge-base lookup; never print remotes.
    ok2, _, _ = git_ok(["rev-parse", "--verify", "origin/main"])
    if ok2:
        upstream = "origin/main"
    else:
        print("precheck: cannot resolve %s" % sys.argv[2], file=sys.stderr)
        sys.exit(1)

ok, mb, err = git_ok(["merge-base", "HEAD", upstream])
base = mb.strip() if ok and mb.strip() else upstream

names = []
for args in (
    ["diff", "--name-only", f"{base}...HEAD"],
    ["diff", "--name-only", base],
    ["diff", "--name-only", "--cached"],
    ["ls-files", "--others", "--exclude-standard"],
):
    ok, out, _ = git_ok(args)
    if ok:
        names.extend(out.splitlines())

skip_prefixes = (".cursor/", ".github/", ".pnp/")
lean = []
seen = set()
for n in names:
    n = n.strip().replace("\\", "/")
    if not n or n in seen:
        continue
    seen.add(n)
    if n.startswith(skip_prefixes):
        continue
    if n.endswith(".lean"):
        lean.append(n)

want = rel
if want not in lean:
    # The argument is the file we intend to push; count it even if unchanged.
    lean.append(want)

lean_u = sorted(set(lean))
if len(lean_u) != 1 or lean_u[0] != want:
    print("precheck: branch diff must contain exactly one Lean file (%s)" % want, file=sys.stderr)
    for n in lean_u:
        print("  lean: %s" % n, file=sys.stderr)
    sys.exit(1)
print("precheck: one Lean file in branch diff: %s" % want, file=sys.stderr)
PY
echo "precheck: ok ${REL}"
