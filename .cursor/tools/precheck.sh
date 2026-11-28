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

# Forbidden tokens, desk kind, and import whitelist live in pnplib.py.
TOOLS="$(cd "$(dirname "$0")" && pwd)"
python3 "${TOOLS}/pnplib.py" precheck "${ROOT}" "${REL}"

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
