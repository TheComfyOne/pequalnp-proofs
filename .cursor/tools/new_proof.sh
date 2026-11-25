#!/usr/bin/env bash
# Cut a one-file proof branch from upstream/main and paste CircuitKit.
# Never include .cursor/ in the proof branch. Never open a PR.
set -euo pipefail

ROOT="$(git -C "$(dirname "$0")/../.." rev-parse --show-toplevel)"
KIT="${ROOT}/.cursor/lib/CircuitKit.lean"
UPSTREAM_REMOTE="${UPSTREAM_REMOTE:-upstream}"
UPSTREAM_REF="${UPSTREAM_REF:-upstream/main}"
NO_GIT=0
JSON=""
STATEMENT=""
IMPORTS="PEqualNP.Defs"
TITLE=""
KIND="check"
SKIP_CHECK=0
KIT_ALL=0
KIT_USE=""

usage() {
  cat <<'EOF'
Usage: .cursor/tools/new_proof.sh <gap-id> [options]

  --json FILE        pnp.sh / desk-next JSON (gap.id, gap.statement, gap.imports)
  --statement TEXT   Lean proposition if no JSON
  --imports LIST     extra import modules (comma or space); Mathlib is always added
  --title TEXT       one-line comment above the theorem
  --kind check|refute
  --kit-all          paste the whole CIRCUITKIT block (default for unknown shapes)
  --kit-use NAMES    comma/space names to keep, plus their kit dependencies
  --no-git           write the Lean file on the current tree; do not fetch or branch
  --skip-check       skip lake build and check-lean.mjs

Looks for a saved step at .pnp/<gap-id>.json, then --json, then --statement.
Cuts the branch from upstream/main so fork .cursor/ files stay off the PR.
Pastes only the kit decls the statement needs when that is obvious
(Monotone2 / Represents / size, or HasCircuitSize / lb_cert); never emits inductive.
EOF
}

GAP_ID=""
while [ $# -gt 0 ]; do
  case "$1" in
    -h|--help) usage; exit 0 ;;
    --json) JSON="${2:?}"; shift 2 ;;
    --statement) STATEMENT="${2:?}"; shift 2 ;;
    --imports) IMPORTS="${2:?}"; shift 2 ;;
    --title) TITLE="${2:?}"; shift 2 ;;
    --kind) KIND="${2:?}"; shift 2 ;;
    --kit-all) KIT_ALL=1; shift ;;
    --kit-use) KIT_USE="${2:?}"; shift 2 ;;
    --no-git) NO_GIT=1; shift ;;
    --skip-check) SKIP_CHECK=1; shift ;;
    -*) echo "unknown arg: $1" >&2; usage >&2; exit 2 ;;
    *)
      if [ -z "${GAP_ID}" ]; then GAP_ID="$1"; shift
      else echo "unexpected: $1" >&2; exit 2; fi
      ;;
  esac
done
[ -n "${GAP_ID}" ] || { usage >&2; exit 2; }
[ -f "${KIT}" ] || { echo "missing ${KIT}" >&2; exit 1; }

write_skeleton() {
  python3 - "${ROOT}" "${GAP_ID}" "${JSON}" "${STATEMENT}" "${IMPORTS}" "${TITLE}" "${KIT}" "${KIND}" "${KIT_ALL}" "${KIT_USE}" <<'PY'
import json, os, re, sys
root, gid, json_path, statement, imports, title, kit_path, kind, kit_all, kit_use = sys.argv[1:]

def load_json(path):
    with open(path, encoding="utf-8") as f:
        return json.load(f)

data = None
for p in ([json_path] if json_path else []) + [os.path.join(root, ".pnp", gid + ".json")]:
    if p and os.path.isfile(p):
        data = load_json(p)
        break

g = {}
if isinstance(data, dict):
    g = data.get("gap") if isinstance(data.get("gap"), dict) else data

if not re.fullmatch(r"[LR]-[A-Za-z]+-\d+(?:-\d+)?", gid):
    sys.exit("gap id must look like L-meta-5443")

mod_leaf = gid.replace("-", "_")
module = (g.get("module") or ("PEqualNP.Outside." + mod_leaf))
path = g.get("file") or ("lean/PEqualNP/Outside/" + mod_leaf + ".lean")
if not path.startswith("lean/PEqualNP/Outside/") or ".." in path:
    sys.exit("refusing unexpected file path %s" % path)
stmt = (g.get("statement") or statement or "").strip()
imps = g.get("imports") or []
if isinstance(imps, str):
    imps = [x for x in re.split(r"[\s,]+", imps) if x]
else:
    imps = [m for m in imps if isinstance(m, str)]
extra = [x for x in re.split(r"[\s,]+", imports) if x]
seen = set()
all_imps = []
for mname in ["Mathlib"] + extra + imps:
    if mname and mname not in seen and re.fullmatch(r"[A-Za-z0-9_.]+", mname):
        seen.add(mname)
        all_imps.append(mname)
title = g.get("title") or title or gid
aux = module + "_aux"
if not stmt:
    sys.exit("no statement: pass --statement or a pnp JSON with gap.statement")

kit = open(kit_path, encoding="utf-8").read()
m = re.search(r"-- CIRCUITKIT BEGIN\n(.*)\n-- CIRCUITKIT END", kit, re.S)
if not m:
    sys.exit("CircuitKit.lean is missing CIRCUITKIT BEGIN/END markers")
kit_body = m.group(1).rstrip() + "\n"
if re.search(r"\binductive\b", kit_body):
    sys.exit("CircuitKit paste would emit inductive; the kit must be inductive-free")

DECL_HEAD = re.compile(
    r"^(def|theorem|abbrev|instance|opaque)\s+((?:[A-Za-z_][\w']*)(?:\.[A-Za-z_][\w']*)*)\b",
    re.M,
)
IDENT = re.compile(r"[A-Za-z_][\w']*(?:\.[A-Za-z_][\w']*)*")

def split_kit(text: str):
    """Split into (leading_comment, [(name, chunk)])."""
    lines = text.splitlines(keepends=True)
    chunks = []
    buf = []
    name = None
    leading = []
    started = False
    def flush():
        nonlocal buf, name
        if name is None:
            return
        chunks.append((name, "".join(buf)))
        buf = []
        name = None
    for line in lines:
        hm = DECL_HEAD.match(line)
        if hm:
            started = True
            flush()
            name = hm.group(2)
            buf = [line]
        elif not started:
            leading.append(line)
        else:
            buf.append(line)
    flush()
    return "".join(leading), chunks

def idents_in(s: str):
    return set(IDENT.findall(s))

def prune_kit(text: str, seeds):
    if not seeds:
        return text
    lead, chunks = split_kit(text)
    by_name = {}
    order = []
    for n, c in chunks:
        order.append(n)
        by_name.setdefault(n, "")
        by_name[n] += c
    declared = set(by_name)
    # Also treat Foo as used when Foo.bar is declared.
    prefixes = {}
    for n in declared:
        prefixes.setdefault(n.split(".")[0], set()).add(n)
    needed = set()
    stack = list(seeds)
    while stack:
        n = stack.pop()
        if n in needed:
            continue
        if n in declared:
            needed.add(n)
            body = by_name[n]
            for ident in idents_in(body):
                if ident in declared and ident not in needed:
                    stack.append(ident)
                elif ident in prefixes:
                    for full in prefixes[ident]:
                        if full not in needed:
                            stack.append(full)
        elif n in prefixes:
            for full in prefixes[n]:
                if full not in needed:
                    stack.append(full)
    if not needed:
        return text
    kept = [by_name[n] for n in order if n in needed]
    out = lead + "".join(kept)
    if not out.endswith("\n"):
        out += "\n"
    return out

use_names = [x for x in re.split(r"[\s,]+", kit_use) if x]
auto = kit_all != "1" and not use_names
if auto:
    if re.search(r"\bHasCircuitSize\b|\blb_cert\b|\bNatRun\b|\bFanInTwo\b", stmt):
        use_names = ["lb_cert", "exists_run", "exists_run_m", "eval_eq", "size_eq_len",
                     "monotone2_of_and_or", "wires_eq"]
    elif re.search(r"\bMonotone2\b|\bRepresents\b", stmt):
        use_names = ["monotone2_of_and_or", "size_eq_len", "eval_eq", "wires_eq"]
if kit_all == "1":
    use_names = []
kit_body = prune_kit(kit_body, use_names)
if re.search(r"\binductive\b", kit_body):
    sys.exit("pruned CircuitKit paste still contains inductive")

parts = [f"import {mname}\n" for mname in all_imps]
parts.append("\n")
parts.append(f"namespace {aux}\n\n")
parts.append("open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity\n\n")
parts.append(kit_body)
parts.append(f"\nend {aux}\n\n")
parts.append(f"-- {title}\n")
parts.append(f"theorem {module} : {stmt} := by\n")
parts.append("  sorry\n")
text = "".join(parts)

full = os.path.join(root, path)
os.makedirs(os.path.dirname(full), exist_ok=True)
os.makedirs(os.path.join(root, ".pnp"), exist_ok=True)
open(os.path.join(root, ".pnp", "new_proof.last.json"), "w", encoding="utf-8").write(json.dumps({
    "id": gid, "file": path, "module": module, "aux": aux, "kind": kind, "title": title,
}, indent=1))
open(os.path.join(root, ".pnp", gid + ".statement.txt"), "w", encoding="utf-8").write(stmt + "\n")
open(full, "w", encoding="utf-8").write(text)
print("wrote %s (%d lines)" % (path, text.count("\n") + 1), file=sys.stderr)
PY
}

if [ "${NO_GIT}" != 1 ]; then
  git -C "${ROOT}" fetch "${UPSTREAM_REMOTE}" main
  if git -C "${ROOT}" show-ref --verify --quiet "refs/heads/${GAP_ID}"; then
    echo "branch ${GAP_ID} already exists; delete it first: git branch -D ${GAP_ID}" >&2
    exit 1
  fi
  git -C "${ROOT}" checkout -b "${GAP_ID}" "${UPSTREAM_REF}"
fi

write_skeleton

FILE="$(python3 -c 'import json,sys; print(json.load(open(sys.argv[1]))["file"])' "${ROOT}/.pnp/new_proof.last.json")"
MODULE="$(python3 -c 'import json,sys; print(json.load(open(sys.argv[1]))["module"])' "${ROOT}/.pnp/new_proof.last.json")"
STMT_FILE="${ROOT}/.pnp/${GAP_ID}.statement.txt"

echo "FILE      ${FILE}"
echo "MODULE    ${MODULE}"
echo "BRANCH    $(git -C "${ROOT}" rev-parse --abbrev-ref HEAD)"

if [ "${SKIP_CHECK}" = 1 ]; then
  echo "skip lake / check-lean"
  exit 0
fi

export PATH="/usr/local/bin:${HOME}/.elan/bin:${PATH}"
(cd "${ROOT}/lean" && lake build "${MODULE}")
node "${ROOT}/tools/check-lean.mjs" "${ROOT}/${FILE}" "${STMT_FILE}" "${KIND}"
