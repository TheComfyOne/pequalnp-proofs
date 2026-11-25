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

usage() {
  cat <<'EOF'
Usage: .cursor/tools/new_proof.sh <gap-id> [options]

  --json FILE        pnp.sh / desk-next JSON (gap.id, gap.statement, gap.imports)
  --statement TEXT   Lean proposition if no JSON
  --imports LIST     extra import modules (comma or space); Mathlib is always added
  --title TEXT       one-line comment above the theorem
  --kind check|refute
  --no-git           write the Lean file on the current tree; do not fetch or branch
  --skip-check       skip lake build and check-lean.mjs

Looks for a saved step at .pnp/<gap-id>.json, then --json, then --statement.
Cuts the branch from upstream/main so fork .cursor/ files stay off the PR.
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
  python3 - "${ROOT}" "${GAP_ID}" "${JSON}" "${STATEMENT}" "${IMPORTS}" "${TITLE}" "${KIT}" "${KIND}" <<'PY'
import json, os, re, sys
root, gid, json_path, statement, imports, title, kit_path, kind = sys.argv[1:]

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
