#!/usr/bin/env bash
# List desk gaps that have no open or merged PR in open-goat/pequalnp-proofs.
# A gap counts as claimed when its id appears anywhere in a PR title
# (hyphen or underscore form). Remaining gaps are printed easiest first.
set -euo pipefail

STATUS_URL="${STATUS_URL:-https://pequalnp.com/desk/status}"
REPO="${REPO:-open-goat/pequalnp-proofs}"
CACHE_DIR="${PEQUALNP_CACHE_DIR:-${HOME}/.cache/pequalnp-env}"
CACHE="${CACHE_DIR}/pr-titles.txt"
LIMIT="${LIMIT:-40}"
REFRESH=0
STATUS_FILE=""

usage() {
  cat <<'EOF'
Usage: .cursor/tools/open_steps.sh [--limit N] [--refresh] [--status FILE]

Fetch https://pequalnp.com/desk/status and list gaps with no open or merged
PR in open-goat/pequalnp-proofs whose title contains the gap id. Sorted by
an easiness heuristic (lower score first).
EOF
}

while [ $# -gt 0 ]; do
  case "$1" in
    --limit) LIMIT="${2:?}"; shift 2 ;;
    --refresh) REFRESH=1; shift ;;
    --status) STATUS_FILE="${2:?}"; shift 2 ;;
    -h|--help) usage; exit 0 ;;
    *) echo "unknown arg: $1" >&2; usage >&2; exit 2 ;;
  esac
done

mkdir -p "${CACHE_DIR}"

need_refresh() {
  [ "${REFRESH}" = 1 ] && return 0
  [ ! -f "${CACHE}" ] && return 0
  local age
  age="$(( $(date +%s) - $(stat -c %Y "${CACHE}" 2>/dev/null || echo 0) ))"
  [ "${age}" -gt 3600 ]
}

fetch_pr_titles() {
  if ! command -v gh >/dev/null 2>&1; then
    echo "gh is required to list PRs in ${REPO}" >&2
    exit 1
  fi
  echo "fetching open+merged PR titles from ${REPO}..." >&2
  # REST /pulls is not capped at 1000 the way search is. Keep only open or merged.
  gh api --paginate \
    "/repos/${REPO}/pulls?state=all&per_page=100" \
    --jq '.[] | select(.state == "open" or .merged_at != null) | .title' \
    > "${CACHE}.tmp"
  mv "${CACHE}.tmp" "${CACHE}"
  echo "cached $(wc -l < "${CACHE}") PR titles in ${CACHE}" >&2
}

if need_refresh; then
  fetch_pr_titles
else
  echo "using cached PR titles ($(wc -l < "${CACHE}")) from ${CACHE}" >&2
fi

TMPDIR_WORK="$(mktemp -d)"
trap 'rm -rf "${TMPDIR_WORK}"' EXIT
STATUS_JSON="${TMPDIR_WORK}/status.json"

if [ -n "${STATUS_FILE}" ]; then
  cp "${STATUS_FILE}" "${STATUS_JSON}"
else
  echo "fetching ${STATUS_URL}..." >&2
  curl -fsSL "${STATUS_URL}" -o "${STATUS_JSON}"
fi

ROOT="$(git -C "$(dirname "$0")/../.." rev-parse --show-toplevel 2>/dev/null || true)"
if [ -z "${ROOT}" ]; then
  ROOT="$(cd "$(dirname "$0")/../.." && pwd)"
fi
export REPO
export OPEN_STEPS_STATUS="${STATUS_JSON}"
export OPEN_STEPS_TITLES="${CACHE}"
export OPEN_STEPS_LIMIT="${LIMIT}"
export OPEN_STEPS_TOOLS="${ROOT}/.cursor/tools"

python3 - <<'PY'
import json, os, re, sys

sys.path.insert(0, os.environ["OPEN_STEPS_TOOLS"])
from pnplib import title_claims_gap  # noqa: E402

status_path = os.environ["OPEN_STEPS_STATUS"]
titles_path = os.environ["OPEN_STEPS_TITLES"]
limit = int(os.environ.get("OPEN_STEPS_LIMIT") or "40")

with open(status_path, encoding="utf-8") as f:
    status = json.load(f)
gaps = status.get("gaps") or []

titles = []
with open(titles_path, encoding="utf-8", errors="replace") as f:
    for line in f:
        t = line.strip()
        if t:
            titles.append(t)
titles_l = [t.lower() for t in titles]

def claimed(gid: str) -> bool:
    return title_claims_gap(gid, titles_l)

def ease(g: dict) -> float:
    """Lower is easier. Tuned for small-circuit / fixed-graph desk steps."""
    gid = g.get("id") or ""
    title = g.get("title") or ""
    t = title.lower()
    held = int(g.get("held") or 0)
    parallel = int(g.get("parallel") or 0)
    score = 0.0
    score += 100.0 * held
    score += 4.0 * max(parallel - 1, 0)
    if t.startswith("a step toward") or "a step toward:" in t:
        score += 50.0
    if t.startswith("it is false that"):
        score -= 12.0
    for needle, delta in (
        ("g2x2", -60.0),
        ("g2x3", -50.0),
        ("3-cube", -35.0),
        ("3 cube", -35.0),
        ("k_{2,2}", -55.0),
        ("k2,2", -55.0),
        ("k_{2,3}", -40.0),
        ("complete bipartite", -20.0),
        ("some fan-in-two", -25.0),
        ("some circuit", -20.0),
        ("computes its edge function", -18.0),
        ("edge function", -8.0),
    ):
        if needle in t:
            score += delta
    for needle, delta in (
        ("petersen", 90.0),
        ("heawood", 80.0),
        ("projective", 90.0),
        ("plane of order", 90.0),
        ("rung 0", 70.0),
        ("search shard", 40.0),
        ("search:", 25.0),
        ("lrat", 18.0),
    ):
        if needle in t:
            score += delta
    m = re.search(r"at most (\d+) gates", t)
    if m:
        n = int(m.group(1))
        if "some" in t or "computes" in t or t.startswith("search:"):
            score += 2.0 * n
        else:
            score += n
    m = re.search(r"at least (\d+) gates", t)
    if m:
        score += int(m.group(1))
    if title.strip() == gid:
        score += 30.0
    score += min(len(title), 400) / 50.0
    return score

open_gaps = []
for g in gaps:
    gid = g.get("id") or ""
    if not gid:
        continue
    if claimed(gid):
        continue
    open_gaps.append(g)

open_gaps.sort(key=lambda g: (ease(g), g.get("id") or ""))

print(
    f"# {len(open_gaps)} gaps with no open/merged PR in {os.environ.get('REPO', 'open-goat/pequalnp-proofs')}"
    f" (desk open_gaps={status.get('open_gaps')}, held_now={status.get('held_now')},"
    f" PR titles={len(titles)})"
)
print("# sorted by easiness heuristic (lower = easier); gap id matched anywhere in PR title")
shown = open_gaps if limit <= 0 else open_gaps[:limit]
for g in shown:
    gid = g.get("id")
    title = (g.get("title") or "").replace("\n", " ")
    print(
        f"{gid}\theld={int(g.get('held') or 0)}\tpar={int(g.get('parallel') or 0)}"
        f"\tease={ease(g):.1f}\t{title}"
    )
if limit > 0 and len(open_gaps) > limit:
    print(f"# ... {len(open_gaps) - limit} more; pass --limit 0 for all")
PY
