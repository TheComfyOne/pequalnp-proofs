#!/usr/bin/env bash
# Watch https://pequalnp.com/desk/status for newly posted gap ids.
#
# Every INTERVAL seconds (default 60), fetch the desk status, compare against
# the highest numeric id and the set of known ids in .pnp/seen.txt, and print
# newly posted gap ids + titles that have no open or merged pull request in
# open-goat/pequalnp-proofs whose title contains the gap id (hyphen or
# underscore form, anywhere in the title).
#
# State lives in .pnp/seen.txt (gitignored). Seed it once so the first poll
# does not dump every currently open gap as "new":
#   .cursor/tools/new_steps.sh --seed
#
# Usage:
#   .cursor/tools/new_steps.sh              # loop every 60s
#   .cursor/tools/new_steps.sh --once       # one poll
#   .cursor/tools/new_steps.sh --seed       # record current ids, print nothing
#   .cursor/tools/new_steps.sh --interval N
#   .cursor/tools/new_steps.sh --status FILE --titles FILE
#   .cursor/tools/new_steps.sh --push FILE  # precheck then git push -u origin HEAD
set -euo pipefail

STATUS_URL="${STATUS_URL:-https://pequalnp.com/desk/status}"
REPO="${REPO:-open-goat/pequalnp-proofs}"
ROOT="$(git -C "$(dirname "$0")/../.." rev-parse --show-toplevel 2>/dev/null || true)"
if [ -z "${ROOT}" ]; then
  ROOT="$(cd "$(dirname "$0")/../.." && pwd)"
fi
STATE_DIR="${PEQUALNP_STATE_DIR:-${ROOT}/.pnp}"
SEEN="${STATE_DIR}/seen.txt"
CACHE_DIR="${PEQUALNP_CACHE_DIR:-${HOME}/.cache/pequalnp-env}"
TITLE_CACHE="${CACHE_DIR}/pr-titles.txt"
INTERVAL="${INTERVAL:-60}"
ONCE=0
SEED=0
STATUS_FILE=""
TITLES_FILE=""
PUSH_FILE=""
PRECHECK="${ROOT}/.cursor/tools/precheck.sh"

usage() {
  cat <<'EOF'
Usage: .cursor/tools/new_steps.sh [--once] [--seed] [--interval N] [--status FILE] [--titles FILE]
       .cursor/tools/new_steps.sh --push FILE.lean

Fetch https://pequalnp.com/desk/status every 60s (or once). Compare gap ids to
.pnp/seen.txt (highest id + known ids). Print newly posted ids and titles with
no open/merged PR in open-goat/pequalnp-proofs (gap id anywhere in the title).

--push FILE runs .cursor/tools/precheck.sh FILE, then git push -u origin HEAD.
Every push from this script goes through precheck first.
EOF
}

while [ $# -gt 0 ]; do
  case "$1" in
    --once) ONCE=1; shift ;;
    --seed) SEED=1; ONCE=1; shift ;;
    --interval) INTERVAL="${2:?}"; shift 2 ;;
    --status) STATUS_FILE="${2:?}"; shift 2 ;;
    --titles) TITLES_FILE="${2:?}"; shift 2 ;;
    --push) PUSH_FILE="${2:?}"; shift 2 ;;
    -h|--help) usage; exit 0 ;;
    *) echo "unknown arg: $1" >&2; usage >&2; exit 2 ;;
  esac
done

mkdir -p "${STATE_DIR}" "${CACHE_DIR}"
[ -f "${SEEN}" ] || : > "${SEEN}"

need_title_refresh() {
  [ -n "${TITLES_FILE}" ] && return 1
  [ ! -f "${TITLE_CACHE}" ] && return 0
  local age
  age="$(( $(date +%s) - $(stat -c %Y "${TITLE_CACHE}" 2>/dev/null || echo 0) ))"
  [ "${age}" -gt 600 ]
}

fetch_pr_titles() {
  if [ -n "${TITLES_FILE}" ]; then
    echo "${TITLES_FILE}"
    return 0
  fi
  if ! command -v gh >/dev/null 2>&1; then
    echo "gh is required to list PRs in ${REPO}" >&2
    exit 1
  fi
  if need_title_refresh; then
    echo "fetching open+merged PR titles from ${REPO}..." >&2
    gh api --paginate \
      "/repos/${REPO}/pulls?state=all&per_page=100" \
      --jq '.[] | select(.state == "open" or .merged_at != null) | .title' \
      > "${TITLE_CACHE}.tmp"
    mv "${TITLE_CACHE}.tmp" "${TITLE_CACHE}"
    echo "cached $(wc -l < "${TITLE_CACHE}") PR titles in ${TITLE_CACHE}" >&2
  else
    echo "using cached PR titles ($(wc -l < "${TITLE_CACHE}")) from ${TITLE_CACHE}" >&2
  fi
  echo "${TITLE_CACHE}"
}

poll_once() {
  local tmp titles_path
  tmp="$(mktemp -d)"
  trap 'rm -rf "'"${tmp}"'"' RETURN
  if [ -n "${STATUS_FILE}" ]; then
    cp "${STATUS_FILE}" "${tmp}/status.json"
  else
    echo "fetching ${STATUS_URL}..." >&2
    curl -fsSL "${STATUS_URL}" -o "${tmp}/status.json"
  fi
  titles_path="$(fetch_pr_titles)"

  export NEW_STEPS_STATUS="${tmp}/status.json"
  export NEW_STEPS_SEEN="${SEEN}"
  export NEW_STEPS_TITLES="${titles_path}"
  export NEW_STEPS_SEED="${SEED}"
  export NEW_STEPS_REPO="${REPO}"
  export NEW_STEPS_TOOLS="${ROOT}/.cursor/tools"

  python3 - <<'PY'
import json, os, re, sys
from datetime import datetime, timezone

sys.path.insert(0, os.environ["NEW_STEPS_TOOLS"])
from pnplib import title_claims_gap  # noqa: E402

status_path = os.environ["NEW_STEPS_STATUS"]
seen_path = os.environ["NEW_STEPS_SEEN"]
titles_path = os.environ["NEW_STEPS_TITLES"]
seed = os.environ.get("NEW_STEPS_SEED") == "1"
repo = os.environ.get("NEW_STEPS_REPO") or "open-goat/pequalnp-proofs"

with open(status_path, encoding="utf-8") as f:
    status = json.load(f)
gaps = status.get("gaps") or []

def num(gid: str) -> int:
    m = re.search(r"(\d+)$", gid or "")
    return int(m.group(1)) if m else -1

known = set()
highest = -1
if os.path.isfile(seen_path):
    with open(seen_path, encoding="utf-8") as f:
        for line in f:
            line = line.strip()
            if not line or line.startswith("#"):
                m = re.match(r"#\s*highest\s+(\d+)", line)
                if m:
                    highest = max(highest, int(m.group(1)))
                continue
            known.add(line)
            highest = max(highest, num(line))

titles = []
with open(titles_path, encoding="utf-8", errors="replace") as f:
    for line in f:
        t = line.strip()
        if t:
            titles.append(t)
titles_l = [t.lower() for t in titles]

def claimed(gid: str) -> bool:
    return title_claims_gap(gid, titles_l)

fresh = []
now_ids = []
now_max = highest
for g in gaps:
    gid = g.get("id") or ""
    if not gid:
        continue
    now_ids.append(gid)
    n = num(gid)
    now_max = max(now_max, n)
    is_new = gid not in known or n > highest
    if is_new:
        fresh.append(g)

# Persist the known set and the highest id seen (including held/titled rows).
lines = [f"# highest {now_max}", f"# updated {datetime.now(timezone.utc).strftime('%Y-%m-%dT%H:%M:%SZ')}"]
lines.extend(sorted(set(now_ids) | known, key=lambda x: (num(x), x)))
os.makedirs(os.path.dirname(seen_path) or ".", exist_ok=True)
with open(seen_path, "w", encoding="utf-8") as f:
    f.write("\n".join(lines) + "\n")

if seed:
    print(
        f"# seeded {len(set(now_ids))} desk ids, highest={now_max}"
        f" (open_gaps={status.get('open_gaps')}, held_now={status.get('held_now')})",
        file=sys.stderr,
    )
    sys.exit(0)

fresh.sort(key=lambda g: num(g.get("id") or ""), reverse=True)
unclaimed = [g for g in fresh if not claimed(g.get("id") or "")]
print(
    f"# {len(unclaimed)} new unclaimed / {len(fresh)} newly posted"
    f" (desk open_gaps={status.get('open_gaps')}, held_now={status.get('held_now')},"
    f" highest={now_max}, PR titles={len(titles)}, repo={repo})"
)
print("# newest first; gap id matched anywhere in an open or merged PR title is omitted")
if not unclaimed:
    print("# (none)")
    sys.exit(0)
for g in unclaimed:
    gid = g.get("id") or ""
    title = (g.get("title") or "").replace("\n", " ")
    print(
        f"{gid}\theld={int(g.get('held') or 0)}\tpar={int(g.get('parallel') or 0)}"
        f"\t{title}"
    )
PY
}

push_proof() {
  local f="$1"
  if [ ! -x "${PRECHECK}" ]; then
    chmod +x "${PRECHECK}" 2>/dev/null || true
  fi
  if [ ! -f "${PRECHECK}" ]; then
    echo "missing ${PRECHECK}" >&2
    exit 1
  fi
  "${PRECHECK}" "${f}"
  local br
  br="$(git -C "${ROOT}" rev-parse --abbrev-ref HEAD)"
  git -C "${ROOT}" push -u origin HEAD
  echo "PUSHED ${br}"
}

if [ -n "${PUSH_FILE}" ]; then
  push_proof "${PUSH_FILE}"
  exit 0
fi

if [ "${ONCE}" = 1 ]; then
  poll_once
  exit 0
fi

echo "watching ${STATUS_URL} every ${INTERVAL}s (state ${SEEN})" >&2
while true; do
  poll_once || echo "poll failed; retrying in ${INTERVAL}s" >&2
  sleep "${INTERVAL}"
done
