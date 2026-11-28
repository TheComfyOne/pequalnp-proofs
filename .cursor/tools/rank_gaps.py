#!/usr/bin/env python3
"""One-shot ranking of open desk gaps, with a twin-pair sweep first.

Fetches desk status + gaps.json, diffs upstream/main since the last loop
for newly merged Outside lemmas, and matches open desk rows those lemmas
settle directly:

  too-small bound  -> refute via the lower-bound lemma
  bound >= witness -> prove via that construction

Those twins print first (diff 2–3). Then the usual cheap-row ranking.

Usage:
  .cursor/tools/rank_gaps.py
  .cursor/tools/rank_gaps.py --limit 20 --gh
  .cursor/tools/rank_gaps.py --kind lib,pcx
  .cursor/tools/rank_gaps.py --twins-only
  .cursor/tools/rank_gaps.py --twin-json
"""
from __future__ import annotations

import argparse
import json
import os
import re
import subprocess
import sys
import urllib.request
from pathlib import Path

STATUS_URL = os.environ.get("STATUS_URL", "https://pequalnp.com/desk/status")
GAPS_URL = os.environ.get(
    "GAPS_URL", "https://data.pequalnp.com/data/desk/gaps.json"
)
REPO = os.environ.get("REPO", "open-goat/pequalnp-proofs")

SKIP_TITLE = re.compile(
    r"table 2\b|monotone six-input|one not saves nothing|one-a-side|one a side"
    r"|7-cycle edges|counted gates for four row|two-lit function",
    re.I,
)
SKIP_STMT = re.compile(
    r"RepSizeAtMost|RepSize2AtMost|oneEach u v",
)
HARD = re.compile(
    r"TM2Computable|Turing\.TM2|NestedCover|Poisson|Gaussian|NP-complete"
    r"|ReadsBack|Equiv\.Perm|Matrix\.rank",
    re.I,
)
EASY_MATHLIB = re.compile(
    r"Finrank|BilinForm|LinearMap|Module\.|Finset\.card|Nat\.card|ZMod",
)
CIRCUIT_EXISTS = re.compile(
    r"∃ C : PEqualNP\.CircuitLowerBounds\.Circuit.*FanInTwo.*size ≤ (\d+)",
    re.S,
)
FIN_SMALL = re.compile(r"Fin ([1-8])")
THM_START = "theorem PEqualNP.Outside."
CMP_OPS = ("≤", "<", "≥", ">")


def fetch_json(url: str):
    req = urllib.request.Request(url, headers={"User-Agent": "rank-gaps/1"})
    with urllib.request.urlopen(req, timeout=60) as r:
        return json.load(r)


def num(gid: str) -> int:
    m = re.search(r"(\d+)$", gid or "")
    return int(m.group(1)) if m else -1


def lane(gid: str) -> str:
    if gid.startswith("L-lib-"):
        return "lib"
    if gid.startswith("L-pcx-"):
        return "pcx"
    if gid.startswith("L-meta-"):
        return "meta"
    if gid.startswith("L-clb-"):
        return "clb"
    return "other"


def gap_to_module(gid: str) -> str:
    return gid.replace("L-", "L_").replace("-", "_")


def module_to_gap(mod: str) -> str:
    body = mod[2:] if mod.startswith("L_") else mod
    return "L-" + body.replace("_", "-")


def lean_path(root: Path, gid: str) -> Path:
    return root / "lean" / "PEqualNP" / "Outside" / f"{gap_to_module(gid)}.lean"


def sibling_path(root: Path, gid: str) -> Path | None:
    p = lean_path(root, gid)
    return p if p.is_file() else None


def nearby_sibling_lines(root: Path, gid: str) -> int | None:
    """Median line count of nearby same-lane Outside files, if any exist."""
    prefix, n = gid.rsplit("-", 1)
    try:
        n = int(n)
    except ValueError:
        return None
    lens = []
    stem = prefix.replace("L-", "L_").replace("-", "_") + "_"
    outside = root / "lean" / "PEqualNP" / "Outside"
    if not outside.is_dir():
        return None
    for d in range(1, 6):
        for k in (n - d, n + d):
            q = outside / f"{stem}{k}.lean"
            if q.is_file():
                try:
                    lens.append(sum(1 for _ in q.open(encoding="utf-8", errors="replace")))
                except OSError:
                    pass
    if not lens:
        return None
    lens.sort()
    return lens[len(lens) // 2]


def difficulty(g: dict, root: Path) -> tuple[int, str]:
    title = g.get("title") or ""
    stmt = g.get("statement") or ""
    blob = title + "\n" + stmt
    reasons = []
    d = 5

    if SKIP_TITLE.search(title) or SKIP_STMT.search(stmt):
        return 9, "skip-family"

    if HARD.search(blob):
        d += 3
        reasons.append("tm2/circuit-machine")
    if len(stmt) > 2500:
        d += 2
        reasons.append("long-stmt")
    elif len(stmt) > 1200:
        d += 1
        reasons.append("med-stmt")

    m = CIRCUIT_EXISTS.search(stmt)
    if m:
        k = int(m.group(1))
        fins = [int(x) for x in FIN_SMALL.findall(stmt)]
        fin = min(fins) if fins else 99
        if k <= 3 and fin <= 4:
            d = min(d, 3)
            reasons.append("small-fanin-exists")
        elif k <= 5 and fin <= 4:
            d = min(d, 4)
            reasons.append("fanin-exists")
        else:
            d += 1
            reasons.append("bigger-circuit")

    if EASY_MATHLIB.search(stmt) and "Circuit" not in stmt and "Turing" not in stmt:
        d = min(d, 4)
        reasons.append("mathlib-shape")

    sib = nearby_sibling_lines(root, g["id"])
    if sib is not None:
        if sib <= 200:
            d = min(d, max(2, d - 2))
            reasons.append(f"short-sib:{sib}")
        elif sib <= 600:
            d = min(d, max(3, d - 1))
            reasons.append(f"mid-sib:{sib}")
        elif sib >= 2000:
            d += 2
            reasons.append(f"huge-sib:{sib}")

    d = max(1, min(10, d))
    return d, ",".join(reasons) or "base"


def gh_open_titles(ids: list[str]) -> set[str]:
    """Return gap ids that already have an open PR whose title contains the id."""
    hit = set()
    for gid in ids:
        try:
            p = subprocess.run(
                [
                    "gh",
                    "pr",
                    "list",
                    "-R",
                    REPO,
                    "--search",
                    f"{gid} in:title",
                    "--state",
                    "open",
                    "--json",
                    "number,title",
                ],
                capture_output=True,
                text=True,
                timeout=30,
            )
        except (OSError, subprocess.TimeoutExpired):
            continue
        if p.returncode != 0:
            continue
        try:
            rows = json.loads(p.stdout or "[]")
        except json.JSONDecodeError:
            continue
        if rows:
            hit.add(gid)
    return hit


def git_out(root: Path, args: list[str], timeout: int = 60) -> str:
    p = subprocess.run(
        ["git"] + args,
        cwd=root,
        capture_output=True,
        text=True,
        timeout=timeout,
    )
    if p.returncode != 0:
        return ""
    return p.stdout


def twin_state_path(root: Path) -> Path:
    env = os.environ.get("TWIN_STATE")
    if env:
        return Path(env)
    return root / ".pnp" / "twin-last-sha"


def read_last_sha(root: Path) -> str:
    p = twin_state_path(root)
    try:
        return p.read_text(encoding="utf-8").split()[0].strip()
    except (OSError, IndexError):
        return ""


def write_last_sha(root: Path, sha: str) -> None:
    p = twin_state_path(root)
    p.parent.mkdir(parents=True, exist_ok=True)
    p.write_text(sha.strip() + "\n", encoding="utf-8")


def ensure_upstream(root: Path, fetch: bool) -> str:
    sha = git_out(root, ["rev-parse", "upstream/main"]).strip()
    if fetch or not sha:
        subprocess.run(
            ["git", "fetch", "upstream", "main"],
            cwd=root,
            capture_output=True,
            text=True,
            timeout=120,
        )
        sha = git_out(root, ["rev-parse", "upstream/main"]).strip()
    return sha


def new_merged_names(root: Path, last_sha: str, head: str) -> list[str]:
    """Outside Lean paths that changed on upstream/main since last_sha."""
    names: list[str] = []
    if last_sha and head:
        diff = git_out(
            root,
            ["diff", "--name-only", f"{last_sha}..{head}", "--", "lean/PEqualNP/Outside"],
        )
        names = [n.strip() for n in diff.splitlines() if n.strip().endswith(".lean")]
    if not names:
        log = git_out(
            root,
            [
                "log",
                "--first-parent",
                "-n",
                "40",
                "--diff-filter=A",
                "--name-only",
                "--pretty=format:",
                head or "upstream/main",
                "--",
                "lean/PEqualNP/Outside",
            ],
        )
        names = [n.strip() for n in log.splitlines() if n.strip().endswith(".lean")]
    out = []
    seen = set()
    for n in names:
        n = n.replace("\\", "/")
        if not n or n in seen:
            continue
        if "/Outside/" not in n or not n.endswith(".lean"):
            continue
        seen.add(n)
        out.append(n)
    return out


def git_show_tail(root: Path, rev: str, rel: str, nbytes: int = 32768) -> str:
    p = subprocess.run(
        ["git", "show", f"{rev}:{rel}"],
        cwd=root,
        capture_output=True,
        timeout=60,
    )
    if p.returncode != 0 or not p.stdout:
        return ""
    data = p.stdout[-nbytes:]
    return data.decode("utf-8", "replace")


def new_merged_lean(root: Path, last_sha: str, head: str) -> list[Path]:
    """Disk paths for new Outside files that exist in this worktree."""
    outside = root / "lean" / "PEqualNP" / "Outside"
    out = []
    for n in new_merged_names(root, last_sha, head):
        p = root / n
        if p.is_file() and p.parent == outside:
            out.append(p)
    return out


def last_theorem_type(text: str) -> str | None:
    idx = text.rfind(THM_START)
    if idx < 0:
        return None
    rest = text[idx:]
    m = re.search(r"\s:= by\b", rest)
    if not m:
        m = re.search(r"\n\s*:= by\b", rest)
    if not m:
        return None
    head = rest[: m.start()]
    colon = head.find(":")
    if colon < 0:
        return None
    return head[colon + 1 :].strip()


def last_inequality(text: str) -> tuple[str, str, str] | None:
    """Last comparison in text as (left, op, right), operands whitespace-collapsed."""
    best_idx = -1
    best_op = ""
    for op in CMP_OPS:
        start = len(text)
        while True:
            idx = text.rfind(op, 0, start)
            if idx < 0:
                break
            # Do not treat Lean `=>` as a comparison.
            if op == ">" and idx > 0 and text[idx - 1] == "=":
                start = idx
                continue
            if op == "<" and idx + 1 < len(text) and text[idx + 1] == "=":
                start = idx
                continue
            if idx > best_idx:
                best_idx = idx
                best_op = op
            break
    if best_idx < 0:
        return None
    left = text[:best_idx]
    right = text[best_idx + len(best_op) :]
    # Keep the last line / last implication of the left operand.
    if "\n" in left:
        left = left.split("\n")[-1]
    for sep in (" → ", " ∧ ", ","):
        cut = left.rfind(sep)
        if cut >= 0:
            left = left[cut + len(sep) :]
    right = right.split("\n")[0]
    right = re.sub(r"\s:=.*$", "", right)

    def unwrap(s: str) -> str:
        s = s.strip()
        while len(s) >= 2 and s[0] == "(" and s[-1] == ")":
            depth = 0
            wrap = True
            for i, ch in enumerate(s):
                if ch == "(":
                    depth += 1
                elif ch == ")":
                    depth -= 1
                    if depth == 0 and i != len(s) - 1:
                        wrap = False
                        break
            if wrap and depth == 0:
                s = s[1:-1].strip()
            else:
                break
        return s

    left, right = unwrap(left), unwrap(right)
    if not left or not right:
        return None
    return (re.sub(r"\s+", " ", left), best_op, re.sub(r"\s+", " ", right))


def norm_expr(s: str) -> str:
    return re.sub(r"\s+", "", s or "")


def reverse_ops(op1: str, op2: str) -> bool:
    return {op1, op2} in ({"≤", "<"}, {"≥", ">"})


def ineq_reverse(a: tuple[str, str, str], b: tuple[str, str, str]) -> bool:
    return (
        reverse_ops(a[1], b[1])
        and norm_expr(a[0]) == norm_expr(b[2])
        and norm_expr(a[2]) == norm_expr(b[0])
    )


def read_tail(path: Path, nbytes: int = 8192) -> str:
    try:
        with path.open("rb") as f:
            f.seek(0, 2)
            size = f.tell()
            f.seek(max(0, size - nbytes))
            return f.read().decode("utf-8", "replace")
    except OSError:
        return ""


def lemma_record_from_tail(tail: str, stem: str, path: str = "") -> dict | None:
    typ = last_theorem_type(tail)
    if not typ:
        return None
    ineq = last_inequality(typ)
    kind = "other"
    if typ.lstrip().startswith("∃") or "∃" in typ[:40]:
        kind = "witness"
    elif ineq and ineq[1] in ("≤", "≥"):
        kind = "lower"
    return {
        "path": path,
        "module": stem,
        "gap": module_to_gap(stem),
        "type": typ,
        "ineq": ineq,
        "kind": kind,
    }


def lemma_record(path: Path) -> dict | None:
    tail = read_tail(path)
    if THM_START not in tail:
        # Huge files may put the theorem earlier than 8KB; retry 32KB.
        tail = read_tail(path, 32768)
    return lemma_record_from_tail(tail, path.stem, str(path))


def lemma_record_at(root: Path, rev: str, rel: str) -> dict | None:
    """Read a lemma from git even if it is not in the current worktree."""
    p = root / rel
    if p.is_file():
        rec = lemma_record(p)
        if rec:
            return rec
    stem = Path(rel).stem
    tail = git_show_tail(root, rev, rel)
    if not tail:
        return None
    return lemma_record_from_tail(tail, stem, rel)


def import_lemma_ids(imports: list) -> list[str]:
    out = []
    for imp in imports or []:
        m = re.search(r"(L_[a-z]+_\d+)$", str(imp).replace(".", "_") if False else str(imp))
        # imports look like PEqualNP.Outside.L_meta_25534
        m = re.search(r"(L_[A-Za-z]+_\d+)\s*$", str(imp))
        if m:
            out.append(module_to_gap(m.group(1)))
    return out


def find_twins(
    root: Path,
    status: dict,
    by_id: dict,
    last_sha: str,
    head: str,
    kinds: set[str] | None = None,
) -> list[dict]:
    """Open desk rows settled by a merged lemma (new or imported)."""
    open_rows = []
    for s in status.get("gaps") or []:
        gid = s.get("id") or ""
        if not gid:
            continue
        if kinds is not None and lane(gid) not in kinds:
            continue
        if int(s.get("held") or 0):
            continue
        g = by_id.get(gid) or {}
        if int(g.get("pr_open") or 0) > 0:
            continue
        title = s.get("title") or g.get("title") or ""
        if SKIP_TITLE.search(title):
            continue
        stmt = g.get("statement") or ""
        if not stmt:
            continue
        open_rows.append(
            {
                "id": gid,
                "title": title.replace("\n", " "),
                "stmt": stmt,
                "imports": g.get("imports") or [],
                "ineq": last_inequality(stmt),
            }
        )

    # Index reverse inequalities: B < A  looks up  A ≤ B.
    rev_index: dict[tuple[str, str], list[dict]] = {}
    for row in open_rows:
        ineq = row["ineq"]
        if not ineq:
            continue
        key = (norm_expr(ineq[2]), norm_expr(ineq[0]))
        rev_index.setdefault(key, []).append(row)

    new_names = new_merged_names(root, last_sha, head)
    new_mods = {Path(n).stem for n in new_names}
    lemmas: dict[str, dict] = {}
    for rel in new_names:
        rec = lemma_record_at(root, head, rel)
        if rec:
            lemmas[rec["gap"]] = rec

    # Every Outside lemma an open row already imports.
    for row in open_rows:
        for lid in import_lemma_ids(row["imports"]):
            if lid in lemmas:
                continue
            p = lean_path(root, lid)
            if p.is_file():
                rec = lemma_record(p)
                if rec:
                    lemmas[lid] = rec

    hits: list[dict] = []
    seen: set[tuple[str, str]] = set()

    def add(gap_id: str, lemma_id: str, kind: str, why: str, title: str, new: bool) -> None:
        key = (gap_id, lemma_id)
        if key in seen:
            return
        seen.add(key)
        hits.append(
            {
                "id": gap_id,
                "lemma": lemma_id,
                "kind": kind,
                "why": why + (":new" if new else ""),
                "diff": 2 if new else 3,
                "title": title,
                "lane": lane(gap_id),
                "held": 0,
                "pr": 0,
                "n": num(gap_id),
            }
        )

    for lid, rec in lemmas.items():
        is_new = rec["module"] in new_mods
        ineq = rec.get("ineq")
        if ineq:
            key = (norm_expr(ineq[0]), norm_expr(ineq[2]))
            for row in rev_index.get(key, []):
                if row["ineq"] and reverse_ops(ineq[1], row["ineq"][1]):
                    knd = "refute" if rec["kind"] != "witness" else "witness"
                    # Existence of the reverse of a ≤-lemma is a refute.
                    if rec["kind"] == "lower" and row["ineq"][1] in ("<", ">"):
                        knd = "refute"
                    elif rec["kind"] == "witness":
                        knd = "witness"
                    add(row["id"], lid, knd, "rev-ineq", row["title"], is_new)
        for row in open_rows:
            imps = import_lemma_ids(row["imports"])
            # A library dump of 80 imported lemmas is not a twin. Direct
            # twins name one or two Outside lemmas.
            if len(imps) > 2 or lid not in imps:
                continue
            knd = "refute" if rec["kind"] == "lower" else "witness"
            add(row["id"], lid, knd, "imports", row["title"], is_new)

    # Full reverse-ineq pass over Outside for still-open Find/beating rows
    # whose lemma may have merged before this loop's window.
    find_rows = [r for r in open_rows if r["ineq"]]
    if find_rows:
        need = {(norm_expr(r["ineq"][2]), norm_expr(r["ineq"][0])): r for r in find_rows if r["ineq"]}
        outside = root / "lean" / "PEqualNP" / "Outside"
        if outside.is_dir() and need:
            for p in outside.glob("L_*.lean"):
                tail = read_tail(p, 4096)
                if "≤" not in tail and "≥" not in tail:
                    continue
                rec = lemma_record(p)
                if not rec or not rec.get("ineq"):
                    continue
                ineq = rec["ineq"]
                key = (norm_expr(ineq[0]), norm_expr(ineq[2]))
                row = need.get(key)
                if row and reverse_ops(ineq[1], row["ineq"][1]):
                    add(row["id"], rec["gap"], "refute", "rev-ineq-scan", row["title"], False)

    hits.sort(key=lambda h: (h["diff"], -h["n"]))
    return hits


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--limit", type=int, default=16)
    ap.add_argument("--kind", default="lib,pcx", help="comma list: lib,pcx,meta,all")
    ap.add_argument("--max-diff", type=int, default=5)
    ap.add_argument("--gh", action="store_true", help="confirm top list against open PRs")
    ap.add_argument("--include-held", action="store_true")
    ap.add_argument("--status", default="")
    ap.add_argument("--gaps", default="")
    ap.add_argument("--no-twins", action="store_true")
    ap.add_argument("--twins-only", action="store_true")
    ap.add_argument("--twin-json", action="store_true")
    ap.add_argument("--no-fetch", action="store_true")
    args = ap.parse_args()

    kinds = {k.strip() for k in args.kind.split(",") if k.strip()}
    if "all" in kinds:
        kinds = {"lib", "pcx", "meta", "clb", "other"}

    root = Path(
        subprocess.check_output(
            ["git", "rev-parse", "--show-toplevel"], text=True
        ).strip()
    )

    status = json.load(open(args.status)) if args.status else fetch_json(STATUS_URL)
    gaps_blob = json.load(open(args.gaps)) if args.gaps else fetch_json(GAPS_URL)
    by_id = {g["id"]: g for g in (gaps_blob.get("gaps") or []) if g.get("id")}

    twins: list[dict] = []
    head = ""
    last_sha = ""
    if not args.no_twins or args.twins_only or args.twin_json:
        last_sha = read_last_sha(root)
        head = ensure_upstream(root, fetch=not args.no_fetch)
        twins = find_twins(root, status, by_id, last_sha, head, kinds=None)
        if head:
            write_last_sha(root, head)

    if args.twin_json:
        json.dump(twins, sys.stdout, indent=2)
        sys.stdout.write("\n")
        return 0

    if twins:
        print(
            f"# twins {len(twins)} (upstream={head[:12] if head else '?'} "
            f"since={last_sha[:12] if last_sha else 'first'})",
            file=sys.stderr,
        )
        print("# twin\tgap\tlemma\tkind\tdiff\twhy\ttitle")
        for t in twins:
            print(
                f"twin\t{t['id']}\t{t['lemma']}\t{t['kind']}\t{t['diff']}\t"
                f"{t['why']}\t{(t['title'] or '')[:90]}"
            )
        if args.twins_only:
            return 0

    if args.twins_only:
        return 0

    rows = []
    for s in status.get("gaps") or []:
        gid = s.get("id") or ""
        if not gid:
            continue
        ln = lane(gid)
        if ln not in kinds:
            continue
        held = int(s.get("held") or 0)
        if held and not args.include_held:
            continue
        g = by_id.get(gid) or {}
        if int(g.get("pr_open") or 0) > 0:
            continue
        title = s.get("title") or g.get("title") or ""
        stmt = g.get("statement") or ""
        if SKIP_TITLE.search(title) or SKIP_STMT.search(stmt):
            continue
        d, why = difficulty(
            {
                "id": gid,
                "title": title,
                "statement": stmt,
            },
            root,
        )
        rows.append(
            {
                "id": gid,
                "lane": ln,
                "diff": d,
                "why": why,
                "held": held,
                "pr": int(g.get("pr_open") or 0),
                "n": num(gid),
                "title": title.replace("\n", " "),
                "stmt": stmt,
                "file": g.get("file") or "",
                "imports": g.get("imports") or [],
            }
        )

    def key(r):
        lane_rank = 0 if r["lane"] in ("lib", "pcx") else 1
        return (lane_rank, r["diff"], -r["n"])

    rows.sort(key=key)
    easy = [r for r in rows if r["diff"] <= args.max_diff]
    pool = easy or rows
    short = pool[: max(args.limit * 3, args.limit)]

    blocked = set()
    if args.gh:
        ids = [r["id"] for r in short] + [t["id"] for t in twins[:20]]
        blocked = gh_open_titles(ids)

    out = [r for r in short if r["id"] not in blocked][: args.limit]

    print(
        f"# rank {len(out)}/{len(rows)} shown "
        f"(desk open={status.get('open_gaps')} held={status.get('held_now')} "
        f"kinds={','.join(sorted(kinds))} max_diff={args.max_diff} "
        f"gh_blocked={len(blocked)})",
        file=sys.stderr,
    )
    print("# id\tlane\tdiff\theld\tpr\twhy\ttitle")
    for r in out:
        print(
            f"{r['id']}\t{r['lane']}\t{r['diff']}\t{r['held']}\t{r['pr']}\t{r['why']}\t{r['title'][:110]}"
        )
    return 0


if __name__ == "__main__":
    sys.exit(main())
