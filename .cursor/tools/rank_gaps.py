#!/usr/bin/env python3
"""One-shot ranking of open desk gaps, with a twin-pair sweep first.

Fetches desk status + gaps.json, diffs upstream/main since the last loop
for newly merged Outside lemmas, and matches open desk rows those lemmas
settle directly. Intake kind comes from the desk row (GET /desk/row?gap=ID,
and the `find`/`kind` fields on gaps.json):

  find:true / missing kind -> checker kind check: prove the posted statement
  kind: refute             -> checker kind refute: prove ¬ posted
  bound >= a merged witness / symmetry / special-case that prove posted
  too-small bound          -> ONLY if the desk posts the step as a refutation
                              (or the posted statement is already ¬ S)

Never emit ¬ of a find/check existence row. Those are skipped as
skip-find-refute (L-meta-25584 / 25609 / 25652 were this mistake).

Pushable twins print first (diff 2–3). Then the usual cheap-row ranking.

Usage:
  .cursor/tools/rank_gaps.py
  .cursor/tools/rank_gaps.py --limit 20 --gh
  .cursor/tools/rank_gaps.py --kind lib,pcx
  .cursor/tools/rank_gaps.py --twins-only
  .cursor/tools/rank_gaps.py --twin-json
"""
from __future__ import annotations

import argparse
import itertools
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
ROW_URL = os.environ.get(
    "ROW_URL", "https://pequalnp-desk.pequalnp.workers.dev/desk/row?gap="
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


def fetch_desk_row(gid: str) -> dict | None:
    """One gap as the intake reads it (GET /desk/row?gap=ID)."""
    try:
        blob = fetch_json(ROW_URL + gid)
    except Exception:
        return None
    for g in blob.get("gaps") or []:
        if g.get("id") == gid:
            return g
    return None


def checker_kind(g: dict | None) -> str:
    """Match outside-guard.mjs + intake: find:true and missing kind are check."""
    if not g:
        return "check"
    k = g.get("kind")
    if k == "refute":
        return "refute"
    if k == "reduce":
        return "reduce"
    if k == "value":
        return "check"
    return "check"


def is_find_row(g: dict | None) -> bool:
    return bool(g and g.get("find") is True)


def posted_is_negation(stmt: str) -> bool:
    s = (stmt or "").lstrip()
    return s.startswith("¬") or s.startswith("(¬")


def file_to_gap(rel: str) -> str | None:
    """lean/PEqualNP/Outside/L_meta_25584.lean -> L-meta-25584."""
    stem = Path(rel).stem
    if not stem.startswith("L_"):
        return None
    return "L-" + stem[2:].replace("_", "-")


def last_theorem_type_of_text(text: str) -> str | None:
    """Type of the last `theorem PEqualNP.Outside.` in a Lean file."""
    return last_theorem_type(text)


def theorem_wraps_posted(thm_type: str, posted: str) -> bool:
    """True when the theorem is ¬ posted (extra wrapper), not posted itself."""
    if not thm_type or not posted:
        return False
    if posted_is_negation(posted):
        return False
    t = thm_type.lstrip()
    if not (t.startswith("¬") or t.startswith("(¬")):
        return False
    tn = re.sub(r"\s+", "", t)
    pn = re.sub(r"\s+", "", posted)
    return pn in tn


HCS_RE = re.compile(
    r"HasCircuitSize\s+(\d+)\s+\(\s*(fun\b[\s\S]*?)\)\s+(\d+)"
)
EDGE_AND_RE = re.compile(r"\(x\s+(\d+)\s*&&\s*x\s+(\d+)\)")
CROWN_RE = re.compile(
    r"fun\s+(\w+)\s+(\w+)\s*:\s*Fin\s+(\d+)\s*=>\s*decide\s*\(\s*\1\s*≠\s*\2\s*\)"
)


def parse_hcs(stmt: str) -> tuple[int, str, int] | None:
    m = HCS_RE.search(stmt or "")
    if not m:
        return None
    return int(m.group(1)), m.group(2).strip(), int(m.group(3))


def graph_edges(expr: str) -> frozenset[tuple[int, int]] | None:
    pairs = [tuple(sorted((int(a), int(b)))) for a, b in EDGE_AND_RE.findall(expr or "")]
    if not pairs:
        return None
    return frozenset(pairs)


def graph_canon(n: int, edges: frozenset[tuple[int, int]]) -> tuple | None:
    if n < 2 or n > 6:
        return None
    best = None
    verts = list(range(n))
    for p in itertools.permutations(verts):
        mapped = tuple(sorted(tuple(sorted((p[a], p[b]))) for a, b in edges))
        if best is None or mapped < best:
            best = mapped
    return best


LAST_TWIN_COUNTS: dict = {}


def twin_action(row: dict, rec: dict, sweep: str = "") -> tuple[str | None, str]:
    """What gen_twin may emit. None = would negate a check/find row; skip."""
    rec_k = rec.get("kind") or "other"
    desk = row.get("desk_kind") or "check"
    if rec_k == "witness":
        return "witness", "witness"
    if desk == "refute":
        return "refute", "refute"
    if row.get("posted_neg") and desk == "check":
        return "check", "posted-neg"
    # Symmetry / special-case / explicit witness sweeps prove posted S.
    if sweep in ("symmetry", "special", "witness") and desk != "refute":
        return "check", sweep
    return None, "skip-find-refute"


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
                "find": is_find_row(g),
                "desk_kind": checker_kind(g),
                "posted_neg": posted_is_negation(stmt),
                "hcs": parse_hcs(stmt),
                "crown_n": (lambda m: int(m.group(3)) if m else None)(CROWN_RE.search(stmt)),
                "g": g,
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
    caught: dict[str, dict[str, set[str]]] = {
        name: {"meta": set(), "pcx": set(), "clb": set()}
        for name in (
            "rev-ineq",
            "rev-ineq-push",
            "skip-find-refute",
            "imports",
            "witness",
            "symmetry",
            "special",
        )
    }

    def catch(kind_name: str, gap_id: str) -> None:
        ln = lane(gap_id)
        if ln in caught[kind_name]:
            caught[kind_name][ln].add(gap_id)

    def add(
        row: dict,
        lemma_id: str,
        rec: dict,
        sweep: str,
        new: bool,
    ) -> None:
        gap_id = row["id"]
        key = (gap_id, lemma_id)
        if key in seen:
            return
        seen.add(key)
        catch(sweep if sweep in caught else "rev-ineq", gap_id)
        action, tag = twin_action(row, rec, sweep)
        if sweep == "rev-ineq" or sweep == "imports":
            if action is None:
                catch("skip-find-refute", gap_id)
            elif sweep == "rev-ineq":
                catch("rev-ineq-push", gap_id)
        if action is None:
            why = f"{sweep}:{tag}"
            knd = "skip"
        else:
            why = f"{sweep}:{tag}"
            knd = action
        hits.append(
            {
                "id": gap_id,
                "lemma": lemma_id,
                "kind": knd,
                "why": why + (":new" if new else ""),
                "diff": 2 if new else 3,
                "title": row["title"],
                "lane": lane(gap_id),
                "held": 0,
                "pr": 0,
                "n": num(gap_id),
                "pushable": action is not None,
                "desk_kind": row.get("desk_kind") or "check",
                "find": bool(row.get("find")),
            }
        )

    for lid, rec in lemmas.items():
        is_new = rec["module"] in new_mods
        ineq = rec.get("ineq")
        if ineq:
            key = (norm_expr(ineq[0]), norm_expr(ineq[2]))
            for row in rev_index.get(key, []):
                if row["ineq"] and reverse_ops(ineq[1], row["ineq"][1]):
                    add(row, lid, rec, "rev-ineq", is_new)
        for row in open_rows:
            imps = import_lemma_ids(row["imports"])
            # A library dump of 80 imported lemmas is not a twin. Direct
            # twins name one or two Outside lemmas.
            if len(imps) > 2 or lid not in imps:
                continue
            add(row, lid, rec, "imports", is_new)

    # Full reverse-ineq pass over Outside for still-open rows whose lemma
    # may have merged before this loop's window.
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
                    add(row, rec["gap"], rec, "rev-ineq", False)

    # Witness / symmetry / special-case: prove the posted statement.
    # Only new/imported lemmas plus a short known list — do not glob 18k files.
    hcs_lemmas: list[tuple[str, dict, tuple[int, str, int]]] = []
    crown_lemmas: list[tuple[str, dict, int, str]] = []
    extra_recs: dict[str, dict] = dict(lemmas)
    for lid in (
        "L-meta-7626",
        "L-meta-18006",
        "L-meta-29939",
        "L-meta-25534",
        "L-meta-25408",
        "L-meta-25529",
        "L-meta-9921",
        "L-pcx-123",
    ):
        if lid in extra_recs:
            continue
        p = lean_path(root, lid)
        if p.is_file():
            rec = lemma_record(p)
            if rec:
                extra_recs[lid] = rec
    for gid, rec in extra_recs.items():
        typ = rec.get("type") or ""
        hcs = parse_hcs(typ)
        if hcs:
            hcs_lemmas.append((gid, rec, hcs))
        cm = CROWN_RE.search(typ)
        if cm and rec.get("kind") == "witness":
            crown_lemmas.append((gid, rec, int(cm.group(3)), typ))

    hcs_exact: dict[tuple[int, str], list[tuple[str, dict, int]]] = {}
    hcs_graph: dict[tuple[int, tuple], list[tuple[str, dict, int]]] = {}
    for lid, rec, (n, expr, k) in hcs_lemmas:
        if rec.get("kind") != "witness":
            continue
        hcs_exact.setdefault((n, norm_expr(expr)), []).append((lid, rec, k))
        edges = graph_edges(expr)
        if edges:
            canon = graph_canon(n, edges)
            if canon is not None:
                hcs_graph.setdefault((n, canon), []).append((lid, rec, k))

    for row in open_rows:
        hcs = row.get("hcs")
        if hcs:
            n, expr, k_post = hcs
            for lid, rec, k_lem in hcs_exact.get((n, norm_expr(expr)), []):
                if k_post >= k_lem:
                    add(row, lid, rec, "witness", rec["module"] in new_mods)
            edges = graph_edges(expr)
            if edges:
                canon = graph_canon(n, edges)
                if canon is not None:
                    for lid, rec, k_lem in hcs_graph.get((n, canon), []):
                        if k_post >= k_lem and norm_expr(expr) != norm_expr(
                            parse_hcs(rec.get("type") or "")[1]
                            if parse_hcs(rec.get("type") or "")
                            else ""
                        ):
                            add(row, lid, rec, "symmetry", rec["module"] in new_mods)
        # Special-case: posted is a Fin-n crown instance of a general witness,
        # or a forall lower bound instantiating a merged ∀ lemma (prove posted).
        cn = row.get("crown_n")
        if cn is not None:
            for lid, rec, n_lem, typ in crown_lemmas:
                if n_lem == cn and rec.get("kind") == "witness":
                    add(row, lid, rec, "special", rec["module"] in new_mods)
            stmt = row["stmt"]
            if stmt.lstrip().startswith("∀") and not row.get("find"):
                for lid in (
                    "L-meta-7626",
                    "L-meta-18006",
                    "L-meta-29939",
                    "L-meta-25534",
                    "L-meta-25408",
                    "L-meta-25529",
                ):
                    rec = extra_recs.get(lid)
                    if rec and rec.get("kind") == "lower":
                        add(row, lid, rec, "special", rec["module"] in new_mods)

    global LAST_TWIN_COUNTS
    LAST_TWIN_COUNTS = {
        name: {ln: len(ids) for ln, ids in lanes.items()}
        for name, lanes in caught.items()
    }
    LAST_TWIN_COUNTS["_open"] = {
        ln: sum(1 for r in open_rows if lane(r["id"]) == ln)
        for ln in ("meta", "pcx", "clb")
    }

    hits.sort(key=lambda h: (0 if h.get("pushable") else 1, h["diff"], -h["n"]))
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

    if twins or LAST_TWIN_COUNTS:
        open_n = LAST_TWIN_COUNTS.get("_open") or {}
        print(
            f"# twins {len(twins)} (upstream={head[:12] if head else '?'} "
            f"since={last_sha[:12] if last_sha else 'first'}) "
            f"open meta={open_n.get('meta', 0)} pcx={open_n.get('pcx', 0)} "
            f"clb={open_n.get('clb', 0)}",
            file=sys.stderr,
        )
        print("# sweep\tmeta\tpcx\tclb\ttotal")
        for name in (
            "rev-ineq",
            "rev-ineq-push",
            "skip-find-refute",
            "imports",
            "witness",
            "symmetry",
            "special",
        ):
            d = LAST_TWIN_COUNTS.get(name) or {}
            m, p, c = d.get("meta", 0), d.get("pcx", 0), d.get("clb", 0)
            print(f"{name}\t{m}\t{p}\t{c}\t{m + p + c}")
        print("# twin\tgap\tlemma\tkind\tdiff\tpush\twhy\ttitle")
        for t in twins:
            flag = "yes" if t.get("pushable") else "SKIP"
            print(
                f"twin\t{t['id']}\t{t['lemma']}\t{t['kind']}\t{t['diff']}\t"
                f"{flag}\t{t['why']}\t{(t['title'] or '')[:90]}"
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
