#!/usr/bin/env python3
"""Shared desk, kind, import-whitelist, PR, and lease helpers for hunt tools.

Imported by rank_gaps.py, gen_twin.py, precheck.sh, and the watcher scripts.
Does not claim, beat, or release desk units.
"""
from __future__ import annotations

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
USER_AGENT = os.environ.get("PNP_UA", "pnplib/1")

AUTHOR_NAME = "TheComfyOne"
AUTHOR_EMAIL = "210307828+TheComfyOne@users.noreply.github.com"
GIT_ENV = {
    "GIT_AUTHOR_NAME": AUTHOR_NAME,
    "GIT_AUTHOR_EMAIL": AUTHOR_EMAIL,
    "GIT_COMMITTER_NAME": AUTHOR_NAME,
    "GIT_COMMITTER_EMAIL": AUTHOR_EMAIL,
}

THM_START = "theorem PEqualNP.Outside."
IMPORT_RX = re.compile(
    r"^import ([A-Za-z][A-Za-z0-9_]*(?:\.[A-Za-z][A-Za-z0-9_]*)*)[ \t]*$"
)
FORBIDDEN_RX = re.compile(r"\b(inductive|sorry|axiom|native_decide)\b")
GAP_ID_RX = re.compile(r"[LR]-[A-Za-z]+-\d+(?:-\d+)?")


def repo_root(start: Path | None = None) -> Path:
    cwd = start or Path.cwd()
    p = subprocess.run(
        ["git", "rev-parse", "--show-toplevel"],
        cwd=cwd,
        capture_output=True,
        text=True,
    )
    if p.returncode == 0 and p.stdout.strip():
        return Path(p.stdout.strip())
    return cwd


def tools_dir() -> Path:
    return Path(__file__).resolve().parent


def pnp_dir(root: Path) -> Path:
    return root / ".pnp"


def fetch_json(url: str, timeout: int = 60, ua: str | None = None):
    req = urllib.request.Request(
        url, headers={"User-Agent": ua or USER_AGENT}
    )
    with urllib.request.urlopen(req, timeout=timeout) as r:
        return json.load(r)


def fetch_desk_row(gid: str, ua: str | None = None) -> dict | None:
    """One gap as intake reads it (GET /desk/row?gap=ID). None on fetch error."""
    try:
        blob = fetch_json(ROW_URL + gid, timeout=30, ua=ua)
    except Exception:
        return None
    return row_from_blob(blob, gid)


def row_from_blob(blob: dict | None, gid: str) -> dict | None:
    for g in (blob or {}).get("gaps") or []:
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


def gap_to_module(gid: str) -> str:
    return gid.replace("L-", "L_").replace("-", "_")


def module_to_gap(mod: str) -> str:
    body = mod[2:] if mod.startswith("L_") else mod
    return "L-" + body.replace("_", "-")


def file_to_gap(rel: str) -> str | None:
    """lean/PEqualNP/Outside/L_meta_25584.lean -> L-meta-25584."""
    stem = Path(rel).stem
    if not stem.startswith("L_"):
        return None
    return "L-" + stem[2:].replace("_", "-")


def lean_path(root: Path, gid: str) -> Path:
    return root / "lean" / "PEqualNP" / "Outside" / f"{gap_to_module(gid)}.lean"


def lemma_module_name(gid: str) -> str:
    return f"PEqualNP.Outside.{gap_to_module(gid)}"


def listed_imports(row: dict | None) -> list[str]:
    return [str(x) for x in ((row or {}).get("imports") or [])]


def row_allows_lemma(row: dict, lemma_id: str) -> bool:
    """True when the desk lists the lemma's module (CI import whitelist)."""
    return lemma_module_name(lemma_id) in set(listed_imports(row))


def parse_import_names(text: str) -> list[str]:
    """Leading `import M` lines, same shape as outside-guard.mjs."""
    names: list[str] = []
    for line in (text or "").splitlines():
        if not line.strip():
            continue
        m = IMPORT_RX.match(line)
        if not m:
            break
        names.append(m.group(1))
    return names


def import_is_allowed(name: str, listed: list | set) -> bool:
    if name == "Mathlib" or name.startswith("Mathlib."):
        return True
    return name in set(listed or [])


def import_header(listed: list[str] | None) -> str:
    """Mathlib, then the desk row's listed modules in order. Nothing else."""
    lines = ["import Mathlib"]
    seen = {"Mathlib"}
    for m in listed or []:
        if not m or m in seen:
            continue
        lines.append(f"import {m}")
        seen.add(m)
    return "\n".join(lines) + "\n\n"


def import_lemma_ids(imports: list) -> list[str]:
    out = []
    for imp in imports or []:
        m = re.search(r"(L_[A-Za-z]+_\d+)\s*$", str(imp))
        if m:
            out.append(module_to_gap(m.group(1)))
    return out


def last_theorem_type(text: str) -> str | None:
    """Type of the last `theorem PEqualNP.Outside.` in a Lean file."""
    idx = text.rfind(THM_START)
    if idx < 0:
        return None
    rest = text[idx:]
    m = re.search(r"\s:=\s*by\b", rest)
    if not m:
        m = re.search(r"\s:=", rest)
    if not m:
        return None
    head = rest[: m.start()]
    colon = head.find(":")
    if colon < 0:
        return None
    return head[colon + 1 :].strip()


last_theorem_type_of_text = last_theorem_type


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
    return pn in tn or tn.startswith("¬(" + pn) or tn.startswith("(¬(" + pn)


def forbidden_hits(text: str) -> list[tuple[int, str, str]]:
    hits = []
    for i, line in enumerate((text or "").splitlines(), 1):
        m = FORBIDDEN_RX.search(line)
        if m:
            hits.append((i, m.group(1), line.strip()[:120]))
    return hits


def gh_open_titles(ids: list[str], repo: str | None = None) -> set[str]:
    """Return gap ids that already have an open PR whose title contains the id."""
    hit = set()
    repo = repo or REPO
    for gid in ids:
        try:
            p = subprocess.run(
                [
                    "gh",
                    "pr",
                    "list",
                    "-R",
                    repo,
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


def title_claims_gap(gid: str, titles_lower: list[str]) -> bool:
    """True when hyphen or underscore form of gid appears in a PR title."""
    g = (gid or "").lower()
    if not g:
        return False
    alt = g.replace("-", "_")
    for t in titles_lower:
        if g in t or alt in t:
            return True
    return False


def load_json_file(path: Path | str) -> dict | None:
    p = Path(path)
    if not p.is_file():
        return None
    try:
        return json.loads(p.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError):
        return None


def load_pnp_step(root: Path, gid: str) -> dict | None:
    """Lease/skeleton JSON written by pnp.sh next at .pnp/<gid>.json."""
    return load_json_file(pnp_dir(root) / f"{gid}.json")


def step_gap(blob: dict | None) -> dict:
    if not blob:
        return {}
    g = blob.get("gap")
    return g if isinstance(g, dict) else blob


def lease_record(blob: dict | None) -> dict:
    if not blob:
        return {}
    lease = blob.get("lease")
    return lease if isinstance(lease, dict) else {}


def lease_terms(blob: dict | None) -> dict:
    rec = lease_record(blob)
    terms = rec.get("terms")
    return terms if isinstance(terms, dict) else {}


def reductions_open(blob: dict | None) -> bool:
    return bool(lease_terms(blob).get("reductions_open"))


def lease_kind(blob: dict | None) -> str:
    return str(lease_terms(blob).get("kind") or "")


def scan_forbidden(path: Path, label: str | None = None) -> int:
    """Print precheck forbidden-token messages. Return 0/1."""
    text = path.read_text(encoding="utf-8")
    shown = label or str(path)
    hits = forbidden_hits(text)
    if hits:
        print(f"precheck: forbidden token in {shown}", file=sys.stderr)
        for i, tok, snippet in hits[:20]:
            print(f"  {shown}:{i}: {tok}  {snippet}", file=sys.stderr)
        return 1
    print(
        f"precheck: no inductive/sorry/axiom/native_decide in {shown}",
        file=sys.stderr,
    )
    return 0


def precheck_desk(root: Path, rel: str, text: str | None = None) -> int:
    """Desk kind + import whitelist. Same messages as the old precheck.sh block."""
    rel = rel.replace("\\", "/")
    stem = Path(rel).stem
    if not stem.startswith("L_"):
        return 0
    gid = "L-" + stem[2:].replace("_", "-")
    path = Path(root) / rel
    if not path.is_file():
        path = Path(rel)
    if text is None:
        text = path.read_text(encoding="utf-8")
    thm = last_theorem_type(text) or ""
    thm_neg = posted_is_negation(thm)

    try:
        blob = fetch_json(ROW_URL + gid, timeout=30, ua="precheck/1")
    except Exception as e:
        has_pnp = any(
            ln.startswith("import PEqualNP.") for ln in text.splitlines()
        )
        if thm_neg or has_pnp:
            print(
                f"precheck: cannot fetch desk row for {gid} ({e}); refusing",
                file=sys.stderr,
            )
            return 1
        print(
            f"precheck: desk row fetch failed for {gid}; no PEqualNP import "
            "and theorem is not a negation, continuing",
            file=sys.stderr,
        )
        return 0

    row = row_from_blob(blob, gid)
    if not row:
        if thm_neg:
            print(
                f"precheck: desk has no open row for {gid}; refusing ¬ theorem",
                file=sys.stderr,
            )
            return 1
        print(
            f"precheck: desk has no open row for {gid}; theorem is not a "
            "negation, continuing",
            file=sys.stderr,
        )
        return 0

    # precheck historically treated only kind==refute as refute; else check.
    desk_kind = "refute" if row.get("kind") == "refute" else "check"
    find = is_find_row(row)
    posted = (row.get("statement") or "").strip()
    posted_neg = posted_is_negation(posted)
    listed = listed_imports(row)
    print(
        f"precheck: desk {gid} kind={desk_kind} find={find} imports={listed}",
        file=sys.stderr,
    )

    for i, line in enumerate(text.splitlines(), 1):
        if not line.strip():
            continue
        m = IMPORT_RX.match(line)
        if not m:
            break
        name = m.group(1)
        if import_is_allowed(name, listed):
            continue
        print(
            f"precheck: line {i}: import {name} is not allowed "
            "(only Mathlib and the modules the gap lists)",
            file=sys.stderr,
        )
        return 1
    print("precheck: imports match desk whitelist", file=sys.stderr)

    if desk_kind != "refute":
        if thm_neg and not posted_neg:
            print(
                f"precheck: desk posts {gid} as kind {desk_kind} (find={find}); "
                "the file must prove the posted statement, not its negation",
                file=sys.stderr,
            )
            return 1
        if theorem_wraps_posted(thm, posted):
            print(
                f"precheck: theorem wraps ¬ around the posted statement of "
                f"check/find row {gid}",
                file=sys.stderr,
            )
            return 1
    else:
        if not thm_neg:
            print(
                f"precheck: desk posts {gid} as kind refute; the theorem must "
                "be ¬ of the posted statement",
                file=sys.stderr,
            )
            return 1
    print(f"precheck: desk kind {desk_kind} matches theorem", file=sys.stderr)
    return 0


def precheck_lean(root: Path, rel: str) -> int:
    rel_n = rel.replace("\\", "/")
    path = Path(root) / rel_n
    if not path.is_file():
        path = Path(rel)
    code = scan_forbidden(path, rel)
    if code:
        return code
    return precheck_desk(root, rel_n, path.read_text(encoding="utf-8"))


def main(argv: list[str] | None = None) -> int:
    args = list(sys.argv[1:] if argv is None else argv)
    if not args or args[0] in ("-h", "--help"):
        print(
            "usage: pnplib.py precheck ROOT REL | forbidden FILE",
            file=sys.stderr,
        )
        return 0
    cmd = args[0]
    if cmd == "precheck" and len(args) >= 3:
        return precheck_lean(Path(args[1]), args[2])
    if cmd == "forbidden" and len(args) >= 2:
        return scan_forbidden(Path(args[1]))
    print(f"pnplib: unknown command {cmd}", file=sys.stderr)
    return 2


if __name__ == "__main__":
    sys.exit(main())
