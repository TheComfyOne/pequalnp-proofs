#!/usr/bin/env python3
"""Emit, build, and optionally push a twin-pair proof from a fixed template.

Takes an open gap id plus the merged lemma that settles it. Kind is the
desk row (GET /desk/row?gap=ID), not a flag we pick:

  desk kind refute -> ¬ posted, apply the lower-bound lemma
  otherwise        -> posted, apply a witness / symmetry / special-case

Never wrap ¬ around a find/check existence row. Intake judges those as
check (find: true => check). L-meta-25584 was REJECTED (statement) for
that.

Imports: only Mathlib (and Mathlib.*) plus the desk row's `imports`
whitelist. A twin may reuse a merged lemma only if that lemma's module is
listed. L-meta-25652 PR 48521 was REFUSED for importing
PEqualNP.Outside.L_meta_25645 when the row listed only PEqualNP.Defs.

Hand-edit only if the one lake build fails.

Usage:
  .cursor/tools/gen_twin.py L-meta-25652 L-meta-25645
  .cursor/tools/gen_twin.py L-meta-25652 L-meta-25645 --push
  .cursor/tools/gen_twin.py L-meta-25693 L-meta-25534 --kind refute --dry-run
  .cursor/tools/gen_twin.py --from-rank --push
"""
from __future__ import annotations

import argparse
import json
import os
import re
import subprocess
import sys
import tempfile
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import pnplib  # noqa: E402
import rank_gaps as rg  # noqa: E402

AUTHOR_NAME = pnplib.AUTHOR_NAME
AUTHOR_EMAIL = pnplib.AUTHOR_EMAIL
GIT_ENV = pnplib.GIT_ENV


def die(msg: str, code: int = 1) -> None:
    print(f"gen_twin: {msg}", file=sys.stderr)
    sys.exit(code)


def run(
    args: list[str],
    cwd: Path | None = None,
    env: dict | None = None,
    timeout: int = 300,
    check: bool = True,
) -> subprocess.CompletedProcess:
    e = os.environ.copy()
    if env:
        e.update(env)
    p = subprocess.run(
        args,
        cwd=cwd,
        env=e,
        text=True,
        capture_output=True,
        timeout=timeout,
    )
    if check and p.returncode != 0:
        sys.stderr.write(p.stdout or "")
        sys.stderr.write(p.stderr or "")
        die(f"command failed ({p.returncode}): {' '.join(args[:6])}", p.returncode)
    return p


def gap_stmt(by_id: dict, gid: str) -> str:
    g = by_id.get(gid)
    if not g:
        die(f"gap {gid} not in gaps.json")
    stmt = (g.get("statement") or "").strip()
    if not stmt:
        die(f"gap {gid} has empty statement")
    if '"' in stmt:
        die(f"gap {gid} statement contains a string literal; template will not emit quotes")
    return stmt


def split_top(s: str, sep: str) -> list[str]:
    """Split on sep at paren depth 0. sep may be a literal or a whitespace-flex ∧/→."""
    flex = {
        " ∧ ": re.compile(r"\s*∧\s*"),
        "∧": re.compile(r"\s*∧\s*"),
        " → ": re.compile(r"\s*→\s*"),
        "→": re.compile(r"\s*→\s*"),
    }
    rx = flex.get(sep)
    parts: list[str] = []
    buf: list[str] = []
    depth = 0
    i = 0
    while i < len(s):
        ch = s[i]
        if ch in "([{":
            depth += 1
        elif ch in ")]}":
            depth = max(0, depth - 1)
        if depth == 0:
            if rx is not None:
                m = rx.match(s, i)
                if m:
                    parts.append("".join(buf).strip())
                    buf = []
                    i = m.end()
                    continue
            elif s.startswith(sep, i):
                parts.append("".join(buf).strip())
                buf = []
                i += len(sep)
                continue
        buf.append(ch)
        i += 1
    parts.append("".join(buf).strip())
    return [p for p in parts if p]


def binder_names(group: str) -> list[str]:
    inner = group.strip()
    if inner.startswith("(") and inner.endswith(")"):
        inner = inner[1:-1]
    if ":" not in inner:
        return inner.split()
    left = inner.split(":", 1)[0]
    return left.split()


def parse_binders(prefix: str) -> tuple[list[str], str]:
    """Parse ∃ / ∀ binder groups. Return (names, rest after comma)."""
    s = prefix.strip()
    names: list[str] = []
    i = 0
    while i < len(s):
        while i < len(s) and s[i].isspace():
            i += 1
        if i >= len(s):
            break
        if s[i] == ",":
            return names, s[i + 1 :].strip()
        if s[i] != "(":
            # Bare name then rest.
            m = re.match(r"([A-Za-z_][\w']*)", s[i:])
            if m:
                names.append(m.group(1))
                i += m.end()
                continue
            break
        depth = 0
        j = i
        while j < len(s):
            if s[j] == "(":
                depth += 1
            elif s[j] == ")":
                depth -= 1
                if depth == 0:
                    j += 1
                    break
            j += 1
        names.extend(binder_names(s[i:j]))
        i = j
    return names, s[i:].lstrip(",").strip()


def strip_lets(body: str) -> str:
    s = body.strip()
    while s.startswith("let "):
        # let name := expr  then newline or ` in `
        rest = s[4:]
        eq = rest.find(":=")
        if eq < 0:
            break
        expr = rest[eq + 2 :].lstrip()
        # Find end of expr: ` in ` at depth 0, or a newline followed by a
        # conjunct / implication / forall, not a continuation indent of the expr.
        depth = 0
        k = 0
        end = None
        while k < len(expr):
            ch = expr[k]
            if ch in "([{":
                depth += 1
            elif ch in ")]}":
                depth = max(0, depth - 1)
            if depth == 0 and expr.startswith(" in ", k):
                end = k
                s = expr[k + 4 :].strip()
                break
            if depth == 0 and expr[k] == "\n":
                nxt = expr[k + 1 :]
                stripped = nxt.lstrip()
                if stripped.startswith(("let ", "∀", "∃", "(", "2", "¬")) or (
                    stripped and not nxt[:1].isspace() and stripped[:1].isalpha()
                ):
                    # Heuristic: a let-bound expr that continues is indented.
                    # A following conjunct at col-0-ish after spaces is the body.
                    # We treat newline + spaces + non-operator as body start
                    # when the next line is not clearly part of the expr.
                    if stripped.startswith(("let ",)) or re.match(
                        r"(\d+\s*≤|∀|∃|PEqualNP|\()", stripped
                    ):
                        end = k
                        s = stripped
                        break
            k += 1
        else:
            if end is None:
                return s
        if end is None:
            return s
    return s


def fin_dims(stmt: str) -> list[int]:
    return [int(x) for x in re.findall(r"Fin\s+(\d+)", stmt)]


def size_le(stmt: str) -> int | None:
    m = re.findall(r"C\.size\s*≤\s*(\d+)", stmt)
    if m:
        return int(m[-1])
    m = re.findall(r"RepSizeAtMost\s+[^ \n]+\s+(\d+)", stmt)
    if m:
        return int(m[-1])
    m = re.findall(r"π\.length\s*≤\s*(\d+)", stmt)
    if m:
        return int(m[-1])
    return None


def eval_nat(expr: str, env: dict[str, int]) -> int | None:
    s = expr
    for k, v in env.items():
        s = re.sub(rf"\b{k}\b", str(v), s)
    s = s.replace("ℕ", "").replace("Nat", "")
    s = re.sub(r"\s+", "", s)
    if not re.fullmatch(r"[0-9+\-*/()]+", s):
        return None
    try:
        val = eval(s, {"__builtins__": {}}, {})  # noqa: S307 — digits and +-* only
    except Exception:
        return None
    if isinstance(val, int) and val >= 0:
        return val
    return None


def parse_exists(stmt: str) -> tuple[list[str], list[str], str]:
    s = stmt.strip()
    if s.startswith("¬"):
        s = s[1:].strip()
        if s.startswith("(") and s.endswith(")"):
            s = s[1:-1].strip()
    if not s.startswith("∃"):
        return [], [], s
    s = s[1:].strip()
    names, rest = parse_binders(s)
    rest = strip_lets(rest)
    parts = split_top(rest, " ∧ ")
    if len(parts) == 1:
        parts = split_top(rest, "∧")
    hyps, last = parts[:-1], parts[-1]
    return names, hyps, last


def parse_forall(typ: str) -> tuple[list[str], list[str], str]:
    s = typ.strip()
    if s.startswith("(") and s.endswith(")"):
        s = s[1:-1].strip()
    names: list[str] = []
    if s.startswith("∀"):
        s = s[1:].strip()
        names, s = parse_binders(s)
        s = strip_lets(s)
    parts = split_top(s, " → ")
    if len(parts) == 1:
        parts = split_top(s, "→")
    if len(parts) == 1:
        return names, [], s
    return names, parts[:-1], parts[-1]


def is_numeric_hyp(hyp: str, forall_names: list[str]) -> bool:
    h = re.sub(r"\s+", " ", hyp.strip())
    return bool(re.fullmatch(r"\d+\s*≤\s*[A-Za-z_]\w*", h))


def is_size_hyp(hyp: str) -> bool:
    return bool(re.search(r"C\.size\s*≤\s*\d+", hyp) or re.search(r"π\.length\s*≤\s*\d+", hyp))


def rintro_names(binders: list[str], n_hyps: int) -> str:
    hyps = [f"h{i}" for i in range(n_hyps)]
    if hyps:
        hyps[-1] = "hlt" if n_hyps else "hlt"
        # last is the inequality / leftover
    inner = ", ".join(binders + hyps)
    return f"⟨{inner}⟩"


def import_header(listed: list[str]) -> str:
    return pnplib.import_header(listed)


def require_listed_lemma(gid: str, lemma_id: str, listed: list[str]) -> str:
    mod = pnplib.lemma_module_name(lemma_id)
    if mod not in set(listed or []):
        die(
            f"desk row {gid} does not list {mod}; "
            "CI only allows Mathlib and the modules the gap lists"
        )
    return mod


def emit_refute_reverse(
    gap_mod: str,
    lemma_mod: str,
    posted: str,
    binders: list[str],
    n_hyps: int,
    wrap: bool = True,
    header: str = "",
) -> str:
    # binders + (n_hyps conjuncts including last ineq)
    names = binders + [f"h{i}" for i in range(n_hyps - 1)] + (["hlt"] if n_hyps else [])
    apply_args = " ".join(binders + [f"h{i}" for i in range(n_hyps - 1)])
    rintro = ", ".join(names)
    thm = f"(¬ ({posted}))" if wrap else f"({posted})"
    return (
        header
        + f"theorem PEqualNP.Outside.{gap_mod} :\n"
        f"    {thm} := by\n"
        f"  rintro ⟨{rintro}⟩\n"
        f"  have hge := PEqualNP.Outside.{lemma_mod} {apply_args}\n"
        "  exact (not_le_of_gt hlt) hge\n"
    )


def emit_refute_instantiate(
    gap_mod: str,
    lemma_mod: str,
    posted: str,
    exists_binders: list[str],
    exists_hyps: list[str],
    forall_names: list[str],
    forall_hyps: list[str],
    lemma_bound: str,
    dims: list[int],
    k: int,
    wrap: bool = True,
    header: str = "",
) -> str:
    # Map extra Nat binders to Fin dimensions in order.
    nat_binders = []
    rest_forall = []
    for n in forall_names:
        # Heuristic: leading Nat names n, m, p, ... until we hit G/C/edge.
        if n in ("n", "m", "p", "q", "k", "d") and len(nat_binders) < len(dims):
            nat_binders.append(n)
        else:
            rest_forall.append(n)
    inst = dims[: len(nat_binders)]
    env = {n: v for n, v in zip(nat_binders, inst)}
    bound_val = eval_nat(lemma_bound, env)
    bound_term = str(bound_val) if bound_val is not None else lemma_bound
    for n, v in env.items():
        bound_term = re.sub(rf"\b{n}\b", str(v), bound_term)

    # Exists hyps: skip size hyp when applying the lemma.
    hyp_names = []
    size_name = None
    apply_hyps = []
    fi = 0
    for hyp in exists_hyps:
        name = f"h{fi}"
        fi += 1
        if is_size_hyp(hyp):
            size_name = name
            hyp_names.append(name)
            continue
        hyp_names.append(name)
        apply_hyps.append(name)

    rintro = ", ".join(exists_binders + hyp_names)
    inst_s = " ".join(str(v) for v in inst)
    # Numeric lemma hyps become (by decide); others zip with apply_hyps.
    lemma_args: list[str] = []
    lemma_args.extend(str(v) for v in inst)
    # Remaining forall names should match exists binders (G, code, C, ...)
    used_exists = list(exists_binders)
    lemma_args.extend(used_exists)
    hi = 0
    for hyp in forall_hyps:
        if is_numeric_hyp(hyp, forall_names):
            lemma_args.append("(by decide)")
        elif is_size_hyp(hyp):
            continue
        else:
            if hi < len(apply_hyps):
                lemma_args.append(apply_hyps[hi])
                hi += 1
            else:
                lemma_args.append("(by decide)")
    apply_s = " ".join(lemma_args)
    if size_name is None:
        size_name = "hlt"
    thm = f"(¬ ({posted}))" if wrap else f"({posted})"
    return (
        header
        + f"theorem PEqualNP.Outside.{gap_mod} :\n"
        f"    {thm} := by\n"
        f"  rintro ⟨{rintro}⟩\n"
        f"  have hLower : {bound_term} ≤ C.size :=\n"
        f"    PEqualNP.Outside.{lemma_mod} {apply_s}\n"
        f"  exact (by decide : ¬ ({bound_term} ≤ {k})) (hLower.trans {size_name})\n"
    )


def emit_witness_apply(
    gap_mod: str, lemma_mod: str, posted: str, header: str = ""
) -> str:
    return (
        header
        + f"theorem PEqualNP.Outside.{gap_mod} :\n"
        f"    ({posted}) :=\n"
        f"  PEqualNP.Outside.{lemma_mod}\n"
    )


def emit_witness_weaken(
    gap_mod: str,
    lemma_mod: str,
    posted: str,
    binders: list[str],
    n_hyps: int,
    k_lemma: int,
    k_post: int,
    header: str = "",
) -> str:
    names = binders + [f"h{i}" for i in range(n_hyps)]
    rintro = ", ".join(names)
    # Identify size hyp index.
    size_idx = n_hyps - 1
    fields = []
    for i, n in enumerate(names):
        if n in binders:
            fields.append(n)
        elif i == len(binders) + size_idx:
            fields.append(f"Nat.le_trans {n} (by decide : {k_lemma} ≤ {k_post})")
        else:
            fields.append(n)
    # obtain from lemma then refine with weakened size
    return (
        header
        + f"theorem PEqualNP.Outside.{gap_mod} :\n"
        f"    ({posted}) := by\n"
        f"  obtain ⟨{rintro}⟩ := PEqualNP.Outside.{lemma_mod}\n"
        f"  exact ⟨{', '.join(fields)}⟩\n"
    )


def choose_template(
    kind: str, posted: str, lemma_typ: str, desk_kind: str = "check"
) -> tuple[str, str]:
    """Return (kind, reason) after looking at the two types and the desk row."""
    if kind != "auto":
        if kind == "refute" and desk_kind != "refute":
            die(
                "refute template refused: desk does not post this step as a "
                f"refutation (desk kind {desk_kind})"
            )
        return kind, "cli"
    p_ineq = rg.last_inequality(posted)
    l_ineq = rg.last_inequality(lemma_typ)
    if p_ineq and l_ineq and rg.ineq_reverse(l_ineq, p_ineq):
        if desk_kind == "refute":
            return "refute", "rev-ineq"
        if pnplib.posted_is_negation(posted):
            return "check", "rev-ineq-posted-neg"
        die(
            "rev-ineq on a check/find row; will not emit ¬ of the posted "
            "statement (desk kind "
            + desk_kind
            + ")"
        )
    k_post = size_le(posted)
    k_lem = size_le(lemma_typ)
    if k_post is not None and k_lem is not None and k_post >= k_lem and "∃" in lemma_typ:
        return "witness", "weaken-size"
    if posted.strip() == lemma_typ.strip() or lemma_typ.strip() in posted:
        return "witness", "same-stmt"
    if k_post is not None and l_ineq and l_ineq[1] == "≤" and "C.size" in l_ineq[2]:
        if desk_kind == "refute":
            return "refute", "instantiate-size"
        if pnplib.posted_is_negation(posted):
            return "check", "instantiate-posted-neg"
        die(
            "instantiate-size on a check/find row; will not emit ¬ of the "
            f"posted statement (desk kind {desk_kind})"
        )
    if desk_kind == "refute":
        return "refute", "default-refute"
    return "witness", "default-witness"


def emit_file(
    kind: str,
    gid: str,
    lemma_id: str,
    posted: str,
    lemma_typ: str,
    wrap: bool = True,
    listed: list[str] | None = None,
) -> str:
    gap_mod = pnplib.gap_to_module(gid)
    lemma_mod = pnplib.gap_to_module(lemma_id)
    header = import_header(listed or [])
    binders, hyps, last = parse_exists(posted)
    f_names, f_hyps, f_last = parse_forall(lemma_typ)
    k_post = size_le(posted)
    k_lem = size_le(lemma_typ)

    if kind in ("witness", "check"):
        # Prove posted as-is. wrap=False when posted is already ¬ S.
        if kind == "check" and pnplib.posted_is_negation(posted):
            inner = posted.lstrip()
            if inner.startswith("¬"):
                inner = inner[1:].strip()
            if inner.startswith("(") and inner.endswith(")"):
                inner = inner[1:-1].strip()
            ibinders, ihyps, _ilast = parse_exists(inner)
            if ibinders:
                return emit_refute_reverse(
                    gap_mod,
                    lemma_mod,
                    posted,
                    ibinders,
                    len(ihyps) + 1,
                    wrap=False,
                    header=header,
                )
        if k_lem is not None and k_post is not None and k_post > k_lem and binders:
            return emit_witness_weaken(
                gap_mod,
                lemma_mod,
                posted,
                binders,
                len(hyps) + 1,
                k_lem,
                k_post,
                header=header,
            )
        return emit_witness_apply(gap_mod, lemma_mod, posted, header=header)

    # refute: only when the desk posts the step as a refutation.
    if not wrap:
        die("internal: refute template with wrap=False")
    p_ineq = rg.last_inequality(posted)
    l_ineq = rg.last_inequality(lemma_typ)
    if (
        binders
        and p_ineq
        and l_ineq
        and rg.ineq_reverse(l_ineq, p_ineq)
        and f_names
        and binders == f_names
    ):
        return emit_refute_reverse(
            gap_mod,
            lemma_mod,
            posted,
            binders,
            len(hyps) + 1,
            wrap=True,
            header=header,
        )

    dims = fin_dims(posted)
    if binders and k_post is not None and dims and f_names:
        bound = f_last
        b_ineq = rg.last_inequality(f_last) or l_ineq
        if b_ineq:
            bound = b_ineq[0] if "C.size" in b_ineq[2] else b_ineq[2]
        return emit_refute_instantiate(
            gap_mod,
            lemma_mod,
            posted,
            binders,
            hyps + [last],
            f_names,
            f_hyps,
            bound,
            dims,
            k_post,
            wrap=True,
            header=header,
        )

    if binders:
        return emit_refute_reverse(
            gap_mod,
            lemma_mod,
            posted,
            binders,
            max(1, len(hyps) + 1),
            wrap=True,
            header=header,
        )

    die("could not parse binders for a template; hand-edit")
    return ""


def ensure_branch(root: Path, gid: str) -> None:
    cur = run(["git", "rev-parse", "--abbrev-ref", "HEAD"], cwd=root).stdout.strip()
    if cur == gid:
        return
    run(["git", "fetch", "upstream", "main"], cwd=root, timeout=120)
    # Fail if a different Lean proof is already staged/committed on this branch.
    p = run(
        ["git", "checkout", "-b", gid, "upstream/main"],
        cwd=root,
        check=False,
    )
    if p.returncode != 0:
        # Branch may exist.
        p2 = run(["git", "checkout", gid], cwd=root, check=False)
        if p2.returncode != 0:
            sys.stderr.write(p.stderr or "")
            sys.stderr.write(p2.stderr or "")
            die(f"could not check out branch {gid} from upstream/main")


def write_lean(root: Path, gid: str, text: str) -> Path:
    path = pnplib.lean_path(root, gid)
    path.parent.mkdir(parents=True, exist_ok=True)
    if '"' in text:
        die("template produced a double quote; refusing to write")
    path.write_text(text, encoding="utf-8")
    print(f"gen_twin: wrote {path.relative_to(root)}", file=sys.stderr)
    return path


def lake_build(root: Path, gid: str) -> None:
    mod = f"PEqualNP.Outside.{pnplib.gap_to_module(gid)}"
    print(f"gen_twin: lake build {mod}", file=sys.stderr)
    p = run(
        ["lake", "build", mod],
        cwd=root / "lean",
        check=False,
        timeout=600,
    )
    sys.stderr.write(p.stdout or "")
    sys.stderr.write(p.stderr or "")
    if p.returncode != 0:
        die(
            f"lake build failed for {mod}. Hand-edit {pnplib.lean_path(root, gid)} and rerun.",
            p.returncode,
        )


def precheck(root: Path, lean_file: Path) -> None:
    script = HERE / "precheck.sh"
    run(["bash", str(script), str(lean_file)], cwd=root, timeout=60)


def check_lean(root: Path, lean_file: Path, posted: str, desk_kind: str) -> None:
    chk = "refute" if desk_kind == "refute" else "check"
    stmt_path = Path(tempfile.gettempdir()) / f"{lean_file.stem}.stmt"
    stmt_path.write_text(posted + "\n", encoding="utf-8")
    print(f"gen_twin: check-lean {chk} (desk kind {desk_kind})", file=sys.stderr)
    p = run(
        ["node", "tools/check-lean.mjs", str(lean_file), str(stmt_path), chk],
        cwd=root,
        check=False,
        timeout=300,
    )
    sys.stderr.write(p.stdout or "")
    sys.stderr.write(p.stderr or "")
    if p.returncode != 0:
        die("check-lean failed; not pushing", p.returncode)
    if "ACCEPTED" not in (p.stdout or "") + (p.stderr or ""):
        die("check-lean did not print ACCEPTED; not pushing")


def commit_and_push(root: Path, gid: str, lemma_id: str, kind: str, lean_file: Path) -> None:
    rel = str(lean_file.relative_to(root))
    run(["git", "add", rel], cwd=root)
    msg = (
        f"{'Refute' if kind == 'refute' else 'Prove'} {gid} via merged {lemma_id}\n\n"
        "Generated by .cursor/tools/gen_twin.py from the twin-pair template.\n"
    )
    run(["git", "commit", "-m", msg], cwd=root, env=GIT_ENV)
    run(["bash", str(HERE / "new_steps.sh"), "--push", rel], cwd=root, timeout=120)
    diff = 2
    print(f"PUSHED {gid} (difficulty {diff}/10)")


def process_one(
    root: Path,
    gid: str,
    lemma_id: str,
    kind_cli: str,
    by_id: dict,
    dry_run: bool,
    do_push: bool,
    do_build: bool,
    do_check: bool,
) -> None:
    row = pnplib.fetch_desk_row(gid) or by_id.get(gid) or {}
    desk_kind = pnplib.checker_kind(row)
    find = pnplib.is_find_row(row)
    posted = (row.get("statement") or "").strip() or gap_stmt(by_id, gid)
    if '"' in posted:
        die(f"gap {gid} statement contains a string literal; template will not emit quotes")
    lemma_path = pnplib.lean_path(root, lemma_id)
    if not lemma_path.is_file():
        die(f"merged lemma file missing: {lemma_path}")
    rec = rg.lemma_record(lemma_path)
    if not rec or not rec.get("type"):
        die(f"could not read last theorem of {lemma_id}")
    listed = pnplib.listed_imports(row)
    print(
        f"gen_twin: desk {gid} kind={desk_kind} find={find} imports={listed}",
        file=sys.stderr,
    )
    require_listed_lemma(gid, lemma_id, listed)
    kind, why = choose_template(kind_cli, posted, rec["type"], desk_kind=desk_kind)
    if kind == "refute" and desk_kind != "refute":
        die(
            f"desk posts {gid} as kind {desk_kind} (find={find}); "
            "will not emit ¬ of a check/find row"
        )
    wrap = desk_kind == "refute"
    print(f"gen_twin: {gid} via {lemma_id} kind={kind} ({why})", file=sys.stderr)
    text = emit_file(
        kind, gid, lemma_id, posted, rec["type"], wrap=wrap, listed=listed
    )
    for name in pnplib.parse_import_names(text):
        if not pnplib.import_is_allowed(name, listed):
            die(
                f"template import {name} is not allowed "
                f"(only Mathlib and {listed})"
            )
    if pnplib.theorem_wraps_posted(
        pnplib.last_theorem_type_of_text(text) or "", posted
    ) and desk_kind != "refute":
        die(
            f"template wrapped ¬ around posted statement of check/find row {gid}"
        )
    if dry_run:
        sys.stdout.write(text)
        return
    if do_push:
        ensure_branch(root, gid)
    path = write_lean(root, gid, text)
    if do_build:
        lake_build(root, gid)
        precheck(root, path)
    if do_push:
        if do_check:
            check_lean(root, path, posted, desk_kind)
        commit_and_push(root, gid, lemma_id, kind, path)


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("gap", nargs="?", help="open gap id, e.g. L-meta-25652")
    ap.add_argument("lemma", nargs="?", help="merged lemma id, e.g. L-meta-25645")
    ap.add_argument("--kind", choices=("auto", "refute", "witness", "check"), default="auto")
    ap.add_argument("--push", action="store_true", help="branch, commit, precheck, push")
    ap.add_argument("--dry-run", action="store_true", help="print Lean to stdout")
    ap.add_argument("--no-build", action="store_true")
    ap.add_argument("--no-check", action="store_true", help="skip check-lean")
    ap.add_argument("--from-rank", action="store_true", help="take twins from rank_gaps.py")
    ap.add_argument("--limit", type=int, default=5, help="with --from-rank, max twins")
    args = ap.parse_args()

    root = Path(
        subprocess.check_output(["git", "rev-parse", "--show-toplevel"], text=True).strip()
    )
    gaps_blob = pnplib.fetch_json(pnplib.GAPS_URL, ua="rank-gaps/1")
    by_id = {g["id"]: g for g in (gaps_blob.get("gaps") or []) if g.get("id")}

    jobs: list[tuple[str, str, str]] = []
    if args.from_rank:
        status = pnplib.fetch_json(pnplib.STATUS_URL, ua="rank-gaps/1")
        last = rg.read_last_sha(root)
        head = rg.ensure_upstream(root, fetch=True)
        twins = rg.find_twins(root, status, by_id, last, head, kinds=None)
        for t in twins:
            if not t.get("pushable"):
                print(
                    f"gen_twin: skip {t['id']} ({t.get('why')}); "
                    "would negate a check/find row — lease the twin with "
                    "tools/pnp.sh next --kind refute",
                    file=sys.stderr,
                )
                continue
            if t.get("kind") == "refute" and t.get("desk_kind") != "refute":
                print(
                    f"gen_twin: skip {t['id']}: desk kind is "
                    f"{t.get('desk_kind')}, not refute",
                    file=sys.stderr,
                )
                continue
            if t.get("listed") is False:
                print(
                    f"gen_twin: skip {t['id']} via {t['lemma']}: "
                    "lemma module is not in the desk row imports",
                    file=sys.stderr,
                )
                continue
            jobs.append((t["id"], t["lemma"], t["kind"]))
            if len(jobs) >= args.limit:
                break
        if not jobs:
            print("gen_twin: no pushable twins from rank", file=sys.stderr)
            return 0
    else:
        if not args.gap or not args.lemma:
            die("usage: gen_twin.py GAP LEMMA [--push]  or  gen_twin.py --from-rank [--push]")
        jobs.append((args.gap, args.lemma, args.kind))

    for gid, lemma_id, kind in jobs:
        # Skip if an open GitHub PR already exists at start.
        if not args.dry_run:
            blocked = pnplib.gh_open_titles([gid])
            if gid in blocked:
                print(f"gen_twin: skip {gid}, open PR already", file=sys.stderr)
                continue
            remote = run(
                ["git", "ls-remote", "--heads", "origin", gid],
                cwd=root,
                check=False,
            )
            if (remote.stdout or "").strip():
                print(f"gen_twin: skip {gid}, origin already has branch", file=sys.stderr)
                continue
        k = args.kind if args.kind != "auto" else kind
        process_one(
            root,
            gid,
            lemma_id,
            k if k in ("auto", "refute", "witness", "check") else "auto",
            by_id,
            dry_run=args.dry_run,
            do_push=args.push,
            do_build=not args.no_build and not args.dry_run,
            do_check=not args.no_check,
        )
    return 0


if __name__ == "__main__":
    sys.exit(main())
