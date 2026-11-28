#!/usr/bin/env python3
"""Generator for Table 2 / mono6-screened-orbits prove units.

Emits a non-inductive Lean file in the shape of merged L-meta-40217 (PR 48392)
and L-meta-40417 (PR 48185): a 10-gate AND/OR witness plus a kernel-checked
search certificate that no 8-binary-gate AND/OR/ANDNOT circuit hits the packed
goal. See .cursor/TRICKS.md.

    python3 .cursor/tools/gen_mono6.py \\
        --id L-meta-40217 --hi 4276808426 --lo 4272482952 \\
        --out lean/PEqualNP/Outside/L_meta_40217.lean

No double quotes in the emitted Lean. No sorry / axiom / native_decide /
inductive / macro / notation.
"""
from __future__ import annotations

import argparse
import itertools
import os
import re
import shutil
import subprocess
import sys
import tempfile
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
ENGINE_PATH = ROOT / ".cursor" / "templates" / "Mono6Engine.lean"

MASK64 = (1 << 64) - 1
MASK128 = (1 << 128) - 1
MASK256 = (1 << 256) - 1
MOD_HASH = 1000003
NB = 256
GBUCKET = 8
N_SEARCH = 8
DECIDE_HDR = (
    "set_option maxRecDepth 1000000 in\n"
    "set_option maxHeartbeats 0 in\n"
)


def bvnot(x: int) -> int:
    return (~x) & MASK256


def sep(x: int) -> int:
    return ((x >> 128) ^ x) & MASK128


def cuts(ws: list[int]) -> int:
    v = 0
    for w in ws:
        v |= sep(w)
    return v


def ops(a: int, b: int) -> list[int]:
    return [a & b, a | b, a & bvnot(b), b & bvnot(a)]


def insert_w(x: int, ys: list[int]) -> list[int]:
    out: list[int] = []
    i = 0
    while i < len(ys) and not (x <= ys[i]):
        out.append(ys[i])
        i += 1
    out.append(x)
    out.extend(ys[i:])
    return out


def canon(ws: list[int]) -> list[int]:
    acc: list[int] = []
    for x in reversed(ws):
        acc = insert_w(x, acc)
    return acc


def singles(ws: list[int]) -> list[tuple[int, list[int]]]:
    if not ws:
        return []
    a, rest = ws[0], ws[1:]
    out = [(a, rest)]
    for b, bs in singles(rest):
        out.append((b, [a] + bs))
    return out


def pairs(ws: list[int]) -> list[tuple[int, int, list[int]]]:
    if not ws:
        return []
    a, rest = ws[0], ws[1:]
    out = [(a, b, bs) for b, bs in singles(rest)]
    out.extend((b, c, [a] + bs) for b, c, bs in pairs(rest))
    return out


def kids_of(extra: int, a: int, b: int, r: list[int], w: int) -> list[tuple[int, list[int]]]:
    v = sep(w) | cuts(r)
    out: list[tuple[int, list[int]]] = []
    if v == MASK128:
        out.append((extra, canon([w] + r)))
    if extra != 0 and (v | sep(a)) == MASK128:
        out.append((extra - 1, canon([w, a] + r)))
    if extra != 0 and (v | sep(b)) == MASK128:
        out.append((extra - 1, canon([w, b] + r)))
    if extra >= 2 and (v | sep(a) | sep(b)) == MASK128:
        out.append((extra - 2, canon([w, a, b] + r)))
    return out


def children(c: tuple[int, tuple[int, ...]]) -> list[tuple[int, tuple[int, ...]]]:
    extra, ws = c[0], list(c[1])
    out: list[tuple[int, tuple[int, ...]]] = []
    for a, b, r in pairs(ws):
        for w in ops(a, b):
            for e, lst in kids_of(extra, a, b, r, w):
                out.append((e, tuple(lst)))
    return out


def sublists(ws: list[int]) -> list[list[int]]:
    if not ws:
        return [[]]
    x, xs = ws[0], ws[1:]
    rest = sublists(xs)
    return [[x] + t for t in rest] + rest


def level0(n: int, inputs: list[int]) -> list[tuple[int, tuple[int, ...]]]:
    out = []
    for ws in sublists(inputs):
        if len(ws) <= n + 1 and cuts(ws) == MASK128:
            out.append((n + 1 - len(ws), tuple(canon(ws))))
    return out


def hash_w(acc: int, w: int) -> int:
    return (acc * 31 + w) % MOD_HASH


def hash_s(nb: int, extra: int, ws: tuple[int, ...]) -> int:
    acc = extra
    for w in ws:
        acc = hash_w(acc, w)
    return acc % nb


def pack_rows(table: int) -> list[int]:
    """256-bit input signatures with unit-vector seps.

    Low 128 columns are f=1 assignments, high 128 are f=0. Hamming-distance-1
    pairs are preferred so only the full 6-input set has cuts = -1.
    """
    ones = [i for i in range(64) if (table >> i) & 1]
    zeros = [i for i in range(64) if not ((table >> i) & 1)]
    if not ones or not zeros:
        raise ValueError("constant table; packing needs both ones and zeros")

    pairs_oz: list[tuple[int, int]] = []
    used_o: set[int] = set()
    used_z: set[int] = set()

    def add_pair(o: int, z: int) -> None:
        pairs_oz.append((o, z))
        used_o.add(o)
        used_z.add(z)

    for bit in range(6):
        found = False
        for o in ones:
            z = o ^ (1 << bit)
            if z in zeros:
                add_pair(o, z)
                found = True
                break
        if not found:
            for z in zeros:
                o = z ^ (1 << bit)
                if o in ones:
                    add_pair(o, z)
                    found = True
                    break
        if not found:
            add_pair(ones[0], zeros[0])

    for o in ones:
        if o in used_o:
            continue
        zbest = min(zeros, key=lambda z: (bin(o ^ z).count("1"), z))
        add_pair(o, zbest)
    for z in zeros:
        if z in used_z:
            continue
        obest = min(ones, key=lambda o: (bin(o ^ z).count("1"), o))
        add_pair(obest, z)

    d1 = [(o, z) for o in ones for z in zeros if (o ^ z) in (1, 2, 4, 8, 16, 32)]
    pool = d1 or [(ones[i % len(ones)], zeros[i % len(zeros)]) for i in range(128)]
    i = 0
    while len(pairs_oz) < 128:
        pairs_oz.append(pool[i % len(pool)])
        i += 1
    pairs_oz = pairs_oz[:128]

    rows = [0] * 6
    for k, (o, z) in enumerate(pairs_oz):
        for bit in range(6):
            if (o >> bit) & 1:
                rows[bit] |= 1 << k
            if (z >> bit) & 1:
                rows[bit] |= 1 << (k + 128)
    return rows


def bit_col(rows: list[int], k: int) -> int:
    v = 0
    for i, r in enumerate(rows):
        if (r >> k) & 1:
            v |= 1 << i
    return v


def packing_ok(table: int, rows: list[int]) -> tuple[bool, str]:
    if len(rows) != 6 or len(set(rows)) != 6:
        return False, "rows not 6 distinct"
    seen: set[int] = set()
    for k in range(256):
        x = bit_col(rows, k)
        want = 1 if k < 128 else 0
        if ((table >> x) & 1) != want:
            return False, f"sample mismatch at bit {k}"
        seen.add(x)
    if len(seen) != 64:
        return False, f"only {len(seen)} assignments sampled"
    xors = [bit_col(rows, k) ^ bit_col(rows, k + 128) for k in range(128)]
    covers = [s for s in range(64) if all((x & s) != 0 for x in xors)]
    if covers != [63]:
        return False, f"cuts covers {covers!r}, want only 63"
    return True, "ok"


class Cnf:
    def __init__(self):
        self.n = 0
        self.clauses: list[tuple[int, ...]] = []
        self.names: dict[tuple, int] = {}

    def var(self, *key):
        if key in self.names:
            return self.names[key]
        self.n += 1
        self.names[key] = self.n
        return self.n

    def add(self, *lits):
        self.clauses.append(tuple(int(x) for x in lits))

    def exactly_one(self, vs):
        vs = list(vs)
        self.add(*vs)
        for a, b in itertools.combinations(vs, 2):
            self.add(-a, -b)

    def iff_and(self, o, ins):
        if not ins:
            self.add(o)
            return
        for a in ins:
            self.add(-o, a)
        self.add(o, *[-a for a in ins])

    def iff_or(self, o, ins):
        if not ins:
            self.add(-o)
            return
        for a in ins:
            self.add(-a, o)
        self.add(-o, *ins)


def eval_mono(gates: list[tuple[str, int, int]], output: int, x: int) -> int:
    wires = [(x >> i) & 1 for i in range(6)]
    for op, a, b in gates:
        va = wires[a] if a < len(wires) else 0
        vb = wires[b] if b < len(wires) else 0
        wires.append((va & vb) if op == "and" else (va | vb))
    return wires[output] if output < len(wires) else 0


def sat_witness(table: int, n_gates: int = 10, timeout: int = 60):
    """AND/OR fan-in-two circuit of n_gates computing the 6-input table."""
    kissat = shutil.which("kissat")
    if not kissat:
        return None
    c = Cnf()
    for x in range(64):
        for i in range(6):
            v = c.var("v", i, x)
            c.add(v if (x >> i) & 1 else -v)
    for g in range(n_gates):
        w = 6 + g
        srcs = list(range(w))
        c.exactly_one([c.var("a", g, i) for i in srcs])
        c.exactly_one([c.var("b", g, i) for i in srcs])
        is_and = c.var("and", g)
        for x in range(64):
            va = c.var("va", g, x)
            vb = c.var("vb", g, x)
            terms_a = []
            terms_b = []
            for i in srcs:
                ta = c.var("ta", g, x, i)
                tb = c.var("tb", g, x, i)
                c.iff_and(ta, [c.var("a", g, i), c.var("v", i, x)])
                c.iff_and(tb, [c.var("b", g, i), c.var("v", i, x)])
                terms_a.append(ta)
                terms_b.append(tb)
            c.iff_or(va, terms_a)
            c.iff_or(vb, terms_b)
            vand = c.var("vand", g, x)
            vor = c.var("vor", g, x)
            c.iff_and(vand, [va, vb])
            c.iff_or(vor, [va, vb])
            t1 = c.var("t1", g, x)
            t2 = c.var("t2", g, x)
            c.iff_and(t1, [is_and, vand])
            c.iff_and(t2, [-is_and, vor])
            c.iff_or(c.var("v", w, x), [t1, t2])
    outw = 5 + n_gates
    for x in range(64):
        c.add(c.var("v", outw, x) if (table >> x) & 1 else -c.var("v", outw, x))
    with tempfile.NamedTemporaryFile("w", suffix=".cnf", delete=False) as fh:
        fh.write(f"p cnf {c.n} {len(c.clauses)}\n")
        for cl in c.clauses:
            fh.write(" ".join(str(x) for x in cl) + " 0\n")
        path = fh.name
    try:
        r = subprocess.run(
            [kissat, "--sat", "-q", path],
            capture_output=True,
            text=True,
            timeout=timeout,
        )
    except subprocess.TimeoutExpired:
        os.unlink(path)
        print("kissat timeout", file=sys.stderr)
        return None
    os.unlink(path)
    sat = r.returncode == 10 or "s SATISFIABLE" in r.stdout
    if not sat:
        print(f"kissat rc={r.returncode} unsat/error", file=sys.stderr)
        return None
    assign: set[int] = set()
    for line in r.stdout.splitlines():
        if line.startswith("v "):
            for tok in line.split()[1:]:
                n = int(tok)
                if n > 0:
                    assign.add(n)
    gates = []
    for g in range(n_gates):
        w = 6 + g
        a = next(i for i in range(w) if c.var("a", g, i) in assign)
        b = next(i for i in range(w) if c.var("b", g, i) in assign)
        op = "and" if c.var("and", g) in assign else "or"
        gates.append((op, a, b))
    return gates, 5 + n_gates


def dump_frontiers(rows: list[int]):
    parents = level0(N_SEARCH, rows)
    if not parents:
        raise RuntimeError("level0 empty: packing did not cover cuts")
    step1: list[tuple[int, tuple[int, ...]]] = []
    seen1: set[tuple[int, tuple[int, ...]]] = set()
    for p in parents:
        for c in children(p):
            if c not in seen1:
                seen1.add(c)
                step1.append(c)
    states_a: list[tuple[int, tuple[int, ...]]] = []
    seen_a: set[tuple[int, tuple[int, ...]]] = set()
    for c in step1:
        for x in children(c):
            if x not in seen_a:
                seen_a.add(x)
                states_a.append(x)
    states_b: list[tuple[int, tuple[int, ...]]] = []
    seen_b: set[tuple[int, tuple[int, ...]]] = set()
    for c in states_a:
        for x in children(c):
            if x not in seen_b:
                seen_b.add(x)
                states_b.append(x)
    return parents, states_a, states_b


def to_buckets(states: list[tuple[int, tuple[int, ...]]]):
    bk: list[list[list[tuple[int, tuple[int, ...]]]]] = [
        [[] for _ in range(GBUCKET)] for _ in range(NB // GBUCKET)
    ]
    for extra, ws in states:
        h = hash_s(NB, extra, ws)
        bk[h // GBUCKET][h % GBUCKET].append((extra, ws))
    return bk


def intern_z(bk_a, bk_b, rows: list[int]) -> tuple[dict[int, str], list[int]]:
    order: list[int] = []
    seen: set[int] = set()

    def add(w: int) -> None:
        if w not in seen:
            seen.add(w)
            order.append(w)

    for r in rows:
        add(r)
    for group in bk_a:
        for bucket in group:
            for extra, ws in bucket:
                for w in ws:
                    add(w)
    for group in bk_b:
        for bucket in group:
            for extra, ws in bucket:
                for w in ws:
                    add(w)
    names = {w: f"z{i}" for i, w in enumerate(order)}
    return names, order


def split256(w: int) -> tuple[int, int, int, int]:
    return (
        (w >> 192) & MASK64,
        (w >> 128) & MASK64,
        (w >> 64) & MASK64,
        w & MASK64,
    )


def fmt_hex64(x: int) -> str:
    return f"0x{x:016x}"


def fmt_row(w: int) -> str:
    a, b, c, d = split256(w)
    return (
        f"({fmt_hex64(a)}#64 ++ {fmt_hex64(b)}#64 ++ "
        f"{fmt_hex64(c)}#64 ++ {fmt_hex64(d)}#64 : BitVec 256)"
    )


def fmt_mkw(w: int) -> str:
    a, b, c, d = split256(w)
    return f"mkw {fmt_hex64(a)} {fmt_hex64(b)} {fmt_hex64(c)} {fmt_hex64(d)}"


def fmt_gates(gates: list[tuple[str, int, int]]) -> str:
    return "[" + ", ".join(f"⟨.{op}, [{a}, {b}]⟩" for op, a, b in gates) + "]"


def fmt_state(extra: int, ws: tuple[int, ...], zname: dict[int, str]) -> str:
    inner = ",".join(zname[w] for w in ws)
    return f"({extra},[{inner}])"


def fmt_bk(bk, zname: dict[int, str]) -> str:
    groups = []
    for group in bk:
        buckets = []
        for bucket in group:
            body = ",".join(fmt_state(e, ws, zname) for e, ws in bucket)
            buckets.append("[" + body + "]")
        groups.append("[" + ",".join(buckets) + "]")
    return "[\n   " + ",\n   ".join(groups) + "]"


def chunk_sizes(n: int, target: int) -> list[int]:
    if n <= 0:
        return []
    k = max(1, (n + target - 1) // target)
    base, rem = divmod(n, k)
    return [base + (1 if i < rem else 0) for i in range(k)]


def emit_decide_windows(
    kind: str,
    pred: str,
    expr: str,
    sizes: list[int],
    total: int,
) -> str:
    """kind=A uses windowsG on a state list; kind=C uses windowsF on buckets."""
    parts: list[str] = []
    prefix = {"A": "pa", "B": "pb", "C": "pc"}[kind]
    acc = 0
    names = []
    for i, s in enumerate(sizes):
        thm = f"{prefix}{i}"
        names.append((thm, s, acc))
        if kind == "C":
            goal = f"chunkOK 5 (({expr}.drop {acc}).take {s}).flatten = true"
        else:
            d = 2 if kind == "A" else 1
            goal = f"chunkB {pred} {d} (({expr}.drop {acc}).take {s}) = true"
        parts.append(
            f"{DECIDE_HDR}theorem {thm} : {goal} := by\n  decide +kernel\n"
        )
        acc += s
    end = f"{prefix}end"
    parts.append(
        f"{DECIDE_HDR}theorem {end} : (({expr}.drop {total})).isEmpty = true := by\n"
        f"  decide +kernel\n"
    )
    if kind == "C":
        cons = "windowsF_cons"
        nil = "windowsF_nil"
        win = f"windowsF 5 {expr} 0 {sizes}"
        wname = "windowsC"
    elif kind == "A":
        cons = "windowsG_cons"
        nil = "windowsG_nil"
        win = f"windowsG (chunkB {pred} 2) {expr} 0 {sizes}"
        wname = "windowsA"
    else:
        cons = "windowsG_cons"
        nil = "windowsG_nil"
        win = f"windowsG (chunkB {pred} 1) {expr} 0 {sizes}"
        wname = "windowsB"
    tree = f"{nil} {end}"
    for thm, _s, _a in reversed(names):
        tree = f"{cons} {thm} ({tree})"
    parts.append(f"theorem {wname} : {win} = true :=\n  {tree}\n")
    return "\n".join(parts)


def module_of(gid: str) -> str:
    return "PEqualNP.Outside." + gid.replace("-", "_")


def short_mod(gid: str) -> str:
    return gid.replace("-", "_")


def statement_of(hi: int, lo: int) -> str:
    tbl = (
        f"Nat.testBit ({hi} * 2 ^ 32 + {lo}) "
        f"(∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)"
    )
    return (
        f"∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 "
        f"(fun x : Fin 6 → Bool => {tbl}) s → "
        f"∃ C : PEqualNP.CircuitLowerBounds.Circuit, "
        f"PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ "
        f"∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = {tbl}"
    )


def emit_lean(
    gid: str,
    hi: int,
    lo: int,
    rows: list[int],
    gates: list[tuple[str, int, int]],
    output: int,
    parents,
    bk_a,
    bk_b,
    zname: dict[int, str],
    zorder: list[int],
) -> str:
    engine = ENGINE_PATH.read_text(encoding="utf-8")
    mod = short_mod(gid)
    engine = engine.replace("L_meta_ENGINE", mod)
    engine = engine.replace("def tableHi : ℕ := 0", f"def tableHi : ℕ := {hi}")
    engine = engine.replace("def tableLo : ℕ := 0", f"def tableLo : ℕ := {lo}")
    n_parent = len(parents)
    n_a = sum(len(b) for g in bk_a for b in g)
    n_b_buckets = NB
    sizes_a = chunk_sizes(n_parent, 8) or [0]
    sizes_b = chunk_sizes(n_a, 500)
    sizes_c = chunk_sizes(n_b_buckets, 100)
    rows_s = ",\n   ".join(fmt_row(r) for r in rows)
    z_s = "\n\n".join(f"def {zname[w]} : W := {fmt_mkw(w)}" for w in zorder)
    inst = f"""
def rows : List W :=
  [{rows_s}]

def witness : Circuit :=
  ⟨{fmt_gates(gates)}, {output}⟩

def mkw (a b c d : BitVec 64) : W := a ++ b ++ c ++ d

{z_s}

{DECIDE_HDR}def bkA : List (List (List (ℕ × List W))) :=
  {fmt_bk(bk_a, zname)}

{DECIDE_HDR}def bkB : List (List (List (ℕ × List W))) :=
  {fmt_bk(bk_b, zname)}

def SA : ℕ × List W → Bool := fun c => !inB2 8 256 bkA c

def SB : ℕ × List W → Bool := fun c => !inB2 8 256 bkB c

def parents : List (ℕ × List W) := expandN 0 (level0 8 rows)

{DECIDE_HDR}theorem gf : allGoalFree 0 (level0 8 rows) = true := by
  decide +kernel

{emit_decide_windows("A", "SA", "parents", sizes_a, n_parent)}
{emit_decide_windows("B", "SB", "bkA.flatten.flatten", sizes_b, n_a)}
{emit_decide_windows("C", "SB", "bkB.flatten", sizes_c, n_b_buckets)}
theorem reject : search 8 rows = false :=
  search_false_C2 (dp := 0) (J := 5) (d := 2) (g1 := 8) (nb1 := 256) (g2 := 8) (nb2 := 256) (by norm_num) gf windowsC windowsB windowsA

{DECIDE_HDR}theorem witness_ok : ∀ x : Fin 6 → Bool, Circuit.eval witness (List.ofFn x) = target x := by
  decide +kernel

{DECIDE_HDR}theorem sample_ok : ∀ k : Fin 256, target (fun i => (rows.getD i.val 0)[k.val]) = (~~~goal)[k.val] := by
  decide +kernel

theorem solve (s : ℕ) (hs : HasCircuitSize 6 target s) :
    ∃ C : Circuit, Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = target x := by
  obtain ⟨C, fits, size, computes⟩ := hs
  by_cases hasNot : ∃ g ∈ C.gates, g.op = GateOp.not
  · obtain ⟨g, mem, op⟩ := hasNot
    have short : binaryCost C.gates < C.size :=
      (List.length_filter_lt_length_iff_exists (p := isBinary)).mpr
        ⟨g, mem, by simp [isBinary, op]⟩
    have bound := bound_from_search rows rfl (by decide) reject sample_ok C.gates C.output fits computes
    refine ⟨witness, by simp [Monotone2, witness], ?_, witness_ok⟩
    have wsz : Circuit.size witness = {len(gates)} := rfl
    omega
  · refine ⟨C, ?_, size, computes⟩
    intro g mem
    obtain ⟨op, cap⟩ := fits g mem
    change g.op = .and ∨ g.op = .or ∨ g.op = .not at op
    exact ⟨op.elim Or.inl (fun h => h.elim Or.inr (fun eq => (hasNot ⟨g, mem, eq⟩).elim)), cap⟩

end PEqualNP.Outside.{mod}

theorem PEqualNP.Outside.{mod} :
    {statement_of(hi, lo)} := by
  exact PEqualNP.Outside.{mod}.solve
"""
    return engine.rstrip() + "\n" + inst


def forbidden_scan(text: str) -> list[str]:
    hits = []
    if '"' in text:
        hits.append("double quote")
    pat = re.compile(
        r"\b(inductive|sorry|axiom|native_decide|macro|syntax|notation|elab)\b"
    )
    for i, line in enumerate(text.splitlines(), 1):
        m = pat.search(line)
        if m:
            hits.append(f"{i}:{m.group(1)}")
    return hits


def generate(hi: int, lo: int, gid: str, n_gates: int, sat_timeout: int):
    table = ((hi & MASK64) << 32) | (lo & MASK64)
    t0 = time.time()
    rows = pack_rows(table)
    ok, why = packing_ok(table, rows)
    log = [f"table {hi}*2^32+{lo} pop={table.bit_count()} packing={why}"]
    if not ok:
        raise RuntimeError("packing failed: " + why)
    t1 = time.time()
    wit = sat_witness(table, n_gates=n_gates, timeout=sat_timeout)
    t2 = time.time()
    if wit is None:
        raise RuntimeError(f"no {n_gates}-gate AND/OR witness (kissat timeout/unsat)")
    gates, output = wit
    bad = sum(1 for x in range(64) if eval_mono(gates, output, x) != ((table >> x) & 1))
    if bad:
        raise RuntimeError(f"witness replay failed on {bad} inputs")
    log.append(f"witness {len(gates)} gates output={output} sat={t2-t1:.2f}s")
    parents, states_a, states_b = dump_frontiers(rows)
    t3 = time.time()
    bk_a = to_buckets(states_a)
    bk_b = to_buckets(states_b)
    zname, zorder = intern_z(bk_a, bk_b, rows)
    log.append(
        f"parents={len(parents)} bkA={len(states_a)} bkB={len(states_b)} "
        f"z={len(zorder)} dump={t3-t2:.2f}s total={t3-t0:.2f}s"
    )
    text = emit_lean(gid, hi, lo, rows, gates, output, parents, bk_a, bk_b, zname, zorder)
    hits = forbidden_scan(text)
    if hits:
        raise RuntimeError("forbidden tokens in emit: " + ", ".join(hits[:8]))
    return text, log


def parse_from_lean(path: Path) -> tuple[int, int] | None:
    m = re.search(r"Nat\.testBit \((\d+) \* 2 \^ 32 \+ (\d+)\)", path.read_text())
    if not m:
        return None
    return int(m.group(1)), int(m.group(2))


def main() -> int:
    ap = argparse.ArgumentParser(description="Table 2 / mono6 prove-file generator")
    ap.add_argument("--id", default="L-meta-WIP", help="gap id, e.g. L-meta-40217")
    ap.add_argument("--hi", type=int, help="high 32 bits of the 64-bit table")
    ap.add_argument("--lo", type=int, help="low 32 bits")
    ap.add_argument("--table", type=int, help="full 64-bit table")
    ap.add_argument("--from-lean", type=Path, help="read HI/LO from a merged Lean file")
    ap.add_argument("--out", type=Path)
    ap.add_argument("--gates", type=int, default=10)
    ap.add_argument("--sat-timeout", type=int, default=90)
    ap.add_argument("--self-test", action="store_true")
    args = ap.parse_args()

    if args.from_lean:
        parsed = parse_from_lean(args.from_lean)
        if not parsed:
            print("no table in --from-lean", file=sys.stderr)
            return 2
        hi, lo = parsed
        if args.id == "L-meta-WIP":
            m = re.search(r"L_meta_(\d+)", args.from_lean.name)
            if m:
                args.id = f"L-meta-{m.group(1)}"
    elif args.table is not None:
        hi, lo = (args.table >> 32) & MASK64, args.table & MASK64
    elif args.hi is not None and args.lo is not None:
        hi, lo = args.hi, args.lo
    else:
        hi, lo = 4276808426, 4272482952
        if args.id == "L-meta-WIP":
            args.id = "L-meta-40217"

    if not ENGINE_PATH.is_file():
        print(f"missing engine template {ENGINE_PATH}", file=sys.stderr)
        return 2

    try:
        text, log = generate(hi, lo, args.id, args.gates, args.sat_timeout)
    except Exception as e:
        print(f"gen_mono6 failed: {e}", file=sys.stderr)
        return 1
    for line in log:
        print(line, file=sys.stderr)
    if args.self_test and args.out is None:
        print(f"emit {len(text)} bytes ok", file=sys.stderr)
        return 0
    out = args.out
    if out is None:
        out = ROOT / "lean" / "PEqualNP" / "Outside" / f"{short_mod(args.id)}.lean"
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(text, encoding="utf-8")
    print(f"wrote {out} ({out.stat().st_size} bytes)", file=sys.stderr)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
