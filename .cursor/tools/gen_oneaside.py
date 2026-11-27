#!/usr/bin/env python3
"""Batch generator for one-a-side Represents gaps.

Family: some FanInTwo circuit of size at most K represents the n-by-m bipartite
graph whose adjacency bits are mask.testBit (m * u + v), on the oneEach promise.

SAT-searches a witness with kissat --sat (60s default), then emits one Lean
file in the shape of merged L_meta_19039.lean (Apache License 2.0,
open-goat/pequalnp-proofs): a named Circuit witness, FanInTwo by simp, size
and Represents by decide +kernel.

No double quotes in the emitted Lean. Skip L-meta-19051 (k=8 boundary) and
the sibling-held 19209/19265. Full-encoder unsat at kmax (refute later):
L-meta-19218 (k=6) and L-meta-19078 (k=7).
"""
from __future__ import annotations

import argparse
import itertools
import json
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

OPS = ("and", "or", "not")
LEAN_OP = {
    "and": "PEqualNP.CircuitLowerBounds.GateOp.and",
    "or": "PEqualNP.CircuitLowerBounds.GateOp.or",
    "not": "PEqualNP.CircuitLowerBounds.GateOp.not",
}


class Cnf:
    def __init__(self):
        self.n = 0
        self.clauses = []
        self.names = {}

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
        if not vs:
            self.add()
            return
        self.add(*vs)
        for a, b in itertools.combinations(vs, 2):
            self.add(-a, -b)

    def at_most_one(self, vs):
        vs = list(vs)
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

    def dump(self, fh):
        fh.write(f"p cnf {self.n} {len(self.clauses)}\n")
        for cl in self.clauses:
            fh.write(" ".join(str(x) for x in cl) + " 0\n")


def one_each(n, m, u, v):
    return [i == u for i in range(n)] + [j == v for j in range(m)]


def adj(mask, m, u, v):
    return bool((mask >> (m * u + v)) & 1)


def eval_gate(op, args):
    if op == "and":
        return all(args) if args else True
    if op == "or":
        return any(args) if args else False
    if op == "not":
        return not (args[0] if args else False)
    raise ValueError(op)


def eval_circuit(gates, output, x):
    w = list(x)
    for op, ins in gates:
        args = [w[i] if 0 <= i < len(w) else False for i in ins]
        w.append(eval_gate(op, args))
    return w[output] if 0 <= output < len(w) else False


def represents(gates, output, n, m, mask):
    for u in range(n):
        for v in range(m):
            got = eval_circuit(gates, output, one_each(n, m, u, v))
            if got != adj(mask, m, u, v):
                return False
    return True


def encode(n, m, mask, k):
    """CNF for a k-gate FanInTwo circuit representing mask on oneEach.

    Full FanInTwo: AND/OR/NOT, each slot empty or a prior wire, second slot
    implies the first, NOT uses at most one input. 0-input AND is true,
    0-input OR is false, 0-input NOT is true. Dummy padding gates allowed.
    """
    c = Cnf()
    nin = n + m
    nwire = nin + k

    def op(j, t):
        return c.var("op", j, t)

    def use(j, s, w):
        return c.var("use", j, s, w)

    def has(j, s):
        return c.var("has", j, s)

    def outw(w):
        return c.var("out", w)

    def val(t, w):
        return c.var("v", t, w)

    for j in range(k):
        c.exactly_one([op(j, t) for t in range(3)])
        nw = nin + j
        for s in (0, 1):
            wires = [use(j, s, w) for w in range(nw)]
            c.add(-has(j, s), *wires)
            c.at_most_one(wires)
            for w in range(nw):
                c.add(-use(j, s, w), has(j, s))
        c.add(-has(j, 1), has(j, 0))
        c.add(-op(j, 2), -has(j, 1))

    c.exactly_one([outw(w) for w in range(nwire)])

    points = [(u, v) for u in range(n) for v in range(m)]
    for t, (u, v) in enumerate(points):
        bits = one_each(n, m, u, v)
        for w in range(nin):
            if bits[w]:
                c.add(val(t, w))
            else:
                c.add(-val(t, w))
        for j in range(k):
            z = val(t, nin + j)
            nw = nin + j
            in0 = c.var("in0", t, j)
            in1 = c.var("in1", t, j)
            c.add(has(j, 0), -in0)
            for w in range(nw):
                c.add(-use(j, 0, w), -in0, val(t, w))
                c.add(-use(j, 0, w), in0, -val(t, w))
            c.add(has(j, 1), -in1)
            for w in range(nw):
                c.add(-use(j, 1, w), -in1, val(t, w))
                c.add(-use(j, 1, w), in1, -val(t, w))
            a0 = c.var("a0", t, j)
            a1 = c.var("a1", t, j)
            c.iff_or(a0, [-has(j, 0), in0])
            c.iff_or(a1, [-has(j, 1), in1])
            zand = c.var("zand", t, j)
            c.iff_and(zand, [a0, a1])
            o0 = c.var("o0", t, j)
            o1 = c.var("o1", t, j)
            c.iff_and(o0, [has(j, 0), in0])
            c.iff_and(o1, [has(j, 1), in1])
            zor = c.var("zor", t, j)
            c.iff_or(zor, [o0, o1])
            znot = c.var("znot", t, j)
            c.iff_or(znot, [-has(j, 0), -in0])
            c.add(-op(j, 0), -z, zand)
            c.add(-op(j, 0), z, -zand)
            c.add(-op(j, 1), -z, zor)
            c.add(-op(j, 1), z, -zor)
            c.add(-op(j, 2), -z, znot)
            c.add(-op(j, 2), z, -znot)

        want = adj(mask, m, u, v)
        y = c.var("y", t)
        parts = []
        for w in range(nwire):
            p = c.var("yp", t, w)
            c.iff_and(p, [outw(w), val(t, w)])
            parts.append(p)
        c.iff_or(y, parts)
        if want:
            c.add(y)
        else:
            c.add(-y)

    return c


def parse_model(text):
    vals = set()
    for line in text.splitlines():
        if not line.startswith("v "):
            continue
        for tok in line.split()[1:]:
            if tok == "0":
                continue
            lit = int(tok)
            if lit > 0:
                vals.add(lit)
    return vals


def decode(cnf: Cnf, model, n, m, k):
    nin = n + m
    nwire = nin + k
    true = set(model)
    gates = []
    for j in range(k):
        opname = None
        for t, name in enumerate(OPS):
            if cnf.names[("op", j, t)] in true:
                opname = name
        ins = []
        for s in (0, 1):
            if cnf.names.get(("has", j, s), 0) not in true:
                continue
            for w in range(nin + j):
                if cnf.names.get(("use", j, s, w), 0) in true:
                    ins.append(w)
                    break
        gates.append((opname, ins))
    output = None
    for w in range(nwire):
        if cnf.names[("out", w)] in true:
            output = w
            break
    return gates, output


def run_sat(cnf: Cnf, timeout=60):
    kissat = shutil.which("kissat")
    cadical = shutil.which("cadical")
    if not kissat and not cadical:
        raise SystemExit("need kissat or cadical")
    with tempfile.NamedTemporaryFile("w", suffix=".cnf", delete=False) as fh:
        cnf.dump(fh)
        cnf_path = fh.name
    cmd = None
    # Do not pass kissat --time: the wall-clock limit changes heuristics and
    # can turn a 3s SAT into a timeout. Enforce the budget with subprocess.
    if kissat:
        # --sat targets witnesses; default mode mixed sat/unsat heuristics.
        cmd = [kissat, "--sat", cnf_path]
    else:
        cmd = [cadical, cnf_path]
    try:
        r = subprocess.run(cmd, capture_output=True, text=True, timeout=timeout + 5)
    except subprocess.TimeoutExpired:
        return "timeout", None
    out = r.stdout + r.stderr
    if "s SATISFIABLE" in out or "\ns SATISFIABLE" in out:
        return "sat", parse_model(out)
    if "s UNSATISFIABLE" in out:
        return "unsat", None
    if "s UNKNOWN" in out or "c *** time limit hit" in out or "maximum time" in out.lower():
        return "timeout", None
    return "unknown", out[-500:]


def point_index(m, u, v):
    return m * u + v


def input_tables(n, m):
    """16-or-25-bit (n*m bits) table of each input wire on oneEach points."""
    pts = n * m
    tabs = []
    for i in range(n):
        t = 0
        for u in range(n):
            for v in range(m):
                if i == u:
                    t |= 1 << point_index(m, u, v)
        tabs.append(t)
    for j in range(m):
        t = 0
        for u in range(n):
            for v in range(m):
                if j == v:
                    t |= 1 << point_index(m, u, v)
        tabs.append(t)
    return tabs


def target_table(n, m, mask):
    t = 0
    for u in range(n):
        for v in range(m):
            if adj(mask, m, u, v):
                t |= 1 << point_index(m, u, v)
    return t


def apply_op(op, a, b, full):
    if op == "and":
        return a & b
    if op == "or":
        return a | b
    if op == "not":
        return full ^ a
    raise ValueError(op)


def bfs_circuit(n, m, mask, kmax):
    """Shortest FanInTwo circuit on the oneEach promise, as  n*m-bit tables."""
    full = (1 << (n * m)) - 1
    ins = input_tables(n, m)
    goal = target_table(n, m, mask)
    # how[val] = ('in', i) or (op, a, b_or_none)
    how = {t: ("in", i) for i, t in enumerate(ins)}
    if goal in how:
        return [], how[goal][1] if how[goal][0] == "in" else None

    from collections import deque

    start = tuple(ins)
    # state: tuple of wire tables (inputs + gates in order)
    q = deque([start])
    seen_states = {start}
    parent = {start: None}

    while q:
        cur = q.popleft()
        extra = len(cur) - (n + m)
        if extra >= kmax:
            continue
        avail = list(cur)
        # unary NOT and 0-ary constants, binary AND/OR
        candidates = []
        candidates.append(("and", None, None, full))  # 0-input AND = true
        candidates.append(("or", None, None, 0))  # 0-input OR = false
        for i, a in enumerate(avail):
            candidates.append(("not", i, None, full ^ a))
            candidates.append(("and", i, None, a))  # 1-input AND = identity
            candidates.append(("or", i, None, a))
            for j, b in enumerate(avail):
                candidates.append(("and", i, j, a & b))
                candidates.append(("or", i, j, a | b))
        # prefer new values
        for op, i, j, val in candidates:
            nxt = cur + (val,)
            if nxt in seen_states:
                continue
            seen_states.add(nxt)
            parent[nxt] = (cur, op, i, j, val)
            if val == goal:
                return reconstruct(nxt, parent, n, m, goal)
            q.append(nxt)
    return None


def reconstruct(state, parent, n, m, goal):
    steps = []
    cur = state
    while parent[cur] is not None:
        prev, op, i, j, val = parent[cur]
        ins = []
        if i is not None:
            ins.append(i)
        if j is not None:
            ins.append(j)
        steps.append((op, ins, val))
        cur = prev
    steps.reverse()
    gates = [(op, ins) for op, ins, _ in steps]
    # output is last wire that equals goal; prefer the first occurrence
    wires = list(input_tables(n, m))
    output = None
    for t in wires:
        if t == goal:
            output = wires.index(t)
            break
    for gi, (op, ins, val) in enumerate(steps):
        wires.append(val)
        if val == goal and output is None:
            output = (n + m) + gi
    if output is None:
        output = len(wires) - 1
    return gates, output, len(gates)


def rowcol_circuit(n, m, mask):
    """Row-OR then AND-left, or column-OR then AND-right; pick the shorter."""
    def build(side):
        gates = []
        terms = []
        if side == "row":
            for u in range(n):
                vs = [n + v for v in range(m) if adj(mask, m, u, v)]
                if not vs:
                    continue
                acc = vs[0]
                for w in vs[1:]:
                    gates.append(("or", [acc, w]))
                    acc = n + m + len(gates) - 1
                gates.append(("and", [u, acc]))
                terms.append(n + m + len(gates) - 1)
        else:
            for v in range(m):
                us = [u for u in range(n) if adj(mask, m, u, v)]
                if not us:
                    continue
                acc = us[0]
                for w in us[1:]:
                    gates.append(("or", [acc, w]))
                    acc = n + m + len(gates) - 1
                gates.append(("and", [acc, n + v]))
                terms.append(n + m + len(gates) - 1)
        if not terms:
            return [], 0
        acc = terms[0]
        for t in terms[1:]:
            gates.append(("or", [acc, t]))
            acc = n + m + len(gates) - 1
        return gates, acc

    a = build("row")
    b = build("col")
    return a if len(a[0]) <= len(b[0]) else b


def find_circuit(n, m, mask, kmax, timeout=60, minimize=False):
    """Find a FanInTwo circuit of size at most kmax.

    Tries a row/column construction first, then SAT at kmax. Timeouts and
    unsat at kmax are returned as None so the caller can skip the instance.
    Size 0 is an output among the n+m inputs.
    """
    for out in range(n + m):
        if represents([], out, n, m, mask):
            return [], out, 0
    g, o = rowcol_circuit(n, m, mask)
    if g and len(g) <= kmax and represents(g, o, n, m, mask):
        print(f"  rowcol size={len(g)}", file=sys.stderr)
        return g, o, len(g)
    order = [kmax] if not minimize else list(range(1, kmax + 1))
    found = None
    for k in order:
        cnf = encode(n, m, mask, k)
        status, model = run_sat(cnf, timeout=timeout)
        print(
            f"  k={k} vars={cnf.n} clauses={len(cnf.clauses)} {status}",
            file=sys.stderr,
        )
        if status == "sat":
            gates, output = decode(cnf, model, n, m, k)
            if not represents(gates, output, n, m, mask):
                raise RuntimeError("SAT model failed Python eval")
            found = (gates, output, k)
            if not minimize:
                return found
            continue
        if status == "unsat":
            if minimize:
                continue
            print(f"  unsat at kmax={kmax}; leave for refute", file=sys.stderr)
            return None
        print(f"  skip {status} at k={k}", file=sys.stderr)
        if not minimize:
            return None
    return found


def fmt_gate(op, ins):
    ins_s = ", ".join(str(i) for i in ins)
    return f"⟨.{op}, [{ins_s}]⟩"


def emit_lean(module, stmt, gates, output, kmax):
    ns = module
    gates_s = ", ".join(fmt_gate(op, ins) for op, ins in gates)
    # Shape of merged L_meta_19039.lean (Apache License 2.0): named witness,
    # FanInTwo by simp, size and Represents by decide +kernel.
    return f"""import PEqualNP.Defs

namespace {ns}

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

private def witness : Circuit :=
  ⟨[{gates_s}], {output}⟩

end {ns}

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents in
theorem {module} :
    {stmt} := by
  exact ⟨{ns}.witness,
    by simp [FanInTwo, {ns}.witness],
    by decide +kernel, by decide +kernel⟩
"""


# k=8 boundary L-meta-19051 (mask 4700) is left for last: SAT times out around 60s.
# L-meta-19209 (mask 316, k=6) and L-meta-19265 (mask 5887, k=5): sibling agent.
SKIP_IDS = {
    "L-meta-19051",
    "L-meta-19209",
    "L-meta-19265",
}

FAMILY = [
    {"id": "L-meta-19043", "n": 4, "m": 4, "mask": 5805, "k": 9},
    {"id": "L-meta-19634", "n": 5, "m": 5, "mask": 3315386, "k": 9},
    {"id": "L-meta-19517", "n": 5, "m": 5, "mask": 7876468, "k": 10},
    {"id": "L-meta-19518", "n": 5, "m": 5, "mask": 3320506, "k": 10},
    {"id": "L-meta-19519", "n": 5, "m": 5, "mask": 3675834, "k": 10},
    {"id": "L-meta-19524", "n": 5, "m": 5, "mask": 12063829, "k": 10},
    {"id": "L-meta-19527", "n": 5, "m": 5, "mask": 3187468, "k": 10},
    {"id": "L-meta-19528", "n": 5, "m": 5, "mask": 3195660, "k": 10},
    {"id": "L-meta-19607", "n": 5, "m": 5, "mask": 3258290, "k": 9},
    {"id": "L-meta-19638", "n": 5, "m": 5, "mask": 12059857, "k": 9},
    {"id": "L-meta-19673", "n": 5, "m": 5, "mask": 3249493, "k": 10},
    {"id": "L-meta-19677", "n": 5, "m": 5, "mask": 3320501, "k": 10},
    {"id": "L-meta-19679", "n": 5, "m": 5, "mask": 11700309, "k": 10},
    {"id": "L-meta-19696", "n": 5, "m": 5, "mask": 3937373, "k": 10},
    {"id": "L-meta-19703", "n": 5, "m": 5, "mask": 7865809, "k": 10},
    {"id": "L-meta-19053", "n": 4, "m": 4, "mask": 4702, "k": 8},
    {"id": "L-meta-19056", "n": 4, "m": 4, "mask": 4972, "k": 8},
    {"id": "L-meta-19078", "n": 4, "m": 4, "mask": 4975, "k": 7},
    {"id": "L-meta-19218", "n": 4, "m": 4, "mask": 4703, "k": 6},
    {"id": "L-meta-19051", "n": 4, "m": 4, "mask": 4700, "k": 8},
]


def statement_of(row):
    n, m, mask, k = row["n"], row["m"], row["mask"], row["k"]
    return (
        f"∃ C : PEqualNP.CircuitLowerBounds.Circuit, "
        f"PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ {k} ∧ "
        f"PEqualNP.Represents.Represents "
        f"(fun u v : Fin {n} => ({mask} : ℕ).testBit ({m} * u.val + v.val)) C"
    )


def module_of(gid):
    return "PEqualNP.Outside." + gid.replace("-", "_")


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--id", help="gap id, or all family members")
    ap.add_argument("--n", type=int)
    ap.add_argument("--m", type=int)
    ap.add_argument("--mask", type=int)
    ap.add_argument("--k", type=int)
    ap.add_argument("--out", type=Path)
    ap.add_argument("--timeout", type=int, default=60)
    ap.add_argument("--list", action="store_true")
    ap.add_argument("--include-skipped", action="store_true")
    args = ap.parse_args()

    if args.list:
        for row in FAMILY:
            print(f"{row['id']}\tn={row['n']}\tm={row['m']}\tmask={row['mask']}\tk={row['k']}")
        return 0

    rows = FAMILY
    if not args.id and not args.include_skipped:
        rows = [r for r in FAMILY if r["id"] not in SKIP_IDS]
    if args.id:
        rows = [r for r in FAMILY if r["id"] == args.id]
        if not rows:
            if args.n is None:
                raise SystemExit(f"unknown id {args.id} and no --n/--mask")
            rows = [{
                "id": args.id,
                "n": args.n,
                "m": args.m if args.m is not None else args.n,
                "mask": args.mask,
                "k": args.k,
            }]
    elif args.n is not None:
        rows = [{
            "id": args.id or "L-meta-local",
            "n": args.n,
            "m": args.m if args.m is not None else args.n,
            "mask": args.mask,
            "k": args.k,
        }]

    for row in rows:
        print(f"search {row['id']} n={row['n']} m={row['m']} mask={row['mask']} k≤{row['k']}",
              file=sys.stderr)
        found = find_circuit(row["n"], row["m"], row["mask"], row["k"], timeout=args.timeout)
        if found is None:
            print(f"NO CIRCUIT {row['id']}", file=sys.stderr)
            print(f"SKIP {row['id']}")
            continue
        gates, output, kused = found
        print(f"found {row['id']} size={kused} out={output} gates={gates}", file=sys.stderr)
        stmt = statement_of(row)
        text = emit_lean(module_of(row["id"]), stmt, gates, output, row["k"])
        out = args.out
        if out is None:
            out = Path(f"/tmp/pnp/{row['id'].replace('-', '_')}.lean")
        elif out.is_dir() or str(out).endswith("/"):
            out = Path(out) / f"{row['id'].replace('-', '_')}.lean"
        out.parent.mkdir(parents=True, exist_ok=True)
        # if generating a family and --out is a file, write beside it
        if len(rows) > 1 and args.out and args.out.suffix == ".lean":
            out = args.out.parent / f"{row['id'].replace('-', '_')}.lean"
        out.write_text(text)
        print(out)
    return 0


if __name__ == "__main__":
    sys.exit(main())
