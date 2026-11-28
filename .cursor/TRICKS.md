# Fork-local tricks

Notes from the 2026-11-28 mono6 / Table 2 hunt. Not for proof PRs.

## Table 2 / mono6-screened-orbits generator

Working generator: `.cursor/tools/gen_mono6.py`

Engine template (generic search proofs, copied from merged L-meta-40217):
`.cursor/templates/Mono6Engine.lean`

Local e2e (2026-11-28), no desk lease:

| Unit | table | gen | lake build | check-lean | file |
| --- | --- | --- | --- | --- | --- |
| L-meta-40217 (PR 48392 merged) | 4276808426 * 2^32 + 4272482952 | 10.0s (SAT 9.8s) | 101s | ACCEPTED 121s | 233990 B |
| L-meta-40417 (PR 48185 merged) | 4276809448 * 2^32 + 4209683104 | 21.7s (SAT 21.5s) | 102s | ACCEPTED 115s | 237209 B |

Both files: import only `PEqualNP.Defs`; no `sorry` / `axiom` / `native_decide` / `inductive` / `macro` / `notation` / quotes.

### Usage

```
python3 .cursor/tools/gen_mono6.py \
    --id L-meta-XXXX --hi HI --lo LO \
    --out lean/PEqualNP/Outside/L_meta_XXXX.lean
```

Or parse HI/LO from a merged Lean file:

```
python3 .cursor/tools/gen_mono6.py --from-lean /path/to/L_meta_40217.lean --out FILE
```

Then, on a proof branch cut from `upstream/main`:

```
cd lean && lake build PEqualNP.Outside.L_meta_XXXX
node tools/check-lean.mjs lean/PEqualNP/Outside/L_meta_XXXX.lean STATEMENT check
.cursor/tools/precheck.sh lean/PEqualNP/Outside/L_meta_XXXX.lean
.cursor/tools/new_steps.sh --push lean/PEqualNP/Outside/L_meta_XXXX.lean
```

Needs `kissat` on PATH (CNF for a 10-gate AND/OR witness). SAT is 10–90s;
`--sat-timeout` defaults to 90. Search dump is ~0.15s. Lean `decide +kernel`
on the certificate is the long step (~100s).

### What it emits

Same shape as grayboywilliams L-meta-40217 / 40417:

1. Packed `BitVec 256` rows (low 128 columns = f=1, high 128 = f=0).
   Hamming-distance-1 pairs so only the full 6-input set has `cuts = -1`.
2. 10-gate AND/OR `witness` from kissat.
3. Python replica of `children` / `level0` dumps `bkA` (2-step frontier)
   and `bkB` (one more step), interned as `z0..zN`.
4. `search_false_C2` with `dp=0`, `J=5`, `d=2`, `g=8`, `nb=256`.
5. `solve`: a NOT forces `binaryCost > 8` hence `size ≥ 10`; the witness
   is no larger. A NOT-free circuit is already monotone.

Do not put `.cursor/` on a proof PR. Branch from `upstream/main`.

## Desk (still true)

- `GET /desk/next?proofOf=` is ignored. `kind=prove` prefers high-point
  8-vertex one-NOT units over Table 2 (~30 pts).
- Older mono6 refute twins sit in `twin_primary_open`.
- Capacity 4 held; hunter asked max 2. `out_of_time` / `other` is not
  re-offered for an hour.

## 8-vertex one-NOT prove (not this generator)

Title: `At fan-in two, one NOT gate saves nothing on edges …`.
psosnin pattern: 13–14 gate AND/OR witness plus a 6-input cofactor lower
bound. A 15-gate constructive monotone circuit is one gate too big if the
cofactor only gives binary lower 13.
