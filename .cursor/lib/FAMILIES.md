# willakone step families

Source: `gh pr list -R open-goat/pequalnp-proofs --author willakone --state merged`
(and closed-unmerged), desk titles from `https://pequalnp.com/desk/status`,
and the Lean files those PRs added. Times are UTC on 2026-11-24/25.

## How fast they submit

willakone does not wait. Related gap ids land as a **burst**:

| Burst | Window | PRs | Delay created→merged |
| --- | --- | --- | --- |
| t6 edge-function ≥ 8 (`L-meta-7269`–`7309`) | 2026-11-25 03:21–03:31 | 12 merged (`#11937`–`#11983`) | 30–45 min (CI), opened ~10 min apart |
| `Represents` + `Monotone2` + size (`L-meta-5437`–`5443`) | 2026-11-25 00:55–00:57 | 5 merged in 2 min (`#11125`–`#11150`) | ~35–50 min |
| `RepSizeAtMost` 4×4 bitmasks (`L-meta-5463`–`5599`) | 2026-11-25 01:32–02:09 | 6 merged | ~15–100 min |
| Tiny `IsAO2` / `ReadTwice` circuits (`L-meta-3728`–`3738`) | 2026-11-24 16:57 | 4 merged in one second (`#7834`–`#7867`) | ~2–3 h (queue) |
| Earlier incidence / covering (`L-meta-2393`–`2586`) | 2026-11-24 08:30–09:07 | many, some 6–7k lines | hours of CI |

The t6 family is the smoking gun for a **pre-built kit**: twelve different
6-vertex graphs, same 2316-line library, only the edge-list encoding and
the `T_cert` frontier change. Desk titles for the still-open siblings
(`L-meta-7270`, `7281`, `7286`, `7308`, `7309`, …) are of the form
`Graph t6-… on 6 vertices, k edges: every circuit of AND, OR and NOT
gates of fan-in two for its edge function has at least 8 gates`. Those
ids were claimed within minutes of each other.

Closed-unmerged in the same windows (`#11936` L-meta-6055, `#11480`
L-meta-5603, `#11471` L-meta-5602, `#11422` L-meta-5606, `#11294`
L-meta-5465, `#11273` L-meta-5460, `#11146` L-meta-5444, `#11134`
L-meta-5439) are the same families with a rejected or superseded file,
not a different pattern.

## Families and proof patterns

### 1. Fixed 6-vertex edge function, `HasCircuitSize ≥ 8` (kit family, `BT` as a list of keys)

- **Wins:** `L-meta-7269`, `7270`, `7278`, `7281`, `7283`, `7284`, `7285`,
  `7286`, `7292`, `7299`, `7308`, `7309` (PRs `#11937`, `#11956`, `#11938`,
  `#11957`, `#11960`, `#11963`, `#11951`, `#11939`, `#11967`, `#11973`,
  `#11983`, `#11953`).
- **Desk title shape:** `Graph t6-<hex> on 6 vertices, k edges: every
  circuit of AND, OR and NOT gates of fan-in two for its edge function
  has at least 8 gates`.
- **Pattern:** paste CircuitKit; encode the edge function as a 64-bit
  truth table (`encL` / `Y_`); close a `BT` (`List (List ℕ)` of failing
  `NatRun` keys, built with `BT.nd` / `BT.lf` or a list literal) under
  `next` / `stepOK`; finish with `lb_cert … 7 8`. `decide +kernel` only
  on the certificate, not on the circuit search.
- **Kit parts:** all of them, especially Run/NatRun and the frontier
  certificate.

### 2. Concrete `Monotone2` circuit `Represents` a 4×4 bitmask

- **Wins:** `L-meta-5437`, `5438`, `5440`, `5441`, `5443` (~15 lines).
- **Pattern:** name the circuit as a `Circuit` record; split
  `Monotone2 ∧ size = n ∧ Represents A C`; `simp [Monotone2]` plus
  `decide +kernel`. No search.
- **Kit parts:** `monotone2_of_and_or`, `size_eq_len`, `eval_eq` /
  `wiresFrom`. Re-proved here for `L-meta-5443` at the bottom of
  `CircuitKit.lean`.

### 3. `RepSizeAtMost A k ∧ ¬ RepSizeAtMost A (k-1)` on 4×4 bitmasks

- **Wins:** `L-meta-5464` (k=3), `5507` (k=2), `5599` (k=3), `5463` /
  `5471` (k=4), `5593` (k=5).
- **Pattern:** bitmask pool `stepC` / `reach` (AND/OR of 16-bit
  slices); `decide +kernel` that a target is unreachable in `k-1`
  steps; exhibit a `k`-gate OR/OR/AND circuit for the upper bound.
- **Kit parts:** evaluation + monotone AND/OR. The pool search is a
  smaller cousin of `NatRun`, not the t6 `BT` certificate.

### 4. Relabel / FanInTwo size-preserving rewrite

- **Wins:** `L-meta-4934` (permute 10 inputs, size ≤ 18 stays FanInTwo).
- **Pattern:** `reGate` / `rho` input map; prove `wires` commute with
  the relabeling.
- **Kit parts:** `relabel`, `relabel_size`, `wmap` (same idea as the
  167-line file, unified in the kit).

### 5. Monotone circuit monotonicity (`IsAO2`)

- **Wins:** `L-meta-5174`.
- **Pattern:** if `x ≤ y` pointwise and `IsAO2`, the circuit cannot
  go from true to false. Local `step` / `foldl` lemmas.
- **Kit parts:** `wiresFrom` + AND/OR evaluation (`gateOp_eval_mono`
  in the 2416-style files; kit uses `Agree` / `simplify_sound`).

### 6. Incidence / covering / C4-free combinatorics

- **Wins:** `L-meta-3487` (Zarankiewicz-style 4-cycle-free bound),
  `L-meta-3756` (`IsAO2` + `graphFun`), `L-meta-4837` (cycle / covering
  number vs circuit), `L-meta-2416` (Singer-difference covering on
  `Fin 13` with a monotone circuit).
- **Pattern:** Mathlib `Finset` / `SimpleGraph` plus a small
  `wiresFrom` monotonicity lemma; not the t6 certificate.
- **Kit parts:** evaluation and monotone lemmas only.

### 7. Tiny decide-only circuits (`IsAO2`, `ReadTwiceAt`)

- **Wins:** `L-meta-3728`, `3730`, `3734`, `3738` (14–31 lines).
- **Pattern:** substitute the concrete circuit, `decide` the
  `IsAO2` / size / `circuitFun` / `ReadTwiceAt` conjuncts.
- **Kit parts:** optional; `decide` is enough. Glue lemmas still
  document the `Circuit` encoding.

## What to grab next

Open t6 siblings on the desk (same title shape, no merged PR yet) are
the intended use of CircuitKit + `lb_cert`. The 4×4 `RepSizeAtMost` and
`Represents` rows are the intended use of Section 1 only (no `BT`).
