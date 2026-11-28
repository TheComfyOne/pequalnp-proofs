# Hunt playbook (TheComfyOne)

Read this file at the start of every run. After a push, add the pattern that
won it. This file lives on **fork `main` only** (`.cursor/` never goes on a
proof branch). Proof branches are still cut from `upstream/main` as
`git checkout -b <gap id> upstream/main`.

Push only via `.cursor/tools/new_steps.sh --push FILE`. Print
`PUSHED <gap id> (difficulty N/10)`. Do not open PRs from this agent.

## refute-by-merged-lower-bound

**Trick.** If an open row asks for a circuit (or selector, or Res length)
strictly smaller than a bound already proved by a merged lemma, **refute**
the posted existence by applying that lemma. Do not search for a circuit.

**Examples.**

- `L-meta-25584` (3/10): eight-gate monotone 5-row selector. Merged
  `L-meta-25534` gives `2 * n - 1 ≤ C.size` (here 9) on the same one-hot
  promise, so `size ≤ 8` is false. Encode pairs as `Fin 25`, apply, `omega`
  / `decide` the numeric clash. Checker kind `refute`.
- `L-meta-25609` (2/10): “find a FanInTwo circuit below the sparse
  C4-free bound.” Merged `L-meta-25593` is exactly the opposite inequality
  `(48d+2)(n+m) ≤ (48d+1) C.size + 150d + 5`. `rintro` the exists, apply
  25593, `not_le_of_gt`. Same hyps (degree window, no 4-cycle, FanInTwo,
  Represents). Checker kind `refute`.
- Sibling template: `L-meta-25693` already on main (n=4, size ≤ 6 vs 25534’s 7).

**How to spot.**

1. Open existence rows whose `imports` name an Outside lemma
   (`L_meta_25534`, `L_meta_25593`, …).
2. Merged theorems of the shape `hyps → k ≤ C.size` / `RepSizeAtMost A s → k ≤ s`
   / a linear inequality on `C.size`. Then desk rows that claim `C.size ≤ k-1`
   or the strict opposite inequality under the same hyps.
3. Concrete lower bounds in the tree: 25534 (`2n-1` selectors), 25529
   (`2n` on `RepSizeAtMost` with a triple), 25593 (sparse C4-free FanInTwo),
   18006 (5×5 crown ≥ 15), 7626 (crown `3n-3`), 29939 (crown n≥7 `3n+1`),
   25408 (`2n-1` 2-color), 9442 (Fano AO2 ≥ 27), 118 (`¬` PHP 4 3 LinRefutation
   length ≤ 47). Match open `∃` claims strictly below those numbers.
4. Titles like “find an N-gate …” / “below the … bound” where N is one less
   than a lemma already on `upstream/main`.

If the posted statement is already `¬ (∃ …)` and that `¬` is exactly the
lemma, prove it as `check`, not `refute`.

## twin-pair sweep (templated)

**Trick.** Every loop, diff `upstream/main` since the last SHA and match
each newly merged lemma (ours or anyone’s) against open desk rows on the
same function/promise. A too-small bound is a **refute** via the
lower-bound lemma; a bound at or above a merged construction is a
**prove** via that witness. These are 2–3/10 and minutes each — rank
them first, then emit/build/push from a fixed template. Hand-edit only
if the one lake build fails.

**Tooling.**

```
.cursor/tools/rank_gaps.py --twins-only
.cursor/tools/gen_twin.py GAP LEMMA --push
.cursor/tools/gen_twin.py --from-rank --push
```

`gen_twin.py` writes `lean/PEqualNP/Outside/L_<gap>.lean` from one of two
templates (refute-by-lower-bound or prove-by-witness), runs one
`lake build` + `precheck` (+ `check-lean`), and pushes. Do not open a PR.

**Examples.**

- `L-meta-25609` (2/10) via `L-meta-25593` — reverse inequality, refute template.
- `L-meta-25652` (2/10) via `L-meta-25645` — same template, NOT-charging bound.
- `L-meta-25584` (3/10) via `L-meta-25534` — instantiate `n=5` (template may
  fail; hand-edit the Fin-25 encoding).
- `L-meta-25693` already on main — instantiate `n=4` vs 25534’s `2n-1`.

**How to spot.**

1. Run the twin sweep at the start of every loop (rank_gaps does this
   unless `--no-twins`). State is `.pnp/twin-last-sha`.
2. Open existence whose last comparison is the reverse of a merged
   theorem (`A ≤ B` vs `B < A`) under the same hyps.
3. Open rows whose `imports` name a just-merged Outside lemma.
4. Titles “Find a … below/beating the bound”. Skip generator families.

## push-anyway vs a rival PR under 15 min old

**Trick.** Skip a gap at **start** if anyone already has an open GitHub PR
(`gh pr list -R open-goat/pequalnp-proofs --search '<gap id> in:title' --state open`).
If the proof **already builds** and a rival PR appeared in the last 15
minutes, push anyway.

**Example.** `L-lib-1119` (5/10): we pushed after odinfree; the desk still
merged ours. Speed on newest lib/pcx beats a 4-minute lead.

**How to spot.** Re-run the gh search right before `--push`. If the rival’s
`createdAt` is `< 15 min` and `lake build` + `check-lean` already passed,
push. If the rival is older than 15 min, drop.

## scratch-file iteration and the 15+5 cap

**Trick.** Hard cap **15 min or 3 failed `lake build`s**, whichever first.
Iterate the hard lemma in `lean/scratch.lean` with `cd lean && lake env lean scratch.lean`.
Only run full `lake build <module>` + `precheck` / `check-lean` once the
scratch file elaborates. If at 15 min the scratch file elaborates and the
last full build failed on **one small local error**, take up to **5 extra
minutes**. At 20 min, hard drop.

**Example.** Used on the 1142 Horn/RIP gadget (dropped: scratch never
elaborated, so no +5). Contrast 25584/25609: lemma apply, one scratch
compile, one build, push well under 15 min.

**How to spot.** If the first 5 minutes do not produce a clear lemma, SAT
witness, or `decide` circuit, skip. Do not rebuild Mathlib-scale modules
on every edit.

## families to skip (sibling generator / farm)

Do not take these; a dedicated generator already farms them. `rank_gaps.py`
`SKIP_TITLE` covers several; also skip by id/title even if the ranker
misses them.

| Family | How to spot | Notes |
| --- | --- | --- |
| one-NOT leftovers | title “one not saves nothing”; `one NOT` / leftover NOT on a mask | generator |
| mono6 orbit twins | “monotone six-input f with table `N * 2^32 + M`”; `HasCircuitSize 6` + giant `testBit` word | thousands of orbit copies |
| packed-good 25842–25851 | “counted gates for four row masks …”; ids `L-meta-25842`–`25851` | skip the whole farm |
| one-a-side | title “one-a-side” / “one a side”; `RepSizeAtMost` on a small mask with that promise in the title | `gen_oneaside.py` |
| table 2 | title “table 2” | generator |
| 7-cycle 10-gate | “7-cycle edges” | farm |
| two-lit H-on-6 | “two-lit function of the graph H on 6 points with mask …” | family |
| L-pcx-189 | Res(2) PHP 4/3 upper bound | tight 7/10, drop |

Also skip: NestedCover / ReadsBack research, TM2, Gaussian/Poisson, Walsh/CRT
reconstruction libs, PHP **lower** bounds (`no refutation has at most …`),
and conjectures.

## other operating notes

- Ranker: `.cursor/tools/rank_gaps.py --gh --kind lib,pcx|meta --max-diff 5`.
  Twin sweep runs first (`--twins-only` to print just those). Prefer
  **cheap finite / `decide` / small explicit instances** over newest
  rows when the newest look research-scale. Re-check meta/pcx scored 1–5.
- Identity: `TheComfyOne` / `210307828+TheComfyOne@users.noreply.github.com`
  as both author and committer.
- Snapshot `/tmp/CircuitKit.lean` before any `new_proof.sh` checkout; kit
  is missing on `upstream/main`.
- `cadical` has no `--time`; use `-t N`. Do not pass a second filename
  (that writes a binary proof). `decide` is allowed; `native_decide` is not.
- Desk `pr_open` lags GitHub; always `gh pr list` at start and before push.
- `check-lean` may sit on a stale `lean/.lake/check.lock` (mkdir lock,
  60 min stale). If the checker stays on `started` with no lake child,
  remove the empty lock dir and rerun.
- No leases / no `/desk/next`. No tokens in logs. One Lean file per proof
  branch.
