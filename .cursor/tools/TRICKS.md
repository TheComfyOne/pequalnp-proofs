# Hunt playbook (TheComfyOne)

Read this file at the start of every run. After a push, add the pattern that
won it. This file lives on **fork `main` only** (`.cursor/` never goes on a
proof branch). Proof branches are still cut from `upstream/main` as
`git checkout -b <gap id> upstream/main`.

Push only via `.cursor/tools/new_steps.sh --push FILE`. Print
`PUSHED <gap id> (difficulty N/10)`. Do not open PRs from this agent.

## desk kind is the checker kind (do not negate find/check rows)

**Rule.** Intake / authoritative CI fetch
`https://pequalnp-desk.pequalnp.workers.dev/desk/row?gap=ID` and pass that
row to `outside-guard.mjs`. Kind is `g.kind`: missing or `check` → checker
kind **check**; only `g.kind === 'refute'` → checker kind **refute**. A desk
row with `find: true` has **no** `kind: refute` field, so CI judges it as
**check**. The file must prove the posted statement exactly. Local
`check-lean.mjs FILE STMT refute` saying ACCEPTED only means we passed
`refute` ourselves; CI does not take that argument from us.

`gen_twin.py` and `precheck.sh` must GET that row and use **its** kind.
`check-lean` is called with the desk kind. Refute-by-lower-bound (theorem
`¬ posted`) is emitted **only** when the desk posts the step as a
refutation. Otherwise only prove-by-witness / symmetry / special-case
templates that prove the posted statement. A check/find file whose theorem
is `¬ (posted)` is refused locally.

**Failed pattern (do not repeat).**

- `L-meta-25584` (3/10) PR #48313: REJECTED (statement). Desk `find: true`,
  statement is `∃ C` size ≤ 8 selector. File proved `¬` of that. Merged
  `L-meta-25534` really does show size ≤ 8 is false, but that is not a
  submit path for a find/check row.
- `L-meta-25609` (2/10) and `L-meta-25652` (2/10): same mistake (find rows,
  reverse of 25593 / 25645). Do not push more of these.

**What the repo actually allows when a find statement is false** (do not
use without telling the owner): see the note at the end of this file.
This hunt does not hold leases, so skip those rows and move on.

**How to spot a real refute twin.** Desk row `kind` is the string
`refute`, or the posted statement is already the negated twin the desk
listed (prove that text as **check**, do not wrap another `¬`). Titles
like “Find a … below the bound” with `find: true` are **check**, not
refute.

## desk `imports` is the CI whitelist

**Rule.** `outside-guard.mjs` allows only `import Mathlib`, `import Mathlib.*`,
and modules named in the desk row's `imports` field. A twin may reuse a
merged lemma **only** if that lemma's module is in the list (for example
`PEqualNP.Outside.L_meta_25534`). `gen_twin.py` emits Mathlib plus the
listed modules, nothing else. `precheck.sh` refuses any extra import.
`rank_gaps.py` marks unmatched lemmas `skip-not-listed` and does not
push them.

**Failed pattern (do not repeat).**

- `L-meta-25652` PR #48521: REFUSED before build.
  `import PEqualNP.Outside.L_meta_25645 is not allowed (only Mathlib and
  the modules the gap lists)`. The row listed only `PEqualNP.Defs`.
  Reverse-inequality against an unlisted merged file is not a twin.

**How to spot.** GET `/desk/row?gap=ID` and read `imports`. If the lemma
is not there, skip: do not import it, do not apply it. A row that lists
the lemma (25584 listed 25534; 25609 listed 25593) may import that
module; the desk **kind** still decides check vs refute.

## twin-pair sweep (templated)

**Trick.** Every loop, diff `upstream/main` since the last SHA and match
each newly merged lemma against open desk rows on the same
function/promise.

- Bound **at or above** a merged construction → **prove** the posted
  statement via that witness (also symmetry / special-case that prove S).
- Bound **below** a merged lower bound → **only** if the desk posts the
  step as a refutation (or the posted text is already `¬ S`). Otherwise
  count it as `skip-find-refute` and do not emit.

These are 2–3/10 when they are pushable. Rank pushable twins first, then
emit/build/push from a fixed template. Hand-edit only if the one lake
build fails.

**Tooling.**

```
.cursor/tools/rank_gaps.py --twins-only
.cursor/tools/gen_twin.py GAP LEMMA --push
.cursor/tools/gen_twin.py --from-rank --push
```

`gen_twin.py` writes `lean/PEqualNP/Outside/L_<gap>.lean`, GETs the desk
row, runs one `lake build` + `precheck` (+ `check-lean` with **desk**
kind), and pushes. Do not open a PR. `--from-rank` skips
`skip-find-refute` and `skip-not-listed`.

**Examples (valid).**

- Prove-by-witness / weaken size when a merged `∃` construction is ≤ the
  posted bound (same function). Checker kind `check`.
- Symmetry: posted `HasCircuitSize n f' k` where `f'` is `f` up to input
  permutation / graph relabeling and a merged witness has size ≤ k.
- Special-case: posted is a Fin-n instance of a merged general lemma, and
  the posted text is what we prove (instantiate, do not negate).
- Sibling `L-meta-25693` on main is a **desk-posted** refutation
  instantiate vs 25534, not a find row.

**How to spot.**

1. Run the twin sweep at the start of every loop (rank_gaps does this
   unless `--no-twins`). State is `.pnp/twin-last-sha`. Read the
   sweep-count table (rev-ineq vs skip-find-refute vs witness / symmetry /
   special).
2. Open rows whose last comparison is the reverse of a merged theorem
   **and** the desk kind is refute (or posted is already `¬`).
3. Open rows whose `imports` name a just-merged **witness** lemma.
4. Skip generator families. Skip find/check existence below a lower bound.
5. Skip a lemma whose module is not in the row's `imports`.

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
elaborated, so no +5). Do not spend the cap on find-refute dead-ends.

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
| find below a merged lb | `find: true` existence strictly smaller than a merged lower bound | not a PR; skip |

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

## sanctioned path for a false find/check row (do not use without telling)

Checked `.github/scripts/outside-guard.mjs`,
`.github/workflows/authoritative.yml`, `CONTRIBUTING.md`, `README.md`,
`tools/pnp.sh`, and join.txt.

There is **no** PR/checker path that submits `¬ S` for a find/check row.
`checkGap` maps missing/`check` kind to checker `check`, and a run of
kind `refute` on that row is refused (`as kind check`). Intake leaves
`KIND` empty; the workflow uses `${KIND:-check}`. `find: true` is not
read as refute. Reductions (`R_<gap>_<n>.lean`) are only judged when
`reductions: true` **and** the step is posted to be proved (kind check),
and the theorem’s conclusion is still S, not `¬ S`. `dead: []` on the
row is prior failed-attempt context, not a submit path.

join.txt: prove exactly the posted statement; **refute** kind means prove
the negated twin listed beside the unit (a separate desk-posted
refutation). Search empty range → `pnp.sh release exhausted`.

The only documented agent-facing way to say “this find statement is
false” is **not a proof PR**: if you hold a lease, `tools/pnp.sh release
<unit> statement_seems_false` (or `hypothesis_too_weak`). CONTRIBUTING.md
§5 and README say the same: do not change the statement; release it.
This hunt does not take leases, so that path is unused here. Do not
release, do not open a refute PR against a check row, and do not invent
a dead/refuted file kind.
