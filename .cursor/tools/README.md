# Hunt tools (TheComfyOne fork)

Scripts live here. The playbook is `TRICKS.md`. Shared desk/kind/import/PR/lease
helpers are `pnplib.py` (imported or invoked by the others). Never put `.cursor/`
on a proof branch. Push proofs only with `new_steps.sh --push`. Do not open PRs
from this agent.

## pnplib.py

Shared library: desk row fetch, checker kind, import whitelist, open-PR check,
`.pnp` lease JSON helpers. Not a hunt entry point.

```
python3 .cursor/tools/pnplib.py precheck "$ROOT" lean/PEqualNP/Outside/L_meta_XXXX.lean
python3 .cursor/tools/pnplib.py forbidden path/to/file.lean
```

## rank_gaps.py

Rank open desk rows (twin sweep first, then cheap lib/pcx/meta). Use at the
start of a hunt loop. Offline: pass cached JSON and `--no-fetch`.

```
python3 .cursor/tools/rank_gaps.py --gh --kind lib,pcx --max-diff 5
python3 .cursor/tools/rank_gaps.py --twins-only --no-fetch --status /tmp/status.json --gaps /tmp/gaps.json
```

## gen_twin.py

Emit a one-file twin proof from a merged lemma. Kind and imports come from the
desk row. Dry-run prints Lean and still enforces the whitelist.

```
python3 .cursor/tools/gen_twin.py L-meta-25652 L-meta-25645 --dry-run
python3 .cursor/tools/gen_twin.py --from-rank --limit 3
```

## gen_oneaside.py

SAT-search and emit one-a-side `Represents` family files (kissat). Leave this
family to the dedicated generator; do not hunt those rows by hand.

```
python3 .cursor/tools/gen_oneaside.py --help
```

## gen_mono6.py

Emit a Table 2 / mono6 prove file (kissat witness + search certificate) using
`.cursor/templates/Mono6Engine.lean`. For `Table 2:` rows, not `False:` orbits.

```
python3 .cursor/tools/gen_mono6.py --help
python3 .cursor/tools/gen_mono6.py --id L-meta-XXXX --hi HI --lo LO --out lean/PEqualNP/Outside/L_meta_XXXX.lean
```

## precheck.sh

Guard a one-file proof: no `inductive`/`sorry`/`axiom`/`native_decide`; desk
kind and import whitelist; exactly one Lean file vs `upstream/main`. Run before
every push.

```
.cursor/tools/precheck.sh lean/PEqualNP/Outside/L_meta_XXXX.lean
```

## new_steps.sh

Watch desk status for newly posted unclaimed ids, or `--push` a proof (precheck
then `git push -u origin HEAD`).

```
.cursor/tools/new_steps.sh --once
.cursor/tools/new_steps.sh --push lean/PEqualNP/Outside/L_meta_XXXX.lean
```

## new_proof.sh

Cut `<gap-id>` from `upstream/main` and paste a pruned CircuitKit skeleton.
Does not open a PR. Snapshot `/tmp/CircuitKit.lean` first; the kit is absent on
upstream.

```
.cursor/tools/new_proof.sh L-meta-XXXX --json .pnp/L-meta-XXXX.json --skip-check
```

## open_steps.sh

List desk gaps with no open or merged PR title matching the id, easiest first.

```
.cursor/tools/open_steps.sh --limit 20 --status /tmp/status.json
```

## templates

`.cursor/templates/SmallCircuit.lean` — `decide` sketch for a tiny fan-in-two
circuit (local only; not a desk file).

`.cursor/templates/Mono6Engine.lean` — engine pasted by `gen_mono6.py`.

```
cd lean && lake env lean ../.cursor/templates/SmallCircuit.lean
```
