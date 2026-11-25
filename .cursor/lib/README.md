# CircuitKit

Pasteable Lean helpers extracted from willakone's merged proofs in
`open-goat/pequalnp-proofs` (the identical ~2316-line prefix of
`L_meta_7269`–`L_meta_7309`, plus a few glue lemmas). Proof PRs may add
exactly one file and may import only `Mathlib`, Mathlib modules, and
`gap.imports`, so this kit is **not** a lake module: copy the block
between `-- CIRCUITKIT BEGIN` and `-- CIRCUITKIT END` into
`namespace PEqualNP.Outside.<id>_aux`.

Compile the library itself (does not go in a PR):

```
cd lean && lake env lean ../.cursor/lib/CircuitKit.lean
```

Scaffold a one-file proof branch from `upstream/main`:

```
.cursor/tools/new_proof.sh L-meta-XXXX
```

## What the kit covers

| Part | Names | Step families |
| --- | --- | --- |
| Evaluation | `wiresFrom`, `wiresFrom_append`, `wiresFrom_prefix`, `length_wiresFrom`, `getD_wiresFrom`, `wires_eq`, `eval_eq` | Any concrete circuit, `circuitFun`, `HasCircuitSize`, `Represents` |
| Supports / sensitivity | `gateSupp`, `suppsFrom`, `Agree`, `Cnt`, `dep_lower_set` | Lower bounds from input dependence; fan-in-two size vs sensitive set |
| Simplification | `normGate`, `simpAnd` / `simpOr` / `simpNot`, `simplify`, `CleanG`, `CleanL` | Rewrite AND/OR/NOT of fan-in ≤ 2; drop constants and copies |
| Gate elimination | `elim`, `elimStep`, `Inv`, `gate_elim_one`, `gate_elim_two`, `gate_elim_at`, `one_gate_at` | Restrict a bit, drop unused inputs, save one or two gates |
| Relabeling | `wmap`, `relGate`, `relabel`, `relabel_size` | Permute / inject inputs while preserving size |
| Monotone AND/OR | `Ok`, `NOk`, `monotone2_of_and_or`, `exists_clean_m`, `run_live_m`, `exists_run_m` | `Monotone2` / NOT-free `HasCircuitSize`; g2x2/g2x3/t6 edge functions |
| Run / Reach | `Run`, `Reach`, `Live`, `exists_run`, `NatRun`, `encL` | Encode a circuit as a pool of bitmasks; search for a size witness |
| Frontier certificate | `BT`, `stepOK`, `lb_cert`, `via`, `prsOK`, `actL`, `symOK` | Certified unsat of `HasCircuitSize n f s` (willakone t6-*-at-least-8) |

Instance-specific blobs (`L_`, `M_`, `Y_`, `T_cert`, `K_0`…) are **not** in
the kit. Those are per-graph search certificates; paste the kit, then add
your own `L_` / `T_cert` and call `lb_cert`.

`BT` is `List (List ℕ)`: inorder flattening of the old binary tree (`BT.lf = []`,
`BT.nd l k r = l ++ k :: r`, `BT.mem` is `List.any` over `leqL`). No new
data type is declared. `.cursor/tools/new_proof.sh` pastes only the decls a
statement needs when that is obvious, and refuses to emit a new data type.
`.cursor/tools/precheck.sh` rejects a proof file that contains that word,
`sorry`, `axiom`, or `native_decide`, or a branch with more than one Lean file.

## Local check

The file after `-- CIRCUITKIT END` re-proves willakone's merged
`L-meta-5443` (a 7-gate `Monotone2` circuit that `Represents` bitmask
15839 on `Fin 4 × Fin 4`) using `monotone2_of_and_or`, `size_eq_len`,
`eval_eq`, and `decide +kernel`. That theorem is not for pasting.
`.cursor/tools/new_proof.sh --kit-use monotone2_of_and_or,size_eq_len,eval_eq`
keeps those four decls plus `wiresFrom`.
