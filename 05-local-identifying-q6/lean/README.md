# Lean formalization: local identifying codes in Q6

## Verified result

**The minimum cardinality of a local identifying code in Q6 is 14.**

`FullTheorem.lean` proves the unconditional theorem
`LocalIdentifyingQ6.minimum_local_identifying_Q6`:

* a local identifying code with cardinality 14 exists;
* every local identifying code has cardinality at least 14.

Both the initial build and a separate clean rebuild passed. The clean rebuild
checked 257 modules and all 61,970 RUP proof steps from a snapshot of 451 pinned
source/JSON files, without reusing any pre-existing project `.olean` files.
It completed in 2,127.9 seconds. The final axiom report is exactly:
`[propext, Classical.choice, Quot.sound]`.

Evidence is recorded in `../full-first-result.json`, `../full-first-check.log`,
and `../lean-clean-check/{status.json,check.log,source-manifest.json,build-results.json}`.

The intermediate theorem `PathSemantics.minimum_fourteen_of_path_refutation`
is conditional on the concrete propositional refutation. The final theorem
discharges that premise using the kernel-checked `Q6RUPPath.c92061`.

## Definition and witness

Vertices are `Fin 64`, interpreted as six binary coordinates. Adjacency means
that XOR is one of 1,2,4,8,16,32. Every closed neighborhood meets the code, and
adjacent vertices have different intersections of their closed neighborhoods
with the code. This includes adjacent pairs whose endpoints are codewords.
No separation requirement is imposed on nonadjacent pairs.

The checked size-14 witness is:
0,4,15,23,26,29,31,33,35,36,41,49,58,62.

## Modules

* `LocalIdentifyingQ6`: mathematical definitions, domination/edge-hit
  equivalence, witness validity and cardinality.
* `GraphEncoding`: explicit 64 domination and 192 unordered-edge clauses,
  with both directions of the encoding equivalence.
* `Translation`: XOR translation preserves the graph, code validity and size;
  normalization to include vertex 0.
* `PathNormalization`: a local identifying code of size ≤13 contains a
  codeword adjacent to two distinct other codewords. The argument includes
  the independent-code lower bound 16.
* `CubePathAutomorphism`, `NormalizeSmallCode`: translation and coordinate
  permutation normalize these three codewords to 0,1,2, preserving size.
* `CardinalityEncoding`, `CardinalityBridge`: Boolean prefix counts extend
  every ≤13 input to the exact sequential-counter clauses, and the prefix
  count equals the mathematical cardinality.
* `GraphRows`, `GraphClauseData`: 256 individual kernel-checked equalities
  connecting mathematical graph clauses to explicit SAT clauses.
* `PathInputs`: direct construction of every one of the 1623 propositional
  input-clause fields. This avoids reducing a giant full-CNF equality.
* `PathSemantics`: complete mathematical reduction to the concrete refutation.
* `RUPPath.Inputs`: the explicit propositional input-clause structures.
* `RUPReplay`, `RUPPathFast`: a proof-producing metaprogram and segmented
  replay commands. Each generated theorem is submitted to the Lean kernel.
  The older `RUPPath` source-expanded replay is retained as an alternative.
* `FullTheorem`: the checked unconditional final theorem.

## Reproduction

Use Lean 4.24.0, official release commit
797c613eb9b6d4ec95db23e3e00af9ac6657f24b. Only Lean and its bundled Std library
are required. No mathlib dependency is used.

`LEAN=/path/to/lean ./check_mathematics.sh` checks the mathematical modules in
small processes. The default path refers to the official toolchain installed
in this workspace. The Lake target currently checks the initial definitions
and witness only; it is not a substitute for this full check script.

The optimized RUP build is controlled by `../build_rup_fast.py`; its progress,
per-file hashes, timings and memory records are persisted beside that script.
To check the final theorem after rebuilding the replay, from this directory run:

```
LEAN_PATH=.lake/build/lib/lean:. /path/to/lean -j1 FullTheorem.lean
```

A successful final run must print the theorem's axiom dependencies.
`../verify_lean_clean.py` takes a hashed snapshot
of the final source/JSON dependency closure and recompiles it in a separate
output directory without importing any pre-existing project `.olean` files.

## Trust boundary

The checked mathematics uses kernel reduction (`decide` / `decide +kernel`),
not `native_decide`. `#print axioms` for the final unconditional theorem
reports only the standard `propext`, `Classical.choice`, and `Quot.sound`.
No `sorry`, newly assumed axiom, `Lean.ofReduceBool`, floating-point optimization
claim, or SAT solver soundness assumption is used.

The solver, Python generators, and any metaprogram that constructs proof terms
are untrusted. Their output must pass the ordinary Lean kernel. Independent
Python and C LRAT checks corroborate UNSAT but do not replace the Lean check.

The `experiments/` directory preserves abandoned monolithic attempts that hit
memory limits. These are not imports of the checked mathematics or final proof.
