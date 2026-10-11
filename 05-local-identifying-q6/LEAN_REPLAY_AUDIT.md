# Independent Lean replay audit

## Current status

**PASS: source trust boundary, exact data linkage, first full kernel replay, and independently audited clean rebuild.** All 257 modules compiled from the fresh source snapshot, including all 61,970 RUP proof steps and the unconditional final theorem. Its only axioms are the standard `propext`, `Classical.choice`, and `Quot.sound`.

## Inspected implementation

`lean/RUPReplay.lean` reads JSON steps and constructs explicit propositions and proof terms. Each generated theorem has type

`forall p : Nat -> Prop, Q6RUPPath.Inputs p -> clause p target`.

Positive integers denote `p n`; negative integers denote `Not (p n)`; a nonempty clause is a right-associated disjunction, and the empty clause is `False`. Input clause references use the corresponding structure projection from `Inputs`; derived references use already declared `Q6RUPPath.c<ID>` theorems. Negating a target clause supplies negated literals, and propagation uses explicit `Or.elim`, contradiction, and local let-bound proofs. Classical double-negation elimination is supplied by the standard `Classical.byContradiction` theorem.

Every resulting expression is submitted as `addDecl (.thmDecl ...)`, not installed as an axiom. The producer can supply erroneous JSON, mismatch a reference's clause body, or construct an ill-typed term; these mistakes cannot silently establish the claimed theorem because the emitted expression still must pass the kernel's type check against its declared proposition. In particular, JSON parsing and the Python generator need not be trusted for proof soundness. The same applies to propagation bookkeeping and fallback branches in the term builder. The replay source never uses a kernel bypass, environment injection, custom axiom, `sorry`, `native_decide`, or a Boolean oracle theorem.

I inspected the bundled Lean 4.24.0 source at `Lean/AddDecl.lean` and `Lean/Environment.lean`: `addDecl` submits the declaration for kernel checking; `debug.skipKernelTC` defaults to false. No project source enables it. The build command uses `-DElab.async=false`, so theorem checking is synchronous. Increasing recursion/heartbeat limits does not disable type checking. Partial metaprogram functions are expression producers, not logical axioms.

## Exact data and semantic linkage

`independent_replay_data_check.py` checks, independently of the generator:

1. All 1,623 input clause propositions in `lean/RUPPath/Inputs.lean` agree literally with `exclude13-path.cnf`, including signs, order, and variable indices.
2. All 61,970 replay steps across 194 JSON modules (after audited rebatching) agree with the independently checked LRAT file, including target literals, active referenced clauses, and each hint's expanded literal array.
3. The last theorem ID is 92061 and its target is the empty clause.
4. `FullTheorem.lean` supplies precisely `Q6RUPPath.c92061` to `minimum_fourteen_of_path_refutation`.

The recorded engine source SHA-256 is `fbae6fdc20174b8436812c4298253bbc4066628af5f6777d84081598239a6335`. The check results are saved in `independent_replay_data_results.json`.

The mathematical interface in `PathSemantics.lean` has the correct direction: it extends any normalized size-at-most-13 code to an `Inputs` assignment; uses the path normalization theorem; then combines the contradiction with the separately checked 14-witness. The final theorem quantifies over every Boolean-valued code on `Fin 64`, with domination of all vertices and separation of every adjacent pair, including code vertices. Cardinality counts selected vertices in `List.finRange 64`. This matches the audited literature definition.

## Completion requirements (now satisfied)

A successful source inspection or partial chunk build is not a complete kernel proof. Completion requires all 194 replay modules and `FullTheorem.lean` to compile successfully, with the final theorem's printed axiom list containing only the expected standard axioms. A clean independent rebuild should use separately generated output files, pinned source/JSON inputs, and no reused project `.olean` files.

The initial checkpoint script hashed the current module, its JSON, and engine source, but not the full dependency closure. I reported this reproducibility limitation to the author, who is binding the build to a global source/JSON manifest. It does not invalidate an unchanged run; it means stale cached outputs cannot by themselves certify a modified dependency graph.

The remaining trust boundary is the ordinary Lean kernel/toolchain and its trusted bundled foundation. The exact certificate checks and source audit do not prove the compiler or operating system correct, and do not settle novelty.

## Negative kernel-path test

In isolated `lean-negative-test/`, I copied only the first replay step and changed its first hint reference from clause 257 (`p 1`) to clause 258 (`p 2`), while retaining the claimed literal array `[1]`. With the actual replay engine and synchronous checking, Lean exited 1 and reported `(kernel) let-declaration type mismatch 'k0'`. This exercises rejection by the kernel itself rather than merely by the JSON parser or propagation prechecks. The exact corrupted input, module, and rejection log are saved there; no pinned proof inputs were changed.

## First full kernel pass

I independently inspected `full-first-result.json` and `full-first-check.log`: the build exited 0, and `LocalIdentifyingQ6.minimum_local_identifying_Q6` reports exactly `[propext, Classical.choice, Quot.sound]`. All 194 module build records report exit 0, and each recorded module/source/JSON/engine digest matches the current files. Every entry of `RUP_FAST_SOURCE_MANIFEST.json` matches its file, and its SHA-256 is exactly the digest named in the full-result record (`3496f5ffe42944406e95e2383538248430b14745632ac127a874d11e6bf7990f`). The final theorem statement and semantic definitions are as audited above.

This validates the reported first pass and its pinned source identity. It is not a claim that imported `.olean` files were independently regenerated during that first invocation. The separate clean build was run by the formalization reviewer; its harness was independently inspected and accepts only a previously nonexistent destination, snapshots source and JSON dependencies without copying project `.olean` files, and uses only the clean destination on `LEAN_PATH` (plus the standard toolchain libraries).

## Completed clean-build release gate

Independently checked `lean-clean-check/status.json`, `check.log`, `source-manifest.json`, `build-order.json`, and `build-results.json`. The build completed 257 of 257 modules in 2,127.903920650482 seconds. All module exit codes are zero. The 194 replay log entries total exactly 61,970 RUP steps, and the final theorem prints exactly the three standard axioms stated above. No errors or sorry messages appear in the log.

Every one of the 451 snapshot source/JSON files was rehashed and compared both to the frozen manifest and to the current project source. All match. Every one of the 257 generated `.olean` files was rehashed against its build record. All match. The source-manifest SHA-256 is `0db2b23683bd596b65975841a75677ba05dc92fafba7f87fe03b40e87ed0c566`. The audit result is saved in `independent_clean_build_results.json`.

I also compared all 451 staged `release-candidate/lean` source/JSON files to that exact clean-build manifest: no missing or changed files. Thus the staged mathematical and replay sources agree with the clean-verified source snapshot. Documentation and packaging may still be refreshed without changing those proof inputs; archive checksums should be regenerated after such refreshes. This is a mathematical/proof reproducibility gate, not a novelty or publication authorization decision.
