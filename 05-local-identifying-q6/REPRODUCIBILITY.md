# Minimum local identifying code in the six-dimensional binary cube

## Verification status

Both the first complete Lean kernel build and an independent clean-source rebuild establish M^L(6) = 14. The clean run recompiled all 257 modules from the pinned 451-file source/JSON snapshot, reusing no project `.olean` files, and checked all 61,970 RUP steps plus the unconditional theorem `LocalIdentifyingQ6.minimum_local_identifying_Q6`. The final theorem depends only on `propext`, `Classical.choice`, and `Quot.sound`. The clean build completed in 2127.9 seconds with peak per-process RSS 4038.7 MiB. See `verification/clean/status.json`, `verification/clean/build-results.json`, and `verification/clean/check.log` in the release package.

## Definition and primary proof

Vertices are integers 0,...,63 with six-bit binary labels. Two vertices are adjacent exactly when their XOR has one set bit. The closed neighborhood B(v) consists of v and v XOR 2^i for 0<=i<6. A code C is local 1-identifying exactly when it intersects all 64 closed neighborhoods and all 192 symmetric differences B(u) Δ B(v) for adjacent u,v. Codeword endpoints are included in the separation condition.

The primary formal proof uses `exclude13-path.cnf`, with 727 Boolean variables and 1623 clauses:

- 64 domination clauses;
- 192 adjacent-pair separation clauses;
- three unit clauses selecting vertices 0,1,2;
- 1364 sequential-counter clauses expressing a size bound of at most 13, using 663 auxiliary variables.

The additional normalization is proved, not assumed. If a local identifying code is independent, every vertex outside it has at least two code neighbors, so 6|C| >= 2(64-|C|), giving |C| >= 16. A non-independent local identifying code cannot have an isolated two-vertex component, because its endpoints would have identical identifying sets. Thus a code of size at most 13 contains a codeword with two codeword neighbors. Translation and a coordinate permutation move these three vertices to 0,1,2, preserving validity and size.

Each auxiliary variable has explicit prefix-count semantics s(i,j) iff at least j of the first i original variables are true. The formal cardinality extension proves that every actual code with size at most 13 satisfies all counter clauses under this assignment. No property of the PySAT encoder is assumed on trust.

## Upper-bound witness

Decimal vertex labels:

0,4,15,23,26,29,31,33,35,36,41,49,58,62.

`independent_witness_check.py` checks actual Hamming distances and identifying sets. `lean/LocalIdentifyingQ6.lean` independently proves the witness cardinality and full local-identification property by kernel computation.

## Lower-bound certificate

The path-normalized LRAT proof has 61,970 RUP additions and 1,987,090 propagation hints. It contains no RAT additions. The final empty-clause identifier is 92061.

- `exclude13-path.cnf`, `exclude13-path.lrat`: exact certificate inputs.
- `independent_lrat_check.py`: standalone Python RUP checker.
- `independent_path_lrat_results.json`, `independent_path_official_lrat.log`: independent check records.
- `PATH_CERTIFICATE_SHA256SUMS`: certificate and generator hashes.
- `RUP_FAST_SOURCE_MANIFEST.json` and `.sha256`: exact replay source/JSON manifest.
- `rup-fast-step-map.json`: module-to-certificate-step mapping.

The primary Lean route is `lean/RUPReplay.lean` plus `lean/RUPPathFast/`. The metaprogram reads the certificate-derived JSON and constructs explicit propositional proof terms using disjunction elimination, contradiction and local let bindings. Every theorem is submitted through ordinary `addDecl` to the Lean kernel. It does not use `native_decide`, `Lean.ofReduceBool`, a new axiom, or the SAT solver's reported status as a proof. An independent negative test with a corrupted hint reference is rejected by the kernel.

## Rebuilding

Use the official Lean 4.24.0 toolchain, commit 797c613eb9b6d4ec95db23e3e00af9ac6657f24b. Only Lean and its bundled Std library are needed for verification; no mathlib or SAT solver is needed to check the supplied proof.

The compact replay layout is fixed by `fast-layout.json`: 87 initial modules of 100 steps, followed by modules of up to 500 steps. To regenerate the replay inputs from the supplied LRAT certificate, run from this directory:

    python generate_rup_fast.py --prefix-count 87 --batch-size 500

This produces 194 modules, ending in `RUPPathFast.Chunk0193`. The final theorem is `LocalIdentifyingQ6.minimum_local_identifying_Q6` in `lean/FullTheorem.lean`; it uses `Q6RUPPath.c92061` to discharge the complete lower-bound reduction.

For an independent verification that ignores all pre-existing project `.olean` files, run:

    LEAN=/path/to/lean python verify_lean_clean.py /path/to/new-empty-check-directory

The destination must not already exist. The script snapshots and hashes the actual final dependency closure, then recompiles each module in a separate output tree. Its `status.json` must report `success: true`; the final log must list only the standard axioms `propext`, `Classical.choice` and `Quot.sound` for the unconditional theorem.

`lean/check_mathematics.sh` checks the mathematical reduction alone; it is not a replacement for the complete clean check. The development run recorded per-module timing, memory and hashes in `verification/first/`. The release's supported build is the clean verifier above, not a cached development pass.

## Discovery and independent corroboration

`solve.py` uses the unrestricted 64-variable MILP and returns objective 14. This is discovery evidence, not the final proof. SciPy 1.17.0 and the bundled HiGHS 1.8.0 were used.

PySAT 1.9.dev15 with CaDiCaL195 generated the primary proof; Glucose4 independently reported UNSAT for the original one-unit normalization. The separate `exclude13.cnf`/`exclude13.lrat` route uses only the translation normalization 0 in C and has 343,158 RUP additions. It also passes the standalone and official LRAT checks, but is not the primary Lean certificate.

Official drat-trim source: https://github.com/marijnheule/drat-trim , commit 2e3b2dc0ecf938addbd779d42877b6ed69d9a985. The recorded build used:

    gcc drat-trim.c -D_DEFAULT_SOURCE -std=c99 -O2 -o drat-trim
    drat-trim exclude13-path.cnf exclude13-path.drat -L exclude13-path.lrat
    lrat-check exclude13-path.cnf exclude13-path.lrat

The source-expanded `lean/RUPPath/Chunk*.lean`, original-normalization `lean/RUP/` prototype, and monolithic experiments are not dependencies of the primary final theorem. They need not be included in the compact release. The experimental transparent-counter artifacts are likewise excluded.

## Prior art

Herva, Laihonen and Lehtilä, “Optimal Local Identifying and Local Locating-dominating Codes,” Fundamenta Informaticae 191 (2024), 351–378, Definition 1.3; DOI 10.3233/FI-242187. Sources: https://fi.episciences.org/13881/pdf and https://arxiv.org/abs/2302.13351 . The strongest located prior upper bound is 15 (arXiv version 3, Proposition 2.15), although the table in the journal-hosted PDF gives the older interval 12–16. The appropriate comparison is 12–15. Literature searches did not locate a subsequent exact value; this is a bounded novelty check, not a guarantee that no unpublished or unindexed result exists.
