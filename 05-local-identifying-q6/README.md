# The minimum local identifying code in Q6 is 14

This package contains a size-14 code and a Lean 4.24.0 proof that every local
1-identifying code in the six-dimensional binary cube has at least 14 words.
The definition distinguishes every adjacent pair, including codeword vertices.

## Verification status

The first complete Lean kernel build passed, with only the standard axioms
`propext`, `Classical.choice`, and `Quot.sound`. The independent clean-source rebuild also passed.
See `full-first-result.json`, `full-first-check.log`, and `verification/clean/`.
No SAT-solver answer, floating-point bound, new axiom, `sorry`, `native_decide`,
or `Lean.ofReduceBool` is used as an assumption of the theorem.

## Check the full theorem from scratch

Requirements: Python 3 and the official Lean 4.24.0 toolchain. No mathlib,
PySAT, C compiler, solver, or network access is needed to verify this package.
The supplied `lean-toolchain` pins the version for an existing elan setup.

From this directory, choose a destination that does not yet exist:

    LEAN=/absolute/path/to/lean-4.24.0/bin/lean ./build.sh /tmp/q6-independent-check

If `lean` already selects the pinned toolchain, `./build.sh /tmp/q6-independent-check`
is sufficient. The wrapper resolves the actual toolchain binary before changing
working directories. It snapshots the final dependency closure, hashes every
input, and recompiles all 257 modules in a separate directory. No existing
project `.olean` files are reused. Expect substantial computation and several
GB of memory; measured times and memory are included in the verification logs.

A successful run sets `/tmp/q6-independent-check/status.json` to `success: true`
and prints the axiom dependencies of:

    LocalIdentifyingQ6.minimum_local_identifying_Q6

Its statement gives both a local identifying code of cardinality 14 and a lower
bound of 14 for every local identifying code. The source is
`lean/FullTheorem.lean`.

## Smaller independent checks

    python3 materialize_certificates.py
    python3 independent_witness_check.py
    python3 independent_lrat_check.py exclude13-path.cnf exclude13-path.lrat
    python3 independent_path_encoding_check.py
    python3 independent_replay_data_check.py

These standard-library checks corroborate the witness, exact RUP refutation,
and graph/cardinality encoding. They do not replace the full Lean proof.

## Reconstruct the compact replay inputs

The LRAT and optional producer DRAT certificates are supplied as deterministic gzip files. `materialize_certificates.py` checks both compressed and decompressed byte counts and SHA-256 hashes before writing them; `build.sh` runs it automatically.

The supplied JSON files can be regenerated from the fixed LRAT certificate after materialization:

    python3 generate_rup_fast.py --prefix-count 87 --batch-size 500

The result is the supplied 194-module layout, with 61,970 RUP steps and
1,987,090 hints. The final empty clause is `Q6RUPPath.c92061`, imported from
`RUPPathFast.Chunk0193`. `RUPReplay.lean` constructs ordinary propositional
proof terms, which are checked by the Lean kernel one theorem at a time.
The proof generator is untrusted; malformed data must fail kernel checking.

`verification/clean/source-manifest.json` pins the complete 451-file Lean/JSON
source closure. `RUP_FAST_SOURCE_MANIFEST.json` pins the replay inputs and
certificate/generator data. `MANIFEST.json` and `SHA256SUMS` cover this package.
The large source-expanded fallback and all compiled caches are omitted.

The explicit witness is:

    0,4,15,23,26,29,31,33,35,36,41,49,58,62

See `REPRODUCIBILITY.md` for the exact reduction, normalization, counter
semantics, solver provenance, certificate checks and prior-art comparison.
