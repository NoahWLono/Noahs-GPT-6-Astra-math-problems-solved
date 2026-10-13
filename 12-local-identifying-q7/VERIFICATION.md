# Reproducibility

## Status and requirements

The unchanged public verifier completed a fresh build of all 3,046 custom modules, with zero custom-object reuse. All 162 required named theorem audits in 137 modules passed, including the final original-predicate type check. The replay ran on x86_64 Linux from a fresh transport-only package copy, under an external resource supervisor that left the public driver and proof bytes unchanged. See [public replay evidence](PUBLIC_VERIFICATION.md). Other operating systems and fresh network dependency installation have not been tested. The separate independent source rebuild has completed successfully; its provenance and audited receipt are in INDEPENDENT_VERIFICATION.md. A successful static check does not prove the theorem.

Use Python 3.10 or later, Git, and official Lean **4.32.2**. Mathlib is pinned to [commit `905b95818eb32af7874a58b427f50c1711a5e96c`](https://github.com/leanprover-community/mathlib4/commit/905b95818eb32af7874a58b427f50c1711a5e96c), whose toolchain declaration is Lean 4.32.2. Its transitive dependencies are pinned by [mathlib-lake-manifest.json](manifests/mathlib-lake-manifest.json). Obtain the toolchain from the [official Lean releases](https://github.com/leanprover/lean4/releases/tag/v4.32.2), or install that exact toolchain using [official elan instructions](https://github.com/leanprover/elan). Do not substitute a newer version.

From this folder:

```sh
python3 verify.py --check-inputs
```

This command first automatically reconstructs the complete source archive from `transport/` parts, verifies every part and the combined archive SHA-256, and safely extracts only the 4,490 manifest-listed regular files. Archive links, unsafe paths, duplicate entries, unexpected files and hash mismatches are rejected. It runs no Lean compiler and verifies all 4,490 source/data hashes, exact file coverage, the topological order and named audit requirements.

## Prepare external dependencies

Create a separate dependency directory, then obtain the pinned Mathlib source:

```sh
mkdir -p .deps
git clone https://github.com/leanprover-community/mathlib4.git .deps/mathlib4
git -C .deps/mathlib4 checkout --detach 905b95818eb32af7874a58b427f50c1711a5e96c
```

Run dependency preparation from that checkout using Lean 4.32.2's Lake. The following is the normal Mathlib cached-dependency route, not a custom-proof cache:

```sh
cd .deps/mathlib4
lake exe cache get
cd ../..
```

Review that the committed dependency lock has not changed. The verifier compares it byte-for-byte with this package's lock copy and checks each dependency checkout's exact commit and tracked-file cleanliness. Cached dependency objects are part of the trust boundary. For a stronger external-dependency check, use a fresh checkout and build Mathlib and its dependencies from their pinned sources instead of downloading the Mathlib cache. That alternative has not been exercised here either.

## Fresh custom-proof compilation

Set `LEAN_ROOT` to the official installation directory containing `bin/lean` and `lib/lean` (for elan, `elan which lean` identifies the selected executable). Set `MATHLIB` to the prepared checkout. Then run:

```sh
python3 verify.py --lean-root "$LEAN_ROOT" --mathlib "$MATHLIB" --output .verify
```

The output directory must not exist. The verifier does not resume or import any old custom proof object. Use a new output directory for each retry. It clears inherited `LEAN_PATH` by supplying only the new custom-object root, the selected Lean standard library, and pinned external dependency build directories. It runs one compiler process at a time from `source/`, preserving relative quoted-data paths.

Every one of the 3,046 custom modules is compiled in the frozen topological order, including all certificate/refutation leaves. The compiler must exit successfully and produce the expected object. For every designated final/consumer theorem the verifier requires a named axiom report; absence is a failure, and only `propext`, `Classical.choice`, and `Quot.sound` are allowed. The defining `ExactQ7` module's own audit and the separate exact-type audit must both pass. Ordinary modules may omit audit output; any axiom output they do produce is still checked.

Successful completion writes `.verify/RESULT.json` and per-module logs, together with source/object/log hashes. Inspect the logs for `Q7Mod.Integration.ExactQ7` and `Q7Mod.Integration.ExactQ7Audit`. A missing `RESULT.json` means the run did not finish successfully. The verifier does not impose a wall-clock/resource limit; allocate enough disk, memory and time, and interrupt it if necessary. The completed replay used 9,571.064417 child CPU seconds and 9,703.032116 wall seconds, with maximum observed process-tree RSS 1,459,834,880 bytes. These are measurements from one x86_64 Linux environment, not portable resource guarantees. External-supervisor accounting and limits are documented in PUBLIC_VERIFICATION.md.

## Auxiliary numerical check

The witness checker, when included, tests the explicit 24-element code directly. It is useful for checking the finite specification but does not establish the universal lower bound. The Lean theorem and its complete checked dependency closure establish that bound.

## Bounded smoke-test mode

```sh
python3 verify.py --smoke-test --lean-root "$LEAN_ROOT" --mathlib "$MATHLIB" --output .verify-smoke
```

This mode preserves all static input and dependency checks but compiles only the frozen dependency closure of `BergeMod.K1.Replay0000` and `Q7Mod.Canonical.BergeEightNormalization` (12 modules). It exercises standard/custom/Mathlib import paths and relative quoted JSON loading with one kernel-checked RUP step. It writes `SMOKE_RESULT.json`, never the full-build `RESULT.json`, and does **not** verify the final theorem.

The actual CLI passed from a fresh extracted package using the pinned existing official Lean/Mathlib installations: 13.388368 child CPU seconds, 13.571 seconds wall time, peak sampled process-tree RSS 1,038,303,232 bytes. A separate launch harness enforced one sequential compiler slot, 120 total CPU seconds, 60 CPU seconds per process, a conservative whole-CLI 120-second wall bound, 2 GiB RSS, 64 MiB output and a 4 GiB free-disk floor. No bound was hit. Those smoke-test harness limits are not built into the public verifier. See [smoke receipt](checks/PUBLIC_VERIFIER_SMOKE.json) and [exact subset results](checks/SMOKE_RESULT.json).
