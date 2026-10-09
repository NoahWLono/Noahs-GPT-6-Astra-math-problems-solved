# Reproduce the eight-dimensional APN proof

Requirements: an official Lean/elan installation, Git, Python 3.10+, and a POSIX environment with `which` and `printenv`. Lean is pinned to 4.19.0. Mathlib is pinned to `c44e0c8ee63ca166450922a373c7409c5d26b00b` in `lakefile.lean`.

From this directory:

```sh
lake update
lake exe cache get
python3 rebuild.py
```

The dependency download uses the official mathlib cache. The script verifies the actual mathlib Git commit and compiler version, hashes every local proof source, checks the complete local dependency order, and compiles all 137 modules serially into a freshly cleared `build/` directory. It does not import old local proof objects. Each module has a default 600-second timeout; use `--timeout SECONDS` to change it. Allow several GiB of RAM. Standard toolchain and cached mathlib dependencies are reused, not rebuilt from source.

The 136 proof modules end at `APNEightFinal`; `APNEightFinalAudit` additionally prints the final statements, definitions, and transitive axiom report. The order is frozen in `build-order.txt`; `source-manifest.json` records source hashes. Dependency imports supplied by mathlib or Std are listed in `external-imports.txt`.

For an offline source-integrity and dependency-order check without Lean:

```sh
python3 rebuild.py --check-only
```

Build output goes in `build/logs/`, `build/results.json`, and, only after every module succeeds, `build/SUCCESS`. On failure, read the named module's log. Re-running the script discards only the generated `build/` directory and rebuilds from the first module. A source check alone is not a proof compilation.

The shipped source bytes match the recorded proof snapshots. No `.olean`, `.ilean`, `.lake`, compiler, dependency checkout, or binary cache is included.
