# Reproduce from source

## Inputs and requirements

Use Python 3.10 or newer, Git, and the official `leanprover/lean4:v4.32.2` toolchain. The included `lean/lean-toolchain`, `lean/pins.json` and `lean/mathlib-lake-manifest.json` pin the compiler version, Mathlib commit and all eight transitive Git revisions. The committed `rev` values, not floating `inputRev` branches, are authoritative. No upstream source checkout or compiled project object is distributed.

The custom archive expands to about 81.2 MB. Allow at least 2 GiB of free disk after obtaining built dependencies and several GiB of memory; upstream Lean/Mathlib setup needs additional space and time. The long finite arithmetic chain is intentionally compiled one module at a time with `-j1`; it may take hours depending on hardware. No fixed completion time is promised.

## 1. Obtain the exact upstream dependencies

Install the official Lean release through the normal official distribution or elan. Obtain Mathlib and check out the exact commit:

```sh
git clone https://github.com/leanprover-community/mathlib4.git mathlib4
cd mathlib4
git checkout --detach 905b95818eb32af7874a58b427f50c1711a5e96c
lake build
```

Run this with Lean 4.32.2. Preserve Mathlib's committed `lake-manifest.json`; do not run `lake update`, which can move dependencies. `lake build` obtains pinned dependencies and builds from source. If instead using Mathlib's official pinned cache (`lake exe cache get`), record that upstream compiled objects were reused. This optional cache does not replace any of the 763 custom modules.

The Git revisions and clean tracked files of Mathlib and all eight packages are checked by the verifier. The expected lockfile SHA256 is `015c7e00ead0f05f2a72b32d9bdef782d4689d05a6297f0ceb0ab5d196c164bd`. The fresh-network setup recipe has not itself been exercised for this release.

## 2. Verify the transport without compiling

From this numbered folder:

```sh
sha256sum -c SHA256SUMS
python3 lean/verify.py --check-only
```

The script validates the archive before extracting, rejects unexpected/duplicate/nonregular/unsafe members, checks every source hash, and verifies the full topological build order. All 763 sources can also be inspected by ordinary `tar -xzf lean/sources.tar.gz` in a new directory; no generated Lean source or private file is needed.

## 3. Build a fresh custom proof closure

Supply absolute paths to the official Lean executable and pinned built Mathlib checkout. The parent of the output directory must exist, but the output directory itself must not exist:

```sh
python3 lean/verify.py   --lean /absolute/path/to/lean-4.32.2/bin/lean   --mathlib /absolute/path/to/mathlib4   --output /absolute/path/to/new-c3-build
```

For a dependency-only preflight add `--check-dependencies-only`. The default per-module wall timeout is 300 seconds; `--timeout` can raise it on slower hardware. A timeout or nonzero compiler exit stops the build and does not count as success. Use a new output directory for another attempt; the script never resumes by trusting old custom objects.

The verifier extracts the exact sources into the new output root. `LEAN_PATH` contains only the new custom-object directory and the pinned Mathlib/package object directories. No original project object root or inherited `LEAN_PATH` is used. Each module is compiled in `lean/build-order.txt` order with `lean -j1`, finishing with `FinalAudit`. The script checks all eight named final audits (seven standard-axiom reports plus axiom-free literal alignment), writes logs and per-module receipts, and creates `result.json` only after success. Inspect the printed exact theorem and `logs/FinalAudit.txt` as well as the result.

The public script has undergone static and preflight checks only for this release. No full public-wrapper replay is claimed.

## 4. Rebuild the paper and supplementary arithmetic

With a standard TeX Live installation containing the packages named in the LaTeX preamble:

```sh
cd paper
pdflatex -interaction=nonstopmode -halt-on-error scoped-c3-cyclicity.tex
bibtex scoped-c3-cyclicity
pdflatex -interaction=nonstopmode -halt-on-error scoped-c3-cyclicity.tex
pdflatex -interaction=nonstopmode -halt-on-error scoped-c3-cyclicity.tex
python3 replay-certificate.py
```

The Python standard-library replay independently compares the complete finite fifth-power map and checks compact equality, invariance and two residue-coordinate facts. It is supplementary arithmetic, not a substitute for the universal evaluated Lean identity. Rebuilding PDF metadata can change PDF bytes; the release manifest identifies the supplied PDF exactly.
