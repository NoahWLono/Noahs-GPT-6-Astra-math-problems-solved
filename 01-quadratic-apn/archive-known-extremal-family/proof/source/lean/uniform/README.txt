UNIFORM QUADRATIC FAMILY

Strongest theorem:
FamilyAlgebra.uniform_nonaffine_quadratic

For every natural number e > 0, the theorem proves the existence of an actual
map BitVec (4e) -> BitVec (4e) with a squarefree homogeneous quadratic
representation whose indices satisfy i < j < 4e, explicit nonaffineness, and
exactly 3 * 2^(2e-1) - 1 nonzero nonbent component masks. Bentness means the
original universally quantified actual integer Walsh predicate FastWalsh.IsBent.
The only hypothesis is e > 0.

FamilyAlgebra.uniform_quadratic_family additionally classifies every mask by
the six base tuples and zero effective extension coordinates.
FamilyAlgebra.uniform_twelve_count specializes the existence/count result to
12 input/output bits and 95 nonzero nonbent components.

PINNED DEPENDENCIES
Lean 4.19.0, compiler commit 6caaee842e94.
mathlib commit c44e0c8ee63ca166450922a373c7409c5d26b00b.
The Lake project and lean-toolchain pin these dependencies.

PORTABLE SETUP AND REPLAY
From this directory, with an official Lean/elan installation available:

    lake update
    lake exe cache get
    lake env python3 replay.py --clean

The replay.py runner is the exact independently tested checker. It verifies
source hashes, prepends this source root to the inherited LEAN_PATH, removes
only local generated object files when --clean is passed, and compiles all
26 modules in topological order with one Lean thread.

The complete dependency-download flow above also PASSED from a freshly
extracted source archive: fresh official upstream dependencies, isolated
HOME/cache/git settings, and no old mathlib or project path. Only the official
Lean 4.19.0 toolchain and Std were reused. After an initial download launcher
timeout, resumed lake update succeeded; cache get and all 26 modules passed.
No proof source changed. Sanitized evidence is in bootstrap/.

Alternatively, when LEAN_PATH already identifies the exact dependencies, run:

    python3 replay.py --clean --lean /path/to/lean-4.19.0/bin/lean

An optional --lock PATH serializes against another compile job on Unix.
The runner monitors a 3-GiB resident-memory cap on Linux. Around 2.1 GiB peak
RSS was observed in the recorded run. Logs are ordinary compiler output.

VERIFICATION EVIDENCE
build.log                 Complete successful source-only replay and axiom output
SOURCE_MANIFEST.json      Exact local .lean source hashes
REPLAY_ORDER.txt          Dependency-ordered list of all 26 modules
verification.json         Structured scope, toolchain and replay facts
bootstrap/                Fresh dependency setup and full replay evidence
TOOLCHAIN.txt             Exact compiler and mathlib revision

The initial replay tree had no local .olean files. All 26 modules exited zero
and the final frozen source hashes matched. Only external pinned Lean/mathlib
compiled libraries were reused. The final theorem's axioms are exactly:
propext, Classical.choice, Quot.sound.

SCOPE
The uniform proof makes classical choices of fields, generators and bases.
It is not an efficient coefficient-extraction algorithm for arbitrary e.
It does not identify its e=3 witness byte-for-byte with the separate explicit
66-mask polynomial in ../concrete.
It does not prove the cited universal lower bound, historical novelty,
sharpness for n = 2 modulo 4, the optional linear-coordinate variant, or the
separately stated signed-spectrum multiplicities.

