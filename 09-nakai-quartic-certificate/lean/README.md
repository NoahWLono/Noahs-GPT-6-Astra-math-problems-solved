# Reproducing the mixed-quartic certificate

## Pinned dependencies

- Official Lean 4.32.2, commit `f3b06c705e6c85f5314019d5d3baab0fec5b580c`
- Mathlib commit `905b95818eb32af7874a58b427f50c1711a5e96c`
- The accompanying `mathlib-manifest.json` is the upstream dependency lockfile; the build script compares it byte for byte.
- Python 3 and a Linux `/proc` filesystem for the resource monitor

Use official Lean and matching Lake. Prepare the pinned Mathlib checkout and its official cache separately. For example, with the required tools and network access:

```sh
git clone https://github.com/leanprover-community/mathlib4.git mathlib4-nakai
cd mathlib4-nakai
git checkout 905b95818eb32af7874a58b427f50c1711a5e96c
lake exe cache get
```

No dependency download or Mathlib build occurs in the supplied proof script. The fresh-network setup recipe is not itself a tested installation result.

Set paths and run from any directory:

```sh
export MATHLIB_ROOT=/absolute/path/to/mathlib4-nakai
export OUTPUT=/absolute/path/to/new-empty-nakai-build
# Optional if the matching lean executable is already on PATH:
export LEAN_BINARY=/absolute/path/to/lean-4.32.2/bin/lean
bash /absolute/path/to/09-nakai-quartic-certificate/lean/build.sh
```

The output directory must be empty. The script checks the source hashes, exact Lean version and commit, Mathlib commit and dependency manifest. It obtains Mathlib's LEAN_PATH from Lake, lets Lake exit, then compiles each local module directly with one Lean thread and `-M3072`.

Components have a 30-second wall-time and 3-GiB process-group RSS guard. The final pair has a 60-second and 3.75-GiB guard. A timeout, memory limit or compiler error stops the run. Timings depend on the machine; a guard failure does not establish a mathematical failure. Generated logs and resource JSON are written only to OUTPUT. Avoid concurrent memory-intensive builds.

The public build script passed a fresh-output replay of all fifteen unchanged sources against the existing pinned checkout and cache. No fresh-network installation was tested.

## Exact dependency order

1. `NakaiFramework`: faithful order definition, quotient descent, all-derivation ideal stability and full generated-algebra separation framework
2. `QuarticDefinitions`: actual polynomial, gradient, Hessian, adjugate and operator
3. `QuarticCofactors`: actual Hessian cofactor identities
4. `QuarticCoefficientDefinitions`: coefficient-functional definitions and gradient monomials
5. `QuarticDeterminant`: complete determinant expansion
6. `QuarticSeparatorMonomials`: monomial-coefficient support identities
7. `QuarticSeparatorValue`: exact value on the Hessian determinant
8. `QuarticSeparatorAnnihilation`: annihilation for arbitrary polynomial multipliers
9. `QuarticSeparator`: gradient-ideal nonmembership certificate
10. `QuarticOperatorCoefficients`: explicit operator coefficient identities
11. `QuarticOperatorDescent`: ideal preservation on all polynomial multiples
12. `QuarticPolynomial`: assembled polynomial certificates and generator escape
13. `QuarticOperatorOrder`: every triple commutator of the actual polynomial operator vanishes
14. `NakaiConcrete`: actual quotient operator and full-algebra nonmembership
15. `NakaiExpected`: independently expanded intended theorem

`SOURCE_SHA256SUMS` covers these exact source bytes. The complete local closure is rebuilt; cached official upstream dependencies are a stated trust boundary. No separate-kernel export/replay is claimed.
