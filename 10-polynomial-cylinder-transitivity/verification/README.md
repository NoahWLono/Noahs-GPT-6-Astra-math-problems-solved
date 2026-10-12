# Verification record

Date: 12 October 2026.

## Exact checked result

For an actual complex polynomial `P` with `P.natDegree != 0` and arbitrary points `p,q` in five complex coordinates satisfying `x^2*y+z^2+x+P(t)=0`, `ZariskiCylinder.complex_original_transitive_thirteen` concludes `OriginalReaches P 13 p q`.

`OriginalReaches` transports the precisely defined four-move relation through the checked inverse adapted-coordinate maps. `Reaches` has only reflexivity, one permitted action step and padding, so the result is an upper bound of thirteen action evaluations. It is not reachability by arbitrary maps. The independently expanded `ZariskiCylinder.Expected.checked_main` includes the original equation explicitly and bundles polynomiality, action addition laws and equation preservation with this conclusion. Identity laws and inverse reachability are also checked in the included modules. The generic algebraically closed characteristic-zero theorem is included.

## Checking evidence

- `components/` contains all eleven successful original compiler logs and resource records.
- `independent-rebuild.log` records the clean rebuild of a byte-identical source snapshot into fresh outputs.
- `publication-rebuild.log` records a further fresh-output replay of the unchanged publication sources through the exact included portable `lean/build.sh` and `lean/check_one.py`.
- All final theorem axiom audits contain only `propext`, `Classical.choice` and `Quot.sound`.
- Source review found no admitted proofs, custom axioms, `native_decide` or unsafe project declarations.
- `FTA_PROVENANCE.txt` records the direct official Mathlib fundamental-theorem-of-algebra import and source comparison. No copied or custom FTA proof is used.
- `dependency_closure.json` records the explicit import closure and states the compiler-runtime boundary.
- `paper-qa.json` records the unchanged eight-page PDF and LaTeX hashes and visual inspection.

All builds used official Lean 4.32.2 and Mathlib commit `905b95818eb32af7874a58b427f50c1711a5e96c`. Upstream compiled dependency caches were reused. Each publication invocation used one compiler thread, a 3072 MiB Lean allocation cap and a 60-second timeout. The original and normalized rebuild-log hashes and module resource measurements appear in `verification_manifest.json`.

## Normalization and limits

Absolute machine-specific source prefixes in published compiler logs are replaced by `lean/`. All compiler messages, line and column numbers, theorem names, axiom reports, exit codes and resource measurements are retained. The original logs remain archived separately; normalization does not constitute another proof run. The public scripts are portable versions of the original harness, and the further publication replay validates them from fresh outputs. The mathematical Lean, LaTeX and PDF bytes did not change during curation.

Scheme smoothness, irreducibility, tangent-space flexibility, infinite transitivity and the AFKKZ implication are written or externally cited geometric arguments, not part of the formal theorem. The thirteen-move bound is for point pairs. No cancellation, affine-space isomorphism or non-isomorphism theorem is claimed. There was no separate-kernel replay, full Mathlib source build, fresh-network installation test, external human peer review or exhaustive novelty certification.
