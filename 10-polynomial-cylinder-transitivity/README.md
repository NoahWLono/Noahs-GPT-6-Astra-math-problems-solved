# Four additive group actions on a family of affine cylinders

**Completed scoped pointwise-transitivity theorem, verified in Lean. Historical novelty remains provisional. Affine-space cancellation is not resolved by this work.**

[Read the paper](paper/polynomial-cylinder-transitivity.pdf) · [LaTeX source](paper/polynomial-cylinder-transitivity.tex) · [Reproduce the proof](lean/README.md) · [Verification record](verification/README.md) · [Prior-art comparison](reviews/prior-art-review.md)

## Exact completed result

For every nonconstant complex polynomial `P`, any two points of the cylinder

`x^2*y + z^2 + x + P(t) = 0` in five coordinates `(x,y,z,t,u)`

are connected by at most **13 evaluations of four explicitly specified polynomial additive-group actions**. The result also holds over every algebraically closed characteristic-zero field. There is no assumption on multiplicities of roots, critical points or critical values of `P`.

The maps are expressed in the explicitly equivalent adapted equation `x^2*y + 2*x*z*u + z^2 + x + P(t) = 0`. Lean checks the coordinate-change inverse identities, the equation correspondence, multivariate-polynomial coordinates for each actual action, its group laws and preservation, and full pointwise transitivity. Exceptional loci are included. The final theorem assumes only `P.natDegree != 0` and the two original equations; it does not assume polynomial surjectivity or a bridge witness.

The concrete endpoint is `ZariskiCylinder.complex_original_transitive_thirteen`. The independently expanded specification `ZariskiCylinder.Expected.checked_main` bundles the four polynomiality statements, four addition laws, four preservation identities, and the original-equation thirteen-move conclusion. Its reachability relation permits exactly the four displayed actions, reflexivity and padding for the move bound.

## Scope and prior work

The construction explicitly extends Poloni's September 2026 four-action theorem for the Russell cubic, corresponding to `P(t)=t^3`. His adapted embedding and auxiliary formulas are credited. The extension here treats arbitrary nonconstant `P` with a global polynomial divided-difference formula and a uniform thirteen-move bound. A targeted primary-literature search did not locate the full extension; that is not exhaustive novelty certification or a priority claim.

The manuscript separately proves smoothness and irreducibility and uses the published AFKKZ theorem to deduce tangent-space flexibility and infinite transitivity of the special automorphism group. Those geometric results and the AFKKZ implication are **outside this Lean formalization**. The thirteen-move bound concerns individual points, not arbitrary finite tuples. No isomorphism with affine space, non-isomorphism result or cancellation theorem is proved.

## Verification and package

All eleven unchanged Lean modules passed the original build, an independent clean rebuild, and a further fresh-output replay of the included portable build script. Final axiom reports contain only `propext`, `Classical.choice`, and `Quot.sound`. There are no admitted proofs, custom axioms or native-evaluation proof shortcuts. The complex endpoint imports Mathlib's actual fundamental-theorem-of-algebra module directly.

- `paper/`: eight-page manuscript, visually inspected PDF, unchanged LaTeX and standard build script
- `lean/`: eleven unchanged modules, version pins, source checksums and bounded reproduction script
- `verification/`: normalized compiler evidence, resource measurements, provenance and exact formal boundary
- `reviews/`: primary-source comparison and explicit originality limits
- `SHA256SUMS`: checksums of all package files except itself

No dependency checkout, compiled proof objects, private research notes, account metadata or machine-specific paths are distributed. Upstream cached dependencies were reused; no separate-kernel replay, full Mathlib source build, fresh-network installation test or external human peer review is claimed.
