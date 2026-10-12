# A sharp bound for centers of composite planar rotations

**Completed scoped theorem and sharpness, verified in Lean. Historical novelty is unestablished. Dürer's edge-unfolding conjecture is not resolved by this result.**

[Read the three-page paper](paper/rotation-center-bound.pdf) · [LaTeX source](paper/rotation-center-bound.tex) · [Exact formal specification](SPEC.md) · [Verification](verification/README.md) · [Prior-art context](reviews/prior-art-review.md)

## Exact result

Take a finite list of planar rotations with nonnegative angles and total angle `0 < Theta <= pi`. Let `D` be the diameter of the listed centers. The actual composite is a rotation with a unique center `c`, and there is a point `w` in the real convex hull of those centers such that

    norm(c - w) <= (D / 2) * tan(Theta / 4).

For every permitted total angle and every nonnegative `D`, two rotations of angle `Theta/2`, centered at the endpoints of a segment of length `D`, attain the bound. The formal sharpness theorem proves both a lower bound for every hull point and existence of an attaining point.

The principal theorem is `RotationCenterBound.composite_rotation_center_near_hull`. Individual zero angles, coincident centers, collinearity, and `D=0` are permitted. The list is nonempty because its total angle is positive. The formal statement accepts any nonnegative pairwise distance bound `D`; choosing the finite center-set diameter gives the displayed theorem. No desired trigonometric estimate, coefficient sign, center formula, or convex-hull bound remains as a hypothesis.

`RotationExpectedStatement.literal_composite_center_bound` rewrites the definition using `exp(i*angle)*(z-center)+center` and the ordinary list sum of angles. `RotationSharpness.sharpness` establishes the matching examples. `RotationAudit.lean` separately checks the quarter-turn example discussed in the source-context section of the paper.

## Scope and attribution

This is a theorem about finite planar rotation maps. It supplies no successful edge-cut tree, face non-overlap certificate, or chain-specific separation margin for a polyhedron. Dürer's conjecture remains unresolved by this work.

The paper's elementary source-context example addresses the unrestricted wording of Proposition 9 in arXiv:2603.09813v3 and its use in Lemma 8. It does not establish that the later lemma or main unfolding theorem is false. The classical composition formulas and elementary counterexample are not claimed as new. The bounded prior-art search did not establish historical originality of the sharp diameter theorem.

## Reproduce the checks

Use official Lean 4.32.2 and the prepared mathlib checkout pinned in `lean/mathlib-revision.txt`. Existing mathlib dependencies and compiled caches are required; the script performs no installation or downloads. Run:

    python lean/replay.py \
      --lean /absolute/path/to/lean-4.32.2/bin/lean \
      --mathlib /absolute/path/to/mathlib4-v4.32.2 \
      --output /absolute/path/to/a-new-output-directory

The output directory must not exist. Lake is used only to read the dependency path and exits before direct Lean compilation begins. Each source is checked with one thread, `-M3072`, a 30-second timeout, and a 3-GiB process-group RSS guard. Do not add a virtual-memory ulimit: Lean reserves a large virtual address arena. The script checks all six theorem modules and the separate audit certificate. Only `propext`, `Classical.choice`, and `Quot.sound` occur in the printed theorem axiom lists.

## Files

- `paper/`: PDF, LaTeX, and TeX build script
- `lean/`: seven unchanged proof sources, portable replay, toolchain and dependency pins, source hashes
- `SPEC.md`: exact assumptions, conclusions, and formal boundary
- `reviews/`: bounded primary-source comparison and priority limitations
- `verification/`: normalized compiler logs, replay receipts, source comparison, and PDF review record
- `SHA256SUMS`: checksums of this package's files except itself

No compiled project objects, dependency checkout, build cache, credentials, or private research notes are distributed. No separate-kernel replay, whole-Mathlib source rebuild, fresh-network installation test, or external human peer review is claimed.
