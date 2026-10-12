# Frozen upper-bound proof specification

Frozen on 12 October 2026. Originality has not been established. This proof is about planar rotations, not polyhedral unfolding.

For a finite list `steps : List (Real × Complex)`, each entry `(angle, center)` defines the literal map

    rotation angle center z = exp((angle : Complex) * I) * z
                               + (1 - exp((angle : Complex) * I)) * center.

`applyRotations` applies the first list entry first, then recursively applies the tail, so the last rotation acts last. `totalAngle` is the sum of list angles. `centers` is exactly the set of second coordinates of entries. The convex hull is over Real.

The principal theorem is `RotationCenterBound.composite_rotation_center_near_hull`.
Its assumptions are:

- Every list angle is nonnegative.
- The total angle Theta satisfies 0 < Theta <= pi.
- D is a nonnegative real number.
- Every pair of listed centers has Euclidean distance at most D.

It concludes there exists a complex number c such that:

1. For every z, the actual finite composite map equals the rotation of angle Theta about c.
2. For every z, that composite fixes z if and only if z = c.
3. There exists w in the real convex hull of the listed centers with norm(c-w) <= (D/2) tan(Theta/4).

The last condition is stronger than the corresponding distance-to-hull upper bound. Nonemptiness follows from the positive total angle; zero individual angles, repeated centers, collinearity, and D=0 are allowed.

No coefficient positivity, trigonometric estimate, center representation, or convex-hull diameter estimate is left as a hypothesis. The exact angle-list constant and directional-width refinement are outside this frozen closure. Sharpness is included as described below.

Closure order:
1. RotationComposition.lean
2. ComplexWeightGeometry.lean
3. RotationCoefficients.lean
4. RotationCenterBound.lean

The checked principal theorem has only propext, Classical.choice, and Quot.sound among its axioms. No sorry, admit, custom axiom, or opaque oracle is used. Compiler evidence is included in verification/. A separate replay should use fresh output and inspect the exact expected statement.

## Sharpness and semantic fixture

RotationSharpness.sharpness applies for every real A,D with 0 < A <= pi and D >= 0. It constructs exactly two steps, with angles A/2 and centers 0,D. It proves their total angle is A, all angles are nonnegative, all pairwise center distances are <= D, and the endpoint distance is exactly D. It supplies a hull point whose distance from the composite center equals (D/2)tan(A/4), together with the matching lower bound for every hull point.

RotationExpectedStatement.literal_composite_center_bound proves the same upper-bound statement after replacing the rotation definition with exp(i angle)*(z-center)+center, and totalAngle with the ordinary list sum of first coordinates. The fixture is project-authored; the full sources were also independently rebuilt in a separate checking pass from fresh outputs.

The closure adds RotationSharpness.lean and RotationExpectedStatement.lean in that order after the four upper-bound modules. RotationAudit.lean is a separate exact certificate for the counterexample discussed in the paper, not a dependency of the sharp-bound theorem. It is compiled last by the replay script.
