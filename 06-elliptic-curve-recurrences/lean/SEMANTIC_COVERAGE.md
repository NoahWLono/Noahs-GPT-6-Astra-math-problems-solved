# Manuscript-to-formal coverage

This package formalizes mathematical statements from ASTRA-01. It does not claim full manuscript verification, novelty, an ECDLP solver, or a runtime lower bound. The original 24 published files are unchanged. The dated formal-verification addendum describes the current published-artifact scope.

## Foundations and degree convention

The source is a genuine Mathlib nonsingular Weierstrass curve over an algebraically closed field, in every characteristic unless an endpoint says otherwise. Points carry Mathlib's actual elliptic group law. The function field is an actual fraction field of the coordinate ring. All auxiliary polynomial/rational-function algebra, localization, finite-extension and separability structures are constructed in EllipticFunctionField.

D means the sum of actual pole multiplicities, matching the manuscript's explicit degree convention. Normalized valuations, the global product formula, unique infinity place, rational-point/place dictionary and positive degree of nonconstant functions are proved. There is no assumed geometric degree or divisor oracle. A separate scheme/morphism API formulation, and reduction from every abstract curve presentation to a Weierstrass model, are not supplied.

Projective values use Option k, with none for infinity. Finite values are constructed through actual residue fields. RationalProjectiveComposition proves agreement with the usual outer rational map at every point, including denominator roots and common poles.

## Main theorems

- T1: GlobalProjectiveRecurrence.global_projective_recurrence_obstruction proves r=1 and n divides D from the pointwise global recurrence. Equality in the function field is derived. Exact finite order n≥2 is explicit; primality and characteristic restrictions are absent.
- T2: ProjectiveRecurrenceBounds.full_agreement_set_bound proves the full cyclic agreement-set bound min(n,D(r+1)). The nonglobal branch uses the genuine effective coincidence divisor; the global branch uses T1.
- T3: ProjectiveRecurrenceBounds.full_menu_agreement_set_bound proves the full finite-menu bound min(n,D·sum(r_j+1)) for a fixed finite family of reduced nonconstant rational maps.
- T4: ProjectiveQuotientRecurrence.pgl_cyclic_subgroup_recurrence is the literal PGL quotient theorem on the genuine projective line. It proves injectivity on the cyclic subgroup, exact order n of the PGL element, the three finite-field alternatives and the minimal extension-degree divisibility. Exact order is not asserted for an arbitrary matrix lift. The action and representative existence are constructed from the actual quotient.
- T5: PrimeFullGroupPGLObstruction.prime_full_group_pgl_recurrence_constant proves that every full base-field PGL recurrence is constant when p≥17 is prime, the actual full group has prime cardinality n≠p, and G is nonzero. The function is arbitrary on the actual full group. Hasse, exact order of G, full subgroup generation and representative existence are derived rather than assumed.
- T6: PrimeOrbit proves the full universal deterministic prime-cycle injectivity theorem. Nonconstancy is within the first n entries; no invertibility of the update function is assumed.

## Examples

- E1: SharpnessActualGroup and SharpnessActualOrbit identify the complete F11 table with Mathlib's actual elliptic group, prove 13 rational points and generator order 13. EllipticXYDegrees proves degree(x)=2. EllipticXProjectiveValue identifies geometric x evaluation with ordinary finite coordinates and infinity. SharpnessGeometricAgreements.geometric_exact_count proves exactly four agreements, at indices 1,6,8,9, after every algebraically closed F11 base extension. The extension group homomorphism is proved injective.
- E2: SharpnessMenuEndpoint constructs the four displayed coprime degree-one maps and proves they cover the actual extended cyclic subgroup. Its no_smaller_cover theorem proves every degree-one menu over the algebraically closed extension that covers this subgroup has at least four members. SharpnessBaseFieldMinimum now also proves the literal F11-only minimum theorem for arbitrary reduced degree-one p/q menus and supplies the four-map witness. Its proof constructs the algebraic closure and fraction field internally.
- E3: CharacteristicSevenExample verifies the explicit F7 curve, 12 rational points, generator order three, degree(y)=3 and the global projective semiconjugacy over algebraically closed extensions.
- E4: DoublingEvaluationCost.exponential_degree_linear_doublings proves the general characteristic-not-two Weierstrass statement: the actual function has pole degree 2·4^t, its value at every point is x([2^t]P), and the explicit evaluator is charged exactly t point doublings followed by reading x. degree_at_eight proves 131072. This is a specified group-operation model, not a field/bit-cost or runtime lower bound.

## Audit status

All 113 local modules were rebuilt from source into a fresh object directory with pinned Lean 4.32.2. The run exited 0 in 535.05 seconds; peak sampled process-group RSS was 3346960 KiB. Printed transitive axiom closures use only propext, Classical.choice and Quot.sound. Separate replays cover 83 modules. See the build record, axiom audit and replay manifest.

## Geometric prerequisites and Hasse

The package constructs actual point principal divisors, the product formula, the point/place dictionary and degree-zero principal-divisor existence. It proves actual torsion Weil functions, although a full Weil pairing is not needed for the chosen Hasse proof. Actual point heights satisfy the parallelogram law and a Cauchy–Schwarz discriminant inequality, proved through the symmetric-square addition/subtraction map and normalized valuations.

Finite-field Frobenius is the genuine point-group homomorphism. The generic point has height two and its Frobenius image has height 2q. Their actual difference has an x-coordinate pole of order two at infinity, and actual rational translations preserve that function. Summing its rational-point poles gives the upper point-count bound. The explicit nonsingular general-model twist and exact character count identity give the opposite side. EllipticHasseOdd.finite_field_hasse_discriminant exports (N−q−1)^2≤4q in odd characteristic, without geometric interface hypotheses: the finite-field-only wrapper constructs every auxiliary field structure internally. This is a formalization of the classical Hasse prerequisite, not a historical novelty claim.

## Additional manuscript claims

K1's universal Semaev factorization and denominator-cleared affine addition identity are checked in PolynomialIdentities. The attribution to prior literature, and the manuscript's reported 724 empirical checks, are not proof-assistant claims here. The E1/E3/E4 endpoints supply the mathematical counterexamples behind F1/F2/F3; separate prose-level inference labels are not new formal theorems. T3's uniform probability corollary follows arithmetically from its full set-cardinality bound, but a probability-space API wrapper is not supplied.

U1–U5 remain unproved or unestablished as in the source package: no cryptographic solver, general runtime lower bound, coordinate inversion algorithm, efficient-reduction sufficiency or novelty result is claimed. The original U6 statement describes the published package before this local proof addition; the original files have deliberately not been rewritten. Independent parent replays use the same trusted environment and are not external expert peer review.
