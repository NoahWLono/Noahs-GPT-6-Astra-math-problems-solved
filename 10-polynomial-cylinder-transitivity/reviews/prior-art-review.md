# Novelty comparison and certification scope

## Established antecedent

Poloni's September 2026 paper, arXiv:2609.14090v1, proves that four specified additive-group actions act transitively on the cylinder over the Russell cubic x²y+z²+x+t³=0. Its adapted embedding and the expressions a=1+xy+2zu, c=zy−2au and m=zy+2au are used here with explicit attribution. The cubic infinitesimal generator is not a new result of this project.

## Extension proved in this package

The statement here allows every nonconstant P∈k[t], for k algebraically closed of characteristic zero, in x²y+z²+x+P(t)=0. It gives a closed polynomial divided-difference formula for the fourth action, including the entire exceptional locus ac=0, and an orbit proof that handles arbitrary critical values of P. Any pair of points is connected by at most 13 evaluations of four displayed actions. The bound is uniform in the degree and coefficients of P; no optimality claim is made.

The full arbitrary-P statement and the 13-move bound do not appear in the Poloni paper. A targeted primary-literature search also checked the 2026 Gaifullin–Petrov and Isaev local-slice/suspension results, without locating a theorem directly covering this statement. The search does not establish worldwide priority or exclude unpublished or differently formulated antecedents. Novelty remains provisional. It would be inaccurate to call this a new solution of cancellation, or to claim novelty merely because its proof has been formalized.

## What the Lean result establishes

All 11 modules passed the project build and an independent clean rebuild under official Lean 4.32.2 with pinned Mathlib revision 905b95818eb32af7874a58b427f50c1711a5e96c. The checked package includes:

1. Multivariate-polynomial coordinates for all four parameterized maps.
2. Their exact additive group laws and equation preservation.
3. The original/adapted polynomial coordinate inverse checks.
4. The original-cylinder pointwise 13-move theorem for every nonconstant complex polynomial, with no extra surjectivity or witness assumptions.

The reachability relation has exactly four move constructors and only reflexivity, concatenation-by-one-move, and padding for the word bound. The theorem is not a claim about arbitrary or unspecified maps.

The reported axioms are propext, Classical.choice and Quot.sound. There are no admitted proofs, extra axioms or native_decide calls in the project source.

## What remains outside the formal theorem

Smoothness, irreducibility, tangent-space flexibility and infinite transitivity of the full special automorphism group are treated in the manuscript. Flexibility and infinite transitivity use the published AFKKZ theorem; that theorem is not formalized here. The 13-move bound is for individual points, not arbitrary finite tuples.

No isomorphism of any cylinder with affine four-space is constructed. No non-isomorphism of the threefolds with affine three-space is proved. The original three-dimensional cancellation question remains unaddressed by this scoped result, and the full research project should not be declared solved on the basis of this package.
