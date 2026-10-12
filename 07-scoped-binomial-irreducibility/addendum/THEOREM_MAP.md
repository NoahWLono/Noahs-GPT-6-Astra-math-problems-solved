# Exact theorem map

Module: `CompositeInnerPillai`

Namespace: `PillaiScoped`

Root: `PillaiScoped.irreducible_composition_of_inner_prime_factors_gt`

## Exact declaration signature

```lean
theorem irreducible_composition_of_inner_prime_factors_gt
    (p m : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (hm : 1 < m)
    (hprime : ∀ q : ℕ, q.Prime → q ∣ m → p < q)
    (k A : ℤ) (hk : 1 < |k|)
    (hval : ∀ ell : ℕ, ell.Prime → (ell : ℤ) ∣ k → padicValInt ell k < p) :
    Irreducible (((X : ℚ[X]) ^ m - C (A : ℚ)) ^ p + C (k : ℚ))
```

The polynomial expression is in Q[X]. The full source adds no other premise. No sign, gcd, squarefree, field-degree, coefficient-integrality or affine-exclusion assumption is hidden in this signature.

## Mathematical proof steps and declarations

1. `m` is odd because `2` cannot divide it. This is derived directly in the new root.
2. `PillaiGlobalCoefficients.rational_binomial_irreducible_of_valuation_bounds` and `PillaiCapelliBridge.outer_irreducible` establish outer irreducibility.
3. `PillaiCapelliBridge.neg_generator_power` gives theta^p = k in the actual simple root field K = Q(alpha), with theta = -alpha.
4. `PillaiCapelliBridge.exists_reduced_neg_generator_representation` represents every beta in K as a reduced rational polynomial G(theta).
5. `PillaiScoped.reduced_affine_power_equation_exclusion` excludes beta^q = A-theta for every prime q dividing m.
6. The pinned upstream `X_pow_sub_C_irreducible_of_odd` proves irreducibility of X^m-(A+alpha) over K, including repeated prime factors of m.
7. `Polynomial.irreducible_comp` and `PillaiCapelliBridge.composition_identity` give the displayed rational-polynomial irreducibility.

The new audit checks the root and the declarations in steps 2 (valuation theorem), 4, 5 and 6. Each reports exactly propext, Classical.choice and Quot.sound.
