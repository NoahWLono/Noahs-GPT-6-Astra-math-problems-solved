import IntegralResultant

/-! Transfer the actual rational power equation at the real root to every complex root. -/

set_option autoImplicit false
open scoped BigOperators
open Finset Polynomial Complex
open PillaiFourier PillaiResultant

namespace PillaiConjugates

variable {n : ℕ} [NeZero n] {ζ : ℂ}

lemma eval_ratMap_real (p : ℤ[X]) (x : ℝ) :
    aeval x (p.map (Int.castRingHom ℚ)) = p.eval₂ (Int.castRingHom ℝ) x := by
  rw [aeval_def,eval₂_map]
  congr 1

lemma eval_ratMap_complex (p : ℤ[X]) (x : ℂ) :
    aeval x (p.map (Int.castRingHom ℚ)) = p.eval₂ (Int.castRingHom ℂ) x := by
  rw [aeval_def,eval₂_map]
  congr 1

lemma coefficientPolynomial_real_eval (ρ : ℝ) (c : ZMod n → ℤ) :
    (coefficientPolynomial c).eval₂ (Int.castRingHom ℝ) ρ =
      ∑ j : ZMod n, (c j : ℝ)*ρ^j.val := by
  simp only [coefficientPolynomial,eval₂_finsetSum,eval₂_mul,eval₂_C,eval₂_pow,eval₂_X,
    Int.coe_castRingHom]

/-- Irreducibility identifies the actual minimal polynomial at the given real root. -/
lemma pureBinomial_eq_minpoly (ρ : ℝ) (k : ℤ) (hρ : ρ^n = (k : ℝ))
    (hirr : Irreducible ((pureBinomial n k).map (Int.castRingHom ℚ))) :
    (pureBinomial n k).map (Int.castRingHom ℚ) = minpoly ℚ ρ := by
  apply minpoly.eq_of_irreducible_of_monic hirr
  · rw [eval_ratMap_real]
    simp only [pureBinomial,eval₂_sub,eval₂_pow,eval₂_X,eval₂_C,Int.coe_castRingHom,hρ,sub_self]
  · exact (monic_X_pow_sub_C k (NeZero.ne n)).map _

/-- An equation at the real root holds at every conjugate; its rational coefficients are explicit. -/
theorem power_relation_conjugates (hζ : IsPrimitiveRoot ζ n) (ρ : ℝ) (k : ℤ)
    (hρ : ρ^n = (k : ℝ))
    (hirr : Irreducible ((pureBinomial n k).map (Int.castRingHom ℚ)))
    (c : ZMod n → ℤ) (m : ℕ) (A : ℚ) (s : ℤ)
    (heq : (∑ j : ZMod n, (c j : ℝ)*ρ^j.val)^m = (A : ℝ) - (s : ℝ)*ρ) :
    ∀ i : ZMod n, gammaPower ρ c ζ i ^ m = (A : ℂ) - (s : ℂ)*((ρ : ℂ)*ζ^i.val) := by
  let q : ℚ[X] := ((coefficientPolynomial c).map (Int.castRingHom ℚ))^m - C A + C (s : ℚ)*X
  have hq : aeval ρ q = 0 := by
    simp only [q,map_add,map_sub,map_pow,map_mul,aeval_C,aeval_X,eval_ratMap_real,
      coefficientPolynomial_real_eval]
    change (∑ j : ZMod n, (c j : ℝ)*ρ^j.val)^m - (A : ℝ) + ((s : ℚ) : ℝ)*ρ = 0
    simp only [Rat.cast_intCast]
    linarith [heq]
  have hd : ((pureBinomial n k).map (Int.castRingHom ℚ)) ∣ q := by
    rw [pureBinomial_eq_minpoly ρ k hρ hirr]
    exact minpoly.dvd ℚ ρ hq
  intro i
  have hf : aeval ((ρ : ℂ)*ζ^i.val) ((pureBinomial n k).map (Int.castRingHom ℚ)) = 0 := by
    rw [eval_ratMap_complex]
    simp only [pureBinomial,eval₂_sub,eval₂_pow,eval₂_X,eval₂_C,Int.coe_castRingHom,
      rootEvaluation_pow hζ ρ k hρ i,sub_self]
  have hqi : aeval ((ρ : ℂ)*ζ^i.val) q = 0 := by
    obtain ⟨p,hp⟩ := hd
    rw [hp,map_mul,hf,zero_mul]
  simp only [q,map_add,map_sub,map_pow,map_mul,aeval_C,aeval_X,eval_ratMap_complex,
    coefficientPolynomial_eval] at hqi
  change gammaPower ρ c ζ i ^ m - (A : ℂ) + ((s : ℚ) : ℂ)*((ρ : ℂ)*ζ^i.val) = 0 at hqi
  simp only [Rat.cast_intCast] at hqi
  linear_combination hqi

end PillaiConjugates
