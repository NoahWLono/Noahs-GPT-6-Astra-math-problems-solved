import PillaiPowerBasis
import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.FieldTheory.Minpoly.Field

/-! An actual integer-resultant bridge for the pure binomial and autocorrelation polynomial. -/

set_option autoImplicit false
open scoped BigOperators
open Finset Polynomial Complex
open PillaiFourier

namespace PillaiResultant

variable {n : ℕ} [NeZero n] {ζ : ℂ}

noncomputable def pureBinomial (n : ℕ) (k : ℤ) : ℤ[X] := X^n - C k

noncomputable def coefficientPolynomial (c : ZMod n → ℤ) : ℤ[X] :=
  ∑ j : ZMod n, C (c j) * X^j.val

noncomputable def autocorrelationPolynomial (c : ZMod n → ℤ) (r : ZMod n) : ℤ[X] :=
  ∑ j : ZMod n, ∑ t : ZMod n with j-t=r, C (c j*c t) * X^(j.val+t.val)

lemma autocorrelationPolynomial_eval (ρ : ℝ) (c : ZMod n → ℤ) (ζ : ℂ) (r h : ZMod n) :
    (autocorrelationPolynomial c r).eval₂ (Int.castRingHom ℂ) ((ρ : ℂ)*ζ^h.val) =
      betaPower ρ c ζ r h := by
  simp only [autocorrelationPolynomial,betaPower,eval₂_finsetSum,eval₂_mul,eval₂_C,
    eval₂_pow,eval₂_X,Int.coe_castRingHom,Int.cast_mul]

lemma coefficientPolynomial_eval (ρ : ℝ) (c : ZMod n → ℤ) (ζ : ℂ) (h : ZMod n) :
    (coefficientPolynomial c).eval₂ (Int.castRingHom ℂ) ((ρ : ℂ)*ζ^h.val) =
      gammaPower ρ c ζ h := by
  simp only [coefficientPolynomial,gammaPower,eval₂_finsetSum,eval₂_mul,eval₂_C,eval₂_pow,
    eval₂_X,Int.coe_castRingHom,mul_pow,pow_mul,mul_assoc]

/-- A nonzero value at a common root excludes divisibility by the irreducible polynomial. -/
theorem integer_resultant_ne_zero (f g : ℤ[X])
    (hirr : Irreducible (f.map (Int.castRingHom ℚ))) (x : ℂ)
    (hf : f.eval₂ (Int.castRingHom ℂ) x = 0)
    (hg : g.eval₂ (Int.castRingHom ℂ) x ≠ 0) :
    f.resultant g ≠ 0 := by
  have hcomp : (Rat.castHom ℂ).comp (Int.castRingHom ℚ) = Int.castRingHom ℂ  := by
    ext z
    change ((z : ℚ) : ℂ) = (z : ℂ)
    simp
  have hf' : (f.map (Int.castRingHom ℚ)).eval₂ (Rat.castHom ℂ) x = 0 := by
    simpa [eval₂_map,hcomp] using hf
  have hg' : (g.map (Int.castRingHom ℚ)).eval₂ (Rat.castHom ℂ) x ≠ 0 := by
    simpa [eval₂_map,hcomp] using hg
  have hcop : IsCoprime (f.map (Int.castRingHom ℚ)) (g.map (Int.castRingHom ℚ)) := by
    rcases hirr.isCoprime_or_dvd (g.map (Int.castRingHom ℚ)) with h | ⟨q,hq⟩
    · exact h
    · exfalso
      apply hg'
      rw [hq,eval₂_mul,hf',zero_mul]
  have hres := Polynomial.resultant_ne_zero _ _ hcop
  intro hz
  apply hres
  simp only [natDegree_map_eq_of_injective (f := Int.castRingHom ℚ) (by exact Int.cast_injective),
    resultant_map_map,Int.coe_castRingHom,hz,Int.cast_zero]

lemma rootEvaluations_injective (hζ : IsPrimitiveRoot ζ n) (ρ : ℝ) (hρ : ρ ≠ 0) :
    Function.Injective (fun i : ZMod n ↦ (ρ : ℂ)*ζ^i.val) := by
  intro i j hij
  apply ZMod.val_injective n
  apply hζ.pow_inj (ZMod.val_lt i) (ZMod.val_lt j)
  exact mul_left_cancel₀ (by exact_mod_cast hρ) hij

omit [NeZero n] in
lemma rootEvaluation_pow (hζ : IsPrimitiveRoot ζ n) (ρ : ℝ) (k : ℤ)
    (hρ : ρ^n = (k : ℝ)) (i : ZMod n) :
    ((ρ : ℂ)*ζ^i.val)^n = (k : ℂ) := by
  rw [mul_pow,← pow_mul, Nat.mul_comm i.val n,pow_mul,hζ.pow_eq_one,one_pow,mul_one]
  exact_mod_cast hρ

/-- The product of all root evaluations is exactly the actual integer resultant. -/
theorem pureBinomial_resultant_product (hζ : IsPrimitiveRoot ζ n) (ρ : ℝ) (k : ℤ)
    (hρ₀ : ρ ≠ 0) (hρ : ρ^n = (k : ℝ)) (g : ℤ[X]) :
    ((pureBinomial n k).resultant g : ℂ) =
      ∏ i : ZMod n, g.eval₂ (Int.castRingHom ℂ) ((ρ : ℂ)*ζ^i.val) := by
  classical
  let fC := (pureBinomial n k).map (Int.castRingHom ℂ)
  let gC := g.map (Int.castRingHom ℂ)
  let S : Finset ℂ := univ.image (fun i : ZMod n ↦ (ρ : ℂ)*ζ^i.val)
  have hinj := rootEvaluations_injective hζ ρ hρ₀
  have hcard : S.card = n := by
    simp only [S,card_image_of_injective _ hinj,card_univ,ZMod.card]
  have hmonic : fC.Monic := by
    simpa [fC,pureBinomial] using monic_X_pow_sub_C (k : ℂ) (NeZero.ne n)
  have hdeg : fC.natDegree = n := by
    simp only [fC,pureBinomial,Polynomial.map_sub,Polynomial.map_pow,Polynomial.map_X,Polynomial.map_C,Int.coe_castRingHom,natDegree_X_pow_sub_C]
  have hroots : fC.roots = S.val := by
    apply roots_eq_of_natDegree_le_card_of_ne_zero _ (by omega) hmonic.ne_zero
    intro x hx
    obtain ⟨i,_,rfl⟩ := mem_image.mp hx
    simpa [fC,pureBinomial] using sub_eq_zero.mpr (rootEvaluation_pow hζ ρ k hρ i)
  have hsplit : fC.Splits := by
    apply splits_iff_card_roots.mpr
    rw [hroots,hdeg]
    exact hcard
  have hres := resultant_eq_prod_eval fC gC g.natDegree (natDegree_map_le) hsplit
  rw [hmonic.leadingCoeff,one_pow,one_mul,hroots,Finset.prod_map_val] at hres
  dsimp only [S] at hres
  rw [Finset.prod_image] at hres
  · simpa [fC,gC,natDegree_map_eq_of_injective (f := Int.castRingHom ℂ) (by exact Int.cast_injective),
      resultant_map_map,eval_map] using hres
  · intro i _ j _ hij
    exact hinj hij

/-- A nonzero real autocorrelation value supplies a nonzero integer product of all twists. -/
theorem autocorrelation_product_integer (hζ : IsPrimitiveRoot ζ n) (ρ : ℝ) (k : ℤ)
    (hρ₀ : ρ ≠ 0) (hρ : ρ^n = (k : ℝ))
    (hirr : Irreducible ((pureBinomial n k).map (Int.castRingHom ℚ)))
    (c : ZMod n → ℤ) (r : ZMod n) (hβ : betaPower ρ c ζ r 0 ≠ 0) :
    ∃ N : ℤ, N ≠ 0 ∧ (N : ℂ) = ∏ h : ZMod n, betaPower ρ c ζ r h := by
  let g := autocorrelationPolynomial c r
  refine ⟨(pureBinomial n k).resultant g,?_,?_⟩
  · apply integer_resultant_ne_zero _ _ hirr (ρ : ℂ)
    · simp only [pureBinomial,eval₂_sub,eval₂_pow,eval₂_X,eval₂_C,Int.coe_castRingHom,
        show (ρ : ℂ)^n = (k : ℂ) by exact_mod_cast hρ,sub_self]
    · simpa [g,← autocorrelationPolynomial_eval ρ c ζ r 0] using hβ
  · rw [pureBinomial_resultant_product hζ ρ k hρ₀ hρ]
    simp only [g,autocorrelationPolynomial_eval]

end PillaiResultant
