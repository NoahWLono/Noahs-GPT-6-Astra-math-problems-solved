import PowerSamples
import Mathlib.RingTheory.RootsOfUnity.Complex

/-!
The standalone large-height exclusion for an integral power-basis element.
Every finite Fourier, analytic, conjugacy, integrality, and product obligation is discharged.
This does not assert the local order lemma or the full shifted-binomial irreducibility theorem.
-/

set_option autoImplicit false
open scoped BigOperators
open Finset Polynomial Complex
open PillaiFourier PillaiResultant PillaiConjugates PillaiHeight PillaiSamples

namespace PillaiLargeHeight

variable {n : ℕ} [NeZero n] {ζ : ℂ}

/-- The complete large-height exclusion, first with an arbitrary supplied primitive root. -/
theorem exclusion_with_primitive_root (hζ : IsPrimitiveRoot ζ n) (hn : 5 ≤ n)
    (m : ℕ) (hm : n<m) (k : ℤ) (hk : 1<k) (ρ : ℝ) (hρ₀ : 0<ρ)
    (hρpow : ρ^n=(k : ℝ))
    (hirr : Irreducible ((pureBinomial n k).map (Int.castRingHom ℚ)))
    (c : ZMod n → ℤ) (A : ℚ) (hA : 0<A) (s : ℤ) (hs : s=1 ∨ s= -1)
    (heq : (∑ j : ZMod n, (c j : ℝ)*ρ^j.val)^m = (A : ℝ)-(s : ℝ)*ρ) :
    (A : ℝ)+ρ < ((m : ℝ)*ρ)^m := by
  have hAℝ : (0 : ℝ)<A := by exact_mod_cast hA
  have hkℝ : (1 : ℝ)<k := by exact_mod_cast hk
  have hρ : 1<ρ := by
    by_contra h
    have hle : ρ≤1 := le_of_not_gt h
    have hp : ρ^n≤(1 : ℝ)^n := by gcongr
    simp only [one_pow,hρpow] at hp
    linarith
  have hm₀ : m≠0 := by omega
  have hsℝ : (s : ℝ)=1 ∨ (s : ℝ)= -1 := by
    rcases hs with rfl | rfl <;> simp
  have hsabs : |(s : ℝ)|=1 := by rcases hsℝ with h | h <;> rw [h] <;> norm_num
  by_contra hneg
  have hheight : ((m : ℝ)*ρ)^m ≤ (A : ℝ)+ρ := le_of_not_gt hneg
  have hu := height_ratio_bound m (by omega) ρ (A : ℝ) hρ hAℝ hheight
  let R : ℝ := ((A : ℝ)+ρ)^((m : ℝ)⁻¹)
  let S : ℝ := (A : ℝ)^((m : ℝ)⁻¹)
  have hR : 0<R := Real.rpow_pos_of_pos (by positivity) _
  have hS : 0<S := Real.rpow_pos_of_pos hAℝ _
  have hRm : R^m=(A : ℝ)+ρ := Real.rpow_inv_natCast_pow (by positivity) hm₀
  have hSm : S^m=(A : ℝ) := Real.rpow_inv_natCast_pow hAℝ.le hm₀
  have hRge : (m : ℝ)*ρ ≤ R := by
    apply (pow_le_pow_iff_left₀ (by positivity) hR.le hm₀).mp
    simpa only [hRm] using hheight
  have hSR : S≤R := by
    apply (pow_le_pow_iff_left₀ hS.le hR.le hm₀).mp
    rw [hSm,hRm]
    linarith
  have hconj : ∀ i : ZMod n, gammaPower ρ c ζ i ^ m =
      ((A : ℝ) : ℂ)-((s : ℝ) : ℂ)*(ρ : ℂ)*rootChar hζ.pow_eq_one i := by
    intro i
    simpa [rootChar,mul_assoc] using power_relation_conjugates hζ ρ k hρpow hirr c m A s heq i
  have hsmall := beta_zero_small hζ hn m hm ρ (A : ℝ) R S (s : ℝ) hAℝ hR.le hS
    hSm hSR hsℝ hu.1 hu.2.1 c hconj
  have hall := beta_all_bound hζ m hm₀ ρ (A : ℝ) R (s : ℝ) hAℝ.le hρ₀.le hR.le hRm
    hsabs c hconj
  have hprod := product_norm_lt_one m hn hm ρ (A : ℝ) R hρ hAℝ hR hRm hRge
    (fun h ↦ betaPower ρ c ζ 2 h) hall hsmall.2
  obtain ⟨N,hN,hNeq⟩ := autocorrelation_product_integer hζ ρ k hρ₀.ne' hρpow hirr c 2
    (norm_pos_iff.mp hsmall.1)
  have hlarge := one_le_norm_intCast N hN
  rw [hNeq] at hlarge
  linarith

/-- No primitive-root assumption is needed: the standard complex root supplies it. -/
theorem large_height_exclusion (hn : 5 ≤ n) (m : ℕ) (hm : n<m)
    (k : ℤ) (hk : 1<k) (ρ : ℝ) (hρ₀ : 0<ρ) (hρpow : ρ^n=(k : ℝ))
    (hirr : Irreducible ((X : ℚ[X])^n-C (k : ℚ)))
    (c : ZMod n → ℤ) (A : ℚ) (hA : 0<A) (s : ℤ) (hs : s=1 ∨ s= -1)
    (heq : (∑ j : ZMod n, (c j : ℝ)*ρ^j.val)^m = (A : ℝ)-(s : ℝ)*ρ) :
    (A : ℝ)+ρ < ((m : ℝ)*ρ)^m := by
  apply exclusion_with_primitive_root (Complex.isPrimitiveRoot_exp n (NeZero.ne n)) hn m hm
    k hk ρ hρ₀ hρpow _ c A hA s hs heq
  simpa [pureBinomial] using hirr

omit [NeZero n] in
/-- Public finite-index version: the only hypotheses are the natural arithmetic data and equation. -/
theorem large_height_exclusion_fin (n m : ℕ) (hn : 5 ≤ n) (hm : n<m)
    (k : ℤ) (hk : 1<k) (ρ : ℝ) (hρ₀ : 0<ρ) (hρpow : ρ^n=(k : ℝ))
    (hirr : Irreducible ((X : ℚ[X])^n-C (k : ℚ)))
    (c : Fin n → ℤ) (A : ℚ) (hA : 0<A) (s : ℤ) (hs : s=1 ∨ s= -1)
    (heq : (∑ j : Fin n, (c j : ℝ)*ρ^j.val)^m = (A : ℝ)-(s : ℝ)*ρ) :
    (A : ℝ)+ρ < ((m : ℝ)*ρ)^m := by
  letI : NeZero n := ⟨by omega⟩
  let cZ : ZMod n → ℤ := fun j ↦ c ((ZMod.finEquiv n).symm j)
  have hval (j : Fin n) : (ZMod.finEquiv n j).val=j.val := by
    cases n with
    | zero => exact Fin.elim0 j
    | succ n => rfl
  have hsum : (∑ j : ZMod n, (cZ j : ℝ)*ρ^j.val) = ∑ j : Fin n, (c j : ℝ)*ρ^j.val := by
    symm
    refine Fintype.sum_equiv (ZMod.finEquiv n).toEquiv _ _ ?_
    intro j
    simp only [cZ,RingEquiv.toEquiv_eq_coe,RingEquiv.coe_toEquiv,
      RingEquiv.symm_apply_apply,hval]
  apply large_height_exclusion hn m hm k hk ρ hρ₀ hρpow hirr cZ A hA s hs
  rw [hsum]
  exact heq

end PillaiLargeHeight
