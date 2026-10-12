import IntegralSparsity
import SparseCircle
import LargeHeightExclusion

/-!
Complete integral-power-order exclusion for arbitrary degree n≥5 and prime q>n.
No restriction q∤k is needed. This theorem assumes an actual integral power-basis expression;
it does not prove a local descent to Z[ρ] or assert the full irreducibility theorem.
-/
set_option autoImplicit false
open scoped BigOperators
open Finset Polynomial Complex
open PillaiFourier PillaiResultant PillaiConjugates PillaiCoefficients PillaiFrobenius
open PillaiSparsity PillaiSparseCircle PillaiLargeHeight
namespace PillaiIntegralPowerOrder
variable {n : ℕ} [NeZero n] {ζ : ℂ}

/-- The natural power-order exclusion, first with a supplied primitive complex root. -/
theorem exclusion_with_primitive_root (hζ : IsPrimitiveRoot ζ n) (hn : 5≤n)
    (q : ℕ) (hq : q.Prime) (hnq : n<q) (k : ℤ) (hk : 1<k)
    (ρ : ℝ) (hρ₀ : 0<ρ) (hρpow : ρ^n=(k : ℝ))
    (hirr : Irreducible ((pureBinomial n k).map (Int.castRingHom ℚ)))
    (c : ZMod n → ℤ) (A : ℤ) (hA : 0<A) (s : ℤ) (hs : s=1 ∨ s= -1) :
    (∑ j : ZMod n, (c j : ℝ)*ρ^j.val)^q ≠ (A : ℝ)-(s : ℝ)*ρ := by
  intro heq
  letI : Fact q.Prime := ⟨hq⟩
  have hd := integer_relation_dvd ρ k hρpow hirr c q A s heq
  by_cases hkq : (k : ZMod q)=0
  · exact no_relation_of_cast_k_zero q (by omega) hnq k A s hkq hs c hd
  have hAℝ : (0 : ℝ)<A := by exact_mod_cast hA
  have hAℚ : (0 : ℚ)<A := by exact_mod_cast hA
  have hkℝ : (1 : ℝ)<k := by exact_mod_cast hk
  have hρ : 1<ρ := by
    by_contra h
    have hle : ρ≤1 := le_of_not_gt h
    have hp : ρ^n≤(1 : ℝ)^n := by gcongr
    simp only [one_pow,hρpow] at hp
    linarith
  have hsℝ : (s : ℝ)=1 ∨ (s : ℝ)= -1 := by
    rcases hs with rfl | rfl <;> simp
  have hsabs : |(s : ℝ)|=1 := by rcases hsℝ with h | h <;> rw [h] <;> norm_num
  have heqℚ : (∑ j : ZMod n, (c j : ℝ)*ρ^j.val)^q=((A : ℚ) : ℝ)-(s : ℝ)*ρ := by
    simpa only [Rat.cast_intCast] using heq
  have hstrip : (A : ℝ)+ρ<((q : ℝ)*ρ)^q := by
    simpa only [Rat.cast_intCast] using
      PillaiLargeHeight.exclusion_with_primitive_root hζ hn q hnq k hk ρ hρ₀ hρpow
        hirr c (A : ℚ) hAℚ s hs heqℚ
  have hconj : ∀ i : ZMod n, gammaPower ρ c ζ i ^ q =
      ((A : ℝ) : ℂ)-((s : ℝ) : ℂ)*(ρ : ℂ)*rootChar hζ.pow_eq_one i := by
    intro i
    simpa [rootChar,mul_assoc] using
      power_relation_conjugates hζ ρ k hρpow hirr c q (A : ℚ) s heqℚ i
  let R : ℝ := ((A : ℝ)+ρ)^((q : ℝ)⁻¹)
  have hR : 0<R := Real.rpow_pos_of_pos (by positivity) _
  have hRq : R^q=(A : ℝ)+ρ := Real.rpow_inv_natCast_pow (by positivity) hq.ne_zero
  have hbound (j : ZMod n) (hj : j≠0) : |(c j : ℝ)|<q :=
    strip_coefficient_lt hζ q hq.pos ρ (A : ℝ) R (s : ℝ) hρ hAℝ.le hR.le hRq
      hstrip hsabs c hconj j hj
  obtain ⟨j,hj,hj₀,hc⟩ := two_term_support q (by omega) hnq k A s hkq c hd hbound
  apply sparse_power_impossible hζ hn q (by omega) j hj (c 0 : ℝ)
    ((c j : ℝ)*ρ^j.val) (A : ℝ) ρ (s : ℝ) hAℝ hρ₀ hsℝ
  intro i
  have hh := hconj i
  rw [gammaPower_sparse hζ.pow_eq_one ρ c j hj₀ hc i] at hh
  simpa only [Complex.ofReal_intCast] using hh

/-- Arbitrary n≥5, prime q>n, and every integral coefficient vector. -/
theorem integral_power_order_exclusion (hn : 5≤n) (q : ℕ) (hq : q.Prime) (hnq : n<q)
    (k : ℤ) (hk : 1<k) (ρ : ℝ) (hρ₀ : 0<ρ) (hρpow : ρ^n=(k : ℝ))
    (hirr : Irreducible ((X : ℚ[X])^n-C (k : ℚ)))
    (c : ZMod n → ℤ) (A : ℤ) (hA : 0<A) (s : ℤ) (hs : s=1 ∨ s= -1) :
    (∑ j : ZMod n, (c j : ℝ)*ρ^j.val)^q ≠ (A : ℝ)-(s : ℝ)*ρ := by
  apply exclusion_with_primitive_root (Complex.isPrimitiveRoot_exp n (NeZero.ne n))
    hn q hq hnq k hk ρ hρ₀ hρpow _ c A hA s hs
  simpa [pureBinomial] using hirr

omit [NeZero n] in
/-- Public Fin n formulation. All Fourier, Frobenius, order, and convexity obligations are proved. -/
theorem integral_power_order_exclusion_fin (n q : ℕ) (hn : 5≤n) (hq : q.Prime) (hnq : n<q)
    (k : ℤ) (hk : 1<k) (ρ : ℝ) (hρ₀ : 0<ρ) (hρpow : ρ^n=(k : ℝ))
    (hirr : Irreducible ((X : ℚ[X])^n-C (k : ℚ)))
    (c : Fin n → ℤ) (A : ℤ) (hA : 0<A) (s : ℤ) (hs : s=1 ∨ s= -1) :
    (∑ j : Fin n, (c j : ℝ)*ρ^j.val)^q ≠ (A : ℝ)-(s : ℝ)*ρ := by
  letI : NeZero n := ⟨by omega⟩
  let cZ : ZMod n → ℤ := fun j ↦ c ((ZMod.finEquiv n).symm j)
  have hval (j : Fin n) : (ZMod.finEquiv n j).val=j.val := by
    cases n with
    | zero => exact Fin.elim0 j
    | succ n => rfl
  have hsum : (∑ j : ZMod n, (cZ j : ℝ)*ρ^j.val)=∑ j : Fin n, (c j : ℝ)*ρ^j.val := by
    symm
    refine Fintype.sum_equiv (ZMod.finEquiv n).toEquiv _ _ ?_
    intro j
    simp only [cZ,RingEquiv.toEquiv_eq_coe,RingEquiv.coe_toEquiv,
      RingEquiv.symm_apply_apply,hval]
  have hh := integral_power_order_exclusion hn q hq hnq k hk ρ hρ₀ hρpow hirr cZ A hA s hs
  simpa only [hsum] using hh

end PillaiIntegralPowerOrder
