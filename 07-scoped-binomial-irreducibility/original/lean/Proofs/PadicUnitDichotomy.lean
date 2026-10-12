import FiniteHenselCongruence
import Mathlib.NumberTheory.Padics.Hensel
import Mathlib.RingTheory.Polynomial.Eisenstein.Basic

/-!
Actual strong-Hensel lifting from finite integer congruences.
This module does not assert local extension degrees, ramification indices, or residue fields.
-/
set_option autoImplicit false
open Polynomial
open PillaiFiniteHensel
namespace PillaiPadic
variable {p : ℕ} [Fact p.Prime]

/-- A unit approximate p-th root modulo p³ satisfies the actual strict strong-Hensel inequality. -/
theorem cubic_approximation_has_root (a k : ℤ) (ha : ¬(p : ℤ) ∣ a)
    (hk : (p : ℤ)^3 ∣ a^p-k) :
    ∃ b : ℤ_[p], b^p=(k : ℤ_[p]) ∧ IsUnit b ∧
      ‖b-(a : ℤ_[p])‖<(p : ℝ)⁻¹ := by
  have hp : p.Prime := Fact.out
  have hpℝ : (1 : ℝ)<p := by exact_mod_cast hp.one_lt
  have hinv₀ : (0 : ℝ)<(p : ℝ)⁻¹ := by positivity
  have hinv₁ : (p : ℝ)⁻¹<1 := inv_lt_one_of_one_lt₀ hpℝ
  have haNorm : ‖(a : ℤ_[p])‖=1 := by
    apply le_antisymm (PadicInt.norm_le_one _)
    apply le_of_not_gt
    exact fun h ↦ ha ((PadicInt.norm_int_lt_one_iff_dvd a).mp h)
  let f : (ℤ_[p])[X] := X^p-C (k : ℤ_[p])
  have hfeval : f.aeval (a : ℤ_[p])=((a^p-k : ℤ) : ℤ_[p]) := by simp [f]
  have hder : ‖f.derivative.aeval (a : ℤ_[p])‖=(p : ℝ)⁻¹ := by
    dsimp only [f]
    rw [derivative_sub,derivative_X_pow,derivative_C,sub_zero]
    simp only [map_mul,map_natCast,map_pow,aeval_X,norm_mul,norm_pow,haNorm,one_pow,mul_one,
      PadicInt.norm_p]
  have hbound : ‖((a^p-k : ℤ) : ℤ_[p])‖≤((p : ℝ)⁻¹)^3 := by
    have hh := (PadicInt.norm_int_le_pow_iff_dvd (p := p) (k := a^p-k) (n := 3)).mpr hk
    simpa only [zpow_neg,zpow_natCast,inv_pow] using hh
  have hstrict : ‖f.aeval (a : ℤ_[p])‖<‖f.derivative.aeval (a : ℤ_[p])‖^2 := by
    rw [hfeval,hder]
    apply lt_of_le_of_lt hbound
    have hh := mul_lt_mul_of_pos_right hinv₁ (sq_pos_of_pos hinv₀)
    nlinarith
  obtain ⟨b,hb,hdist,_,_⟩ := hensels_lemma (F := f) (a := (a : ℤ_[p])) hstrict
  rw [hder] at hdist
  refine ⟨b,?_,?_,hdist⟩
  · simpa [f,sub_eq_zero] using hb
  · apply PadicInt.isUnit_iff.mpr
    have hh : ‖b+ -(a : ℤ_[p])‖<‖-(a : ℤ_[p])‖ := by
      simpa only [← sub_eq_add_neg,norm_neg,haNorm] using lt_trans hdist hinv₁
    simpa only [norm_neg,haNorm] using PadicInt.norm_eq_of_norm_add_lt_right hh

/-- Every unit p-th-power congruence modulo p² lifts to an actual p-adic unit root. -/
theorem square_congruence_has_root (hp₃ : 3≤p) (a k : ℤ) (ha : ¬(p : ℤ) ∣ a)
    (hk : (p : ℤ)^2 ∣ k-a^p) : ∃ b : ℤ_[p], b^p=(k : ℤ_[p]) ∧ IsUnit b := by
  obtain ⟨a₁,_,ha₁,hk₁⟩ := lift_square_to_cube p Fact.out hp₃ a k ha hk
  obtain ⟨b,hb,hub,_⟩ := cubic_approximation_has_root a₁ k ha₁ hk₁
  exact ⟨b,hb,hub⟩

/-- The nonsplit arithmetic alternative is the actual Eisenstein predicate. -/
theorem translated_eisenstein (a k : ℤ) (hconst : (p : ℤ) ∣ a^p-k)
    (hconst₂ : ¬(p : ℤ)^2 ∣ a^p-k) :
    (((X : ℤ[X])+C a)^p-C k).IsEisensteinAt (Ideal.span {(p : ℤ)}) := by
  have hp : p.Prime := Fact.out
  have hmonic : (((X : ℤ[X])+C a)^p-C k).Monic := by
    apply ((monic_X_add_C a).pow p).sub_of_left
    apply degree_C_le.trans_lt
    rw [degree_eq_natDegree ((monic_X_add_C a).pow p).ne_zero,natDegree_pow_X_add_C]
    exact WithBot.coe_lt_coe.mpr hp.pos
  have hdeg : (((X : ℤ[X])+C a)^p-C k).natDegree=p := by
    simp only [natDegree_sub_C,natDegree_pow_X_add_C]
  refine ⟨?_,?_,?_⟩
  · rw [hmonic.leadingCoeff,Ideal.mem_span_singleton]
    intro h
    have hh := (ZMod.intCast_zmod_eq_zero_iff_dvd 1 p).mpr h
    simp at hh
  · intro j hj
    rw [hdeg] at hj
    rw [Ideal.mem_span_singleton,coeff_sub,coeff_X_add_C_pow,coeff_C]
    by_cases hj₀ : j=0
    · simpa [hj₀] using hconst
    · simp only [hj₀,ite_false,sub_zero]
      apply dvd_mul_of_dvd_right
      exact_mod_cast hp.dvd_choose_self hj₀ hj
  · rw [Ideal.span_singleton_pow,Ideal.mem_span_singleton,coeff_sub,coeff_X_add_C_pow]
    simpa using hconst₂

/-- A unit residue gives an actual translated-Eisenstein or p-adic-unit-root alternative. -/
theorem unit_dichotomy (hp₃ : 3≤p) (a k : ℤ) (ha : ¬(p : ℤ) ∣ a)
    (hres : (a : ZMod p)=(k : ZMod p)) :
    (((X : ℤ[X])+C a)^p-C k).IsEisensteinAt (Ideal.span {(p : ℤ)}) ∨
      ∃ b : ℤ_[p], b^p=(k : ℤ_[p]) ∧ IsUnit b := by
  by_cases h : (p : ℤ)^2 ∣ k-a^p
  · exact Or.inr (square_congruence_has_root hp₃ a k ha h)
  · left
    apply translated_eisenstein a k
    · apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp
      simp only [Int.cast_sub,Int.cast_pow,ZMod.pow_card,hres,sub_self]
    · intro hh
      apply h
      simpa only [neg_sub] using dvd_neg.mpr hh

/-- In particular, one may use the integer k itself as the initial residue representative. -/
theorem unit_dichotomy_self (hp₃ : 3≤p) (k : ℤ) (hk : ¬(p : ℤ) ∣ k) :
    (((X : ℤ[X])+C k)^p-C k).IsEisensteinAt (Ideal.span {(p : ℤ)}) ∨
      ∃ b : ℤ_[p], b^p=(k : ℤ_[p]) ∧ IsUnit b :=
  unit_dichotomy hp₃ k k hk rfl

/-- The same translated polynomial is Eisenstein over Z_p itself, not only over Z. -/
theorem translated_eisenstein_padic (a k : ℤ) (hconst : (p : ℤ) ∣ a^p-k)
    (hconst₂ : ¬(p : ℤ)^2 ∣ a^p-k) :
    (((X : (ℤ_[p])[X])+C (a : ℤ_[p]))^p-C (k : ℤ_[p])).IsEisensteinAt
      (Ideal.span {(p : ℤ_[p])}) := by
  have hp : p.Prime := Fact.out
  have hmonic : (((X : (ℤ_[p])[X])+C (a : ℤ_[p]))^p-C (k : ℤ_[p])).Monic := by
    apply ((monic_X_add_C _).pow p).sub_of_left
    apply degree_C_le.trans_lt
    rw [degree_eq_natDegree ((monic_X_add_C _).pow p).ne_zero,natDegree_pow_X_add_C]
    exact WithBot.coe_lt_coe.mpr hp.pos
  have hdeg : (((X : (ℤ_[p])[X])+C (a : ℤ_[p]))^p-C (k : ℤ_[p])).natDegree=p := by
    simp only [natDegree_sub_C,natDegree_pow_X_add_C]
  refine ⟨?_,?_,?_⟩
  · rw [hmonic.leadingCoeff,Ideal.mem_span_singleton]
    intro h
    exact PadicInt.p_nonunit (isUnit_iff_dvd_one.mpr h)
  · intro j hj
    rw [hdeg] at hj
    rw [Ideal.mem_span_singleton,coeff_sub,coeff_X_add_C_pow,coeff_C]
    by_cases hj₀ : j=0
    · simp only [hj₀,Nat.sub_zero,Nat.choose_zero_right,Nat.cast_one,mul_one,ite_true]
      have hh := (PadicInt.pow_p_dvd_int_iff (p := p) 1 (a^p-k)).mpr (by simpa using hconst)
      simpa only [pow_one,Int.cast_sub,Int.cast_pow] using hh
    · simp only [hj₀,ite_false,sub_zero]
      apply dvd_mul_of_dvd_right
      obtain ⟨v,hv⟩ := hp.dvd_choose_self hj₀ hj
      exact ⟨(v : ℤ_[p]),by exact_mod_cast hv⟩
  · rw [Ideal.span_singleton_pow,Ideal.mem_span_singleton,coeff_sub,coeff_X_add_C_pow]
    simp only [Nat.sub_zero,Nat.choose_zero_right,Nat.cast_one,mul_one,coeff_C_zero]
    simpa only [Int.cast_sub,Int.cast_pow] using
      (PadicInt.pow_p_dvd_int_iff (p := p) 2 (a^p-k)).not.mpr hconst₂

/-- The actual Z_p polynomial alternative used by the local order argument. -/
theorem padic_unit_dichotomy (hp₃ : 3≤p) (a k : ℤ) (ha : ¬(p : ℤ) ∣ a)
    (hres : (a : ZMod p)=(k : ZMod p)) :
    (((X : (ℤ_[p])[X])+C (a : ℤ_[p]))^p-C (k : ℤ_[p])).IsEisensteinAt
        (Ideal.span {(p : ℤ_[p])}) ∨
      ∃ b : ℤ_[p], b^p=(k : ℤ_[p]) ∧ IsUnit b := by
  by_cases h : (p : ℤ)^2 ∣ k-a^p
  · exact Or.inr (square_congruence_has_root hp₃ a k ha h)
  · left
    apply translated_eisenstein_padic a k
    · apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp
      simp only [Int.cast_sub,Int.cast_pow,ZMod.pow_card,hres,sub_self]
    · intro hh
      apply h
      simpa only [neg_sub] using dvd_neg.mpr hh

/-- The Eisenstein alternative cannot simultaneously have a p-adic integer p-th root. -/
theorem translated_eisenstein_no_root (a k : ℤ)
    (he : (((X : (ℤ_[p])[X])+C (a : ℤ_[p]))^p-C (k : ℤ_[p])).IsEisensteinAt
      (Ideal.span {(p : ℤ_[p])})) : ¬∃ b : ℤ_[p], b^p=(k : ℤ_[p]) := by
  have hp : p.Prime := Fact.out
  let f : (ℤ_[p])[X] := (X+C (a : ℤ_[p]))^p-C (k : ℤ_[p])
  have hmonic : f.Monic := by
    apply ((monic_X_add_C _).pow p).sub_of_left
    apply degree_C_le.trans_lt
    rw [degree_eq_natDegree ((monic_X_add_C _).pow p).ne_zero,natDegree_pow_X_add_C]
    exact WithBot.coe_lt_coe.mpr hp.pos
  have hdeg : f.natDegree=p := by simp only [f,natDegree_sub_C,natDegree_pow_X_add_C]
  have hprime : (Ideal.span {(p : ℤ_[p])}).IsPrime := by
    rw [← PadicInt.maximalIdeal_eq_span_p]
    infer_instance
  have hirr : Irreducible f := he.irreducible hprime hmonic.isPrimitive (by rw [hdeg]; exact hp.pos)
  rintro ⟨b,hb⟩
  apply hirr.not_isRoot_of_natDegree_ne_one (by rw [hdeg]; exact hp.ne_one)
    (x := b-(a : ℤ_[p]))
  simp only [f,IsRoot,eval_sub,eval_pow,eval_add,eval_X,eval_C,sub_add_cancel,hb,sub_self]

/-- Exact arithmetic criterion for a p-adic unit p-th root, with both directions proved. -/
theorem unit_root_iff_square_congruence (hp₃ : 3≤p) (a k : ℤ) (ha : ¬(p : ℤ) ∣ a)
    (hres : (a : ZMod p)=(k : ZMod p)) :
    (∃ b : ℤ_[p], b^p=(k : ℤ_[p]) ∧ IsUnit b) ↔ (p : ℤ)^2 ∣ k-a^p := by
  constructor
  · rintro ⟨b,hb,_⟩
    by_contra h
    have he := translated_eisenstein_padic (p := p) a k (by
      apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp
      simp only [Int.cast_sub,Int.cast_pow,ZMod.pow_card,hres,sub_self]) (by
        intro hh
        apply h
        simpa only [neg_sub] using dvd_neg.mpr hh)
    exact translated_eisenstein_no_root a k he ⟨b,hb⟩
  · exact square_congruence_has_root hp₃ a k ha

end PillaiPadic
