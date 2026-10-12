import CoefficientBounds
import FrobeniusReduction

/-! Mod-q support and the actual two-term power-basis expansion. -/
set_option autoImplicit false
open scoped BigOperators
open Finset Polynomial Complex
open PillaiFourier PillaiCoefficients PillaiFrobenius PillaiResultant
namespace PillaiSparsity
variable {n : ℕ} [NeZero n] {ζ : ℂ}

lemma integer_eq_zero_of_cast_eq_zero (q : ℕ) (a : ℤ) (ha : |(a : ℝ)|<q)
    (hz : (a : ZMod q)=0) : a=0 := by
  have hnat : a.natAbs<q := by
    have hh : (a.natAbs : ℝ)<q := by simpa only [Nat.cast_natAbs,Int.cast_abs] using ha
    exact_mod_cast hh
  apply Int.eq_zero_of_dvd_of_natAbs_lt_natAbs ((ZMod.intCast_zmod_eq_zero_iff_dvd a q).mp hz)
  simpa using hnat

/-- Frobenius and the strict coefficient bounds force support in {0,j}, where j is a unit. -/
theorem two_term_support (q : ℕ) [Fact q.Prime] (hn : 1<n) (hnq : n<q)
    (k A s : ℤ) (hk : (k : ZMod q)≠0) (c : ZMod n → ℤ)
    (hd : pureBinomial n k ∣ (coefficientPolynomial c)^q-C A+C s*X)
    (hbound : ∀ t : ZMod n,t≠0 → |(c t : ℝ)|<q) :
    ∃ j : ZMod n, IsUnit j ∧ j≠0 ∧ ∀ t : ZMod n,t≠0 → t≠j → c t=0 := by
  letI : Fact (1<n) := ⟨hn⟩
  have hcop : q.Coprime n := (Nat.Prime.coprime_iff_not_dvd (Fact.out : q.Prime)).mpr
    (Nat.not_dvd_of_pos_of_lt (NeZero.pos n) hnq)
  let u : (ZMod n)ˣ := ZMod.unitOfCoprime q hcop
  let j : ZMod n := ↑(u⁻¹)
  have hj : IsUnit j := Units.isUnit _
  have hju : j*(q : ZMod n)=1 := by
    change (↑(u⁻¹) : ZMod n)*(↑u : ZMod n)=1
    simp
  refine ⟨j,hj,hj.ne_zero,?_⟩
  intro t ht htj
  apply integer_eq_zero_of_cast_eq_zero q (c t) (hbound t ht)
  apply coefficient_cast_eq_zero q hn hcop k A s hk c hd t ht
  intro he
  apply htj
  exact ((ZMod.isUnit_iff_coprime q n).mpr hcop).mul_right_cancel (he.trans hju.symm)

/-- The support conclusion gives exactly the sparse conjugate expression. -/
theorem gammaPower_sparse (hζ : ζ^n=1) (ρ : ℝ) (c : ZMod n → ℤ) (j : ZMod n)
    (hj : j≠0) (hc : ∀ t : ZMod n,t≠0 → t≠j → c t=0) (i : ZMod n) :
    gammaPower ρ c ζ i = (c 0 : ℂ)+((c j : ℝ)*ρ^j.val : ℝ)*rootChar hζ (i*j) := by
  classical
  rw [← gamma_eq_gammaPower hζ]
  have hf (t : ZMod n) : ((weightedCoefficients ρ c t : ℂ)*rootChar hζ (i*t))=
      (if t=0 then (c 0 : ℂ) else 0)+
      (if t=j then (((c j : ℝ)*ρ^j.val : ℝ) : ℂ)*rootChar hζ (i*j) else 0) := by
    by_cases ht : t=0
    · subst t; simp [weightedCoefficients,hj.symm]
    · by_cases htj : t=j
      · subst t; simp [weightedCoefficients,hj]
      · simp [weightedCoefficients,hc t ht htj,ht,htj]
  simp only [gamma,hf,sum_add_distrib,sum_ite_eq',mem_univ,ite_true]

end PillaiSparsity
