import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Data.Nat.Choose.Dvd
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-! The finite binomial congruence supplying the strong-Hensel p-local unit alternative. -/
set_option autoImplicit false
open scoped BigOperators
open Finset
namespace PillaiFiniteHensel

/-- The higher binomial terms carry three factors of an odd prime. -/
lemma cube_dvd_binomial_term (p : ℕ) (hp : p.Prime) (hp₃ : 3≤p)
    (a t : ℤ) (j : ℕ) (hj : 2≤j) (hjp : j≤p) :
    (p : ℤ)^3 ∣ ((p : ℤ)*t)^j*a^(p-j)*(p.choose j : ℤ) := by
  by_cases hje : j=p
  · subst j
    have hd : (p : ℤ)^3 ∣ (p : ℤ)^p := pow_dvd_pow _ hp₃
    rw [mul_pow]
    exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left hd _) _) _
  · have hd : (p : ℤ) ∣ (p.choose j : ℤ) := by
      exact_mod_cast hp.dvd_choose_self (by omega : j≠0) (by omega : j<p)
    obtain ⟨v,hv⟩ := hd
    have hd₂ : (p : ℤ)^2 ∣ (p : ℤ)^j := pow_dvd_pow _ hj
    obtain ⟨w,hw⟩ := hd₂
    refine ⟨w*t^j*a^(p-j)*v,?_⟩
    rw [mul_pow,hv,hw]
    ring

/-- Exact finite congruence modulo p³, valid for every odd prime. -/
theorem prime_cube_congruence (p : ℕ) (hp : p.Prime) (hp₃ : 3≤p) (a t : ℤ) :
    (p : ℤ)^3 ∣ (a+(p : ℤ)*t)^p-a^p-(p : ℤ)^2*a^(p-1)*t := by
  have hd : (p : ℤ)^3 ∣ ∑ j ∈ Ico 2 (p+1), ((p : ℤ)*t)^j*a^(p-j)*(p.choose j : ℤ) := by
    apply dvd_sum
    intro j hj
    exact cube_dvd_binomial_term p hp hp₃ a t j (mem_Ico.mp hj).1 (Nat.le_of_lt_succ (mem_Ico.mp hj).2)
  convert hd using 1
  rw [add_comm a,add_pow,← sum_range_add_sum_Ico _ (by omega : 2≤p+1)]
  simp only [sum_range_succ,sum_range_zero,zero_add,pow_zero,one_mul,Nat.sub_zero,
    Nat.choose_zero_right,Nat.cast_one,mul_one,Nat.choose_one_right,pow_one]
  ring

/-- A unit p-th-power congruence modulo p² can be improved to one modulo p³. -/
theorem lift_square_to_cube (p : ℕ) (hp : p.Prime) (hp₃ : 3≤p) (a k : ℤ)
    (ha : ¬(p : ℤ) ∣ a) (hk : (p : ℤ)^2 ∣ k-a^p) :
    ∃ a₁ : ℤ, (p : ℤ) ∣ a₁-a ∧ ¬(p : ℤ) ∣ a₁ ∧ (p : ℤ)^3 ∣ a₁^p-k := by
  letI : Fact p.Prime := ⟨hp⟩
  have ha' : (a : ZMod p)≠0 := by
    exact fun h ↦ ha ((ZMod.intCast_zmod_eq_zero_iff_dvd a p).mp h)
  have hfer : (p : ℤ) ∣ a^(p-1)-1 := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp
    simp only [Int.cast_sub,Int.cast_pow,Int.cast_one,ZMod.pow_card_sub_one_eq_one ha',sub_self]
  obtain ⟨D,hD⟩ := hk
  obtain ⟨w,hw⟩ := hfer
  obtain ⟨v,hv⟩ := prime_cube_congruence p hp hp₃ a D
  refine ⟨a+(p : ℤ)*D,?_,?_,?_⟩
  · exact ⟨D,by ring⟩
  · intro h
    apply ha
    simpa only [add_sub_cancel_right] using dvd_sub h (dvd_mul_right (p : ℤ) D)
  · refine ⟨v+w*D,?_⟩
    linear_combination hv + ((p : ℤ)^2*D)*hw - hD

end PillaiFiniteHensel
