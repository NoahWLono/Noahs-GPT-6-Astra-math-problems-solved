import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.Algebra.Polynomial.Identities
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.Tactic.LinearCombination

/-! Finite fixed-derivative Newton descent into an actual subring through an ideal conductor. -/
set_option autoImplicit false
open Polynomial
namespace PillaiFiniteNewton
universe u
variable {S : Type u} [CommRing S]

/-- One fixed-derivative Newton step gains one ideal power; no local or completeness hypothesis. -/
lemma fixed_newton_gain (I : Ideal S) (f : S[X]) (x a a₀ d : S) (r : ℕ) (hr : 1≤r)
    (hroot : f.eval x=0) (hclose : x-a₀∈I) (he : x-a∈I^r)
    (hd : d*f.derivative.eval a₀=1) :
    x-(a-d*f.eval a)∈I^(r+1) := by
  have heI : x-a∈I := by
    have hh := Ideal.pow_le_pow_right hr he
    simpa only [pow_one] using hh
  have ha : a-a₀∈I := by
    convert I.sub_mem hclose heI using 1
    ring
  obtain ⟨c,hc⟩ := f.derivative.evalSubFactor a a₀
  have hder : f.derivative.eval a-f.derivative.eval a₀∈I := by
    rw [hc]
    exact I.mul_mem_left c ha
  have hcoef : 1-d*f.derivative.eval a∈I := by
    convert I.neg_mem (I.mul_mem_left d hder) using 1
    linear_combination -hd
  have hfirst : (1-d*f.derivative.eval a)*(x-a)∈I^(r+1) := by
    rw [pow_succ']
    exact Ideal.mul_mem_mul hcoef he
  have hsq : (x-a)^2∈I^(r+1) := by
    rw [pow_two,pow_succ']
    exact Ideal.mul_mem_mul heI he
  obtain ⟨H,hH⟩ := exists_mul_sq_add_linear_part_eq_eval_add f a (x-a)
  rw [add_sub_cancel,hroot] at hH
  have hid : x-(a-d*f.eval a)=
      (1-d*f.derivative.eval a)*(x-a)-d*H*(x-a)^2 := by
    linear_combination d*hH
  rw [hid]
  exact (I^(r+1)).sub_mem hfirst ((I^(r+1)).mul_mem_left (d*H) hsq)

/-- An existing simple root descends into a subring after finitely many fixed-derivative steps. -/
theorem finite_newton_descent (R : Subring S) (I : Ideal S) (N : ℕ) (hN : 1≤N)
    (hconductor : ∀ z : S,z∈I^N → z∈R) (f : R[X]) (x : S) (a₀ : R)
    (hroot : f.eval₂ R.subtype x=0) (hclose : x-(a₀ : S)∈I)
    (hder : IsUnit (f.derivative.eval a₀)) : x∈R := by
  let u : Rˣ := hder.unit
  let d : R := ↑(u⁻¹)
  have hd : d*f.derivative.eval a₀=1 := by
    rw [← hder.unit_spec]
    exact Units.inv_mul u
  let a : ℕ → R := fun n ↦ Nat.recOn n a₀ (fun _ b ↦ b-d*f.eval b)
  have hstep (n : ℕ) : a (n+1)=a n-d*f.eval (a n) := rfl
  let F : S[X] := f.map R.subtype
  have heval (b : R) : F.eval (b : S)=(f.eval b : R) := by
    rw [eval_map]
    exact eval₂_at_apply R.subtype b
  have hdev (b : R) : F.derivative.eval (b : S)=(f.derivative.eval b : R) := by
    rw [derivative_map,eval_map]
    exact eval₂_at_apply R.subtype b
  have hFroot : F.eval x=0 := by simpa only [F,eval_map] using hroot
  have hFd : (d : S)*F.derivative.eval (a₀ : S)=1 := by
    rw [hdev]
    exact_mod_cast hd
  have herror (n : ℕ) : x-R.subtype (a n)∈I^(n+1) := by
    induction n with
    | zero => simpa only [a,pow_one,Nat.rec_zero,Nat.zero_add,Subring.subtype_apply] using hclose
    | succ n ih =>
      have hh := fixed_newton_gain I F x (R.subtype (a n)) (a₀ : S) (d : S) (n+1)
        (by omega) hFroot hclose ih hFd
      rw [hstep,map_sub,map_mul]
      simpa only [Subring.subtype_apply,heval] using hh
  have hlast : x-R.subtype (a (N-1))∈R := hconductor _ (by
    have hh := herror (N-1)
    simpa only [Nat.sub_add_cancel hN] using hh)
  have hh := R.add_mem hlast (a (N-1)).property
  simpa only [Subring.subtype_apply,sub_add_cancel] using hh

/-- Power-root specialization with both invertibility hypotheses discharged inside the subring. -/
theorem finite_power_root_descent (R : Subring S) (I : Ideal S) (N : ℕ) (hN : 1≤N)
    (hconductor : ∀ z : S,z∈I^N → z∈R) (q : ℕ) (u a₀ : R) (x : S)
    (hroot : x^q=(u : S)) (hclose : x-(a₀ : S)∈I)
    (hq : IsUnit (q : R)) (ha : IsUnit a₀) : x∈R := by
  apply finite_newton_descent R I N hN hconductor ((X : R[X])^q-C u) x a₀
  · simpa only [eval₂_sub,eval₂_pow,eval₂_X,eval₂_C,Subring.subtype_apply,sub_eq_zero] using hroot
  · exact hclose
  · rw [derivative_sub,derivative_X_pow,derivative_C,sub_zero,eval_mul,eval_C,eval_pow,eval_X]
    exact hq.mul (ha.pow (q-1))

end PillaiFiniteNewton
