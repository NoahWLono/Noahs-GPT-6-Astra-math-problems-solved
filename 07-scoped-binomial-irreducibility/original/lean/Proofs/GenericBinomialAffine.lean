import GenericBinomialResidue
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic

/-!
Elaborated with pinned Lean 4.32.2 and mathlib commit
905b95818eb32af7874a58b427f50c1711a5e96c. See the adjacent clean-build evidence.
Generic affine nonvanishing/nondivisibility, then explicit local-ring unit conclusions.
-/

set_option autoImplicit false
noncomputable section

namespace PillaiParameterC

universe u
variable {D : Type u} [CommRing D]

/-- Vanishing residue and m >= n force the m-th power into ell*S. -/
lemma scalar_ell_dvd_pow_of_residue_eq_zero (ell v : D) {n m : ℕ}
    (hn : 0 < n) (hv : IsUnit v) (hnm : n ≤ m) (x : Order ell v n)
    (hx : residue ell v hn x = 0) : scalar ell v n ell ∣ x ^ m := by
  have ht : tau ell v n ∣ x :=
    Ideal.mem_span_singleton.mp ((residue_eq_zero_iff ell v hn hv x).mp hx)
  have htn : tau ell v n ^ n ∣ x ^ m := pow_dvd_pow_of_dvd_of_le ht hnm
  have he : scalar ell v n ell ∣ tau ell v n ^ n := by
    rw [tau_pow, map_mul]
    exact dvd_mul_right _ _
  exact he.trans htn

section General
variable [Nontrivial D]

/-- The affine equation already forces nonzero residue of x over an arbitrary
commutative base ring. Reducedness of the residue ring is not needed here. -/
theorem affine_residue_ne_zero (ell v : D) {n m r : ℕ}
    (hell : ¬ IsUnit ell) (hv : IsUnit v) (hr : 0 < r) (hrn : r < n)
    (hnm : n ≤ m) (c A : D) (hc : IsUnit c) (x : Order ell v n)
    (hx : x ^ m = scalar ell v n A - scalar ell v n c * tau ell v n ^ r) :
    residue ell v (hr.trans hrn) x ≠ 0 := by
  intro hx0
  have hdiv := scalar_ell_dvd_pow_of_residue_eq_zero ell v (hr.trans hrn) hv hnm x hx0
  have hneg : scalar ell v n c * tau ell v n ^ r - scalar ell v n A = -(x ^ m) := by
    rw [hx, neg_sub]
  apply scalar_ell_not_dvd_unit_monomial_sub_scalar ell v hell hr hrn c A hc
  rw [hneg]
  exact dvd_neg.mpr hdiv

/-- Generic scalar conclusion: ell does not divide A. Reducedness is sufficient
for this proof to pass from a zero power of the residue to zero residue. -/
theorem affine_scalar_not_dvd (ell v : D) {n m r : ℕ}
    [IsReduced (D ⧸ Ideal.span ({ell} : Set D))]
    (hell : ¬ IsUnit ell) (hv : IsUnit v) (hr : 0 < r) (hrn : r < n)
    (hnm : n ≤ m) (c A : D) (hc : IsUnit c) (x : Order ell v n)
    (hx : x ^ m = scalar ell v n A - scalar ell v n c * tau ell v n ^ r) :
    ¬ ell ∣ A := by
  intro hA
  have hA0 : Ideal.Quotient.mk (Ideal.span ({ell} : Set D)) A = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton.mpr hA)
  have hp : residue ell v (hr.trans hrn) x ^ m = 0 := by
    have h := congrArg (residue ell v (hr.trans hrn)) hx
    simpa only [map_pow, map_sub, map_mul, residue_scalar, residue_tau,
      zero_pow (Nat.ne_of_gt hr), mul_zero, sub_zero, hA0] using h
  exact affine_residue_ne_zero ell v hell hv hr hrn hnm c A hc x hx
    (eq_zero_of_pow_eq_zero hp)

/-- Prime-ideal formulation, with reducedness provided by the actual quotient domain. -/
theorem affine_scalar_not_dvd_of_prime (ell v : D) {n m r : ℕ}
    [hprime : (Ideal.span ({ell} : Set D)).IsPrime]
    (hv : IsUnit v) (hr : 0 < r) (hrn : r < n) (hnm : n ≤ m)
    (c A : D) (hc : IsUnit c) (x : Order ell v n)
    (hx : x ^ m = scalar ell v n A - scalar ell v n c * tau ell v n ^ r) :
    ¬ ell ∣ A := by
  have hell : ¬ IsUnit ell := by
    intro hu
    exact hprime.ne_top (Ideal.span_singleton_eq_top.mpr hu)
  exact affine_scalar_not_dvd ell v hell hv hr hrn hnm c A hc x hx

end General

section Local

variable [IsLocalRing D]

/-- This is exactly the local/DVR hypothesis needed for the unit conclusions below. -/
lemma not_isUnit_of_maximalIdeal_eq_span (ell : D)
    (hmax : IsLocalRing.maximalIdeal D = Ideal.span ({ell} : Set D)) : ¬ IsUnit ell := by
  intro hu
  have hmem : ell ∈ IsLocalRing.maximalIdeal D := by
    rw [hmax]
    exact Ideal.mem_span_singleton_self ell
  exact (IsLocalRing.notMem_maximalIdeal.mpr hu) hmem

/-- The paper's unit conclusion, with the local hypothesis made explicit.
A DVR with chosen uniformizer ell supplies hmax; no valuation on S is involved. -/
theorem affine_scalar_isUnit (ell v : D) {n m r : ℕ}
    (hmax : IsLocalRing.maximalIdeal D = Ideal.span ({ell} : Set D))
    (hv : IsUnit v) (hr : 0 < r) (hrn : r < n) (hnm : n ≤ m)
    (c A : D) (hc : IsUnit c) (x : Order ell v n)
    (hx : x ^ m = scalar ell v n A - scalar ell v n c * tau ell v n ^ r) :
    IsUnit A := by
  letI : (Ideal.span ({ell} : Set D)).IsMaximal := by
    rw [← hmax]
    infer_instance
  apply IsLocalRing.notMem_maximalIdeal.mp
  rw [hmax, Ideal.mem_span_singleton]
  exact affine_scalar_not_dvd_of_prime ell v hv hr hrn hnm c A hc x hx

/-- Every scalar lift of the affine root's residue is a base-ring unit. -/
theorem affine_scalar_lift_isUnit (ell v : D) {n m r : ℕ}
    (hmax : IsLocalRing.maximalIdeal D = Ideal.span ({ell} : Set D))
    (hv : IsUnit v) (hr : 0 < r) (hrn : r < n) (hnm : n ≤ m)
    (c A : D) (hc : IsUnit c) (x : Order ell v n)
    (hx : x ^ m = scalar ell v n A - scalar ell v n c * tau ell v n ^ r)
    (a : D) (ha : x - scalar ell v n a ∈
      Ideal.span ({tau ell v n} : Set (Order ell v n))) : IsUnit a := by
  apply IsLocalRing.notMem_maximalIdeal.mp
  intro hamem
  have ha0 : residue ell v (hr.trans hrn) (scalar ell v n a) = 0 := by
    rw [residue_scalar]
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    rwa [← hmax]
  have hd := (residue_eq_zero_iff ell v (hr.trans hrn) hv
    (x - scalar ell v n a)).mpr ha
  rw [map_sub, ha0, sub_zero] at hd
  exact affine_residue_ne_zero ell v (not_isUnit_of_maximalIdeal_eq_span ell hmax)
    hv hr hrn hnm c A hc x hx hd

/-- An actual scalar unit seed for the finite Newton descent, with its tau-adic error.
The exponent m is not assumed invertible here; that belongs to the Newton step. -/
theorem affine_exists_unit_scalar_seed (ell v : D) {n m r : ℕ}
    (hmax : IsLocalRing.maximalIdeal D = Ideal.span ({ell} : Set D))
    (hv : IsUnit v) (hr : 0 < r) (hrn : r < n) (hnm : n ≤ m)
    (c A : D) (hc : IsUnit c) (x : Order ell v n)
    (hx : x ^ m = scalar ell v n A - scalar ell v n c * tau ell v n ^ r) :
    ∃ a : D, IsUnit a ∧ x - scalar ell v n a ∈
      Ideal.span ({tau ell v n} : Set (Order ell v n)) := by
  obtain ⟨a, ha⟩ := exists_scalar_sub_mem_tau ell v n x
  exact ⟨a, affine_scalar_lift_isUnit ell v hmax hv hr hrn hnm c A hc x hx a ha, ha⟩

end Local

end PillaiParameterC
