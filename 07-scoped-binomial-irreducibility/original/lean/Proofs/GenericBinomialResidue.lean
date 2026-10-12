import Mathlib.RingTheory.AdjoinRoot
import Mathlib.Algebra.Polynomial.Eval.Coeff
import Mathlib.Algebra.Divisibility.Units

/-!
Elaborated with pinned Lean 4.32.2 and mathlib commit
905b95818eb32af7874a58b427f50c1711a5e96c. See the adjacent clean-build evidence.
Actual monic-quotient residue and coefficient interfaces for parameter-prime C.
No coordinate-uniqueness bridge is assumed: coordinates are monic remainders.
The generic ring can have zero divisors. No DVR or extension-field assumption is used.
-/

set_option autoImplicit false

noncomputable section
open Polynomial

namespace PillaiParameterC

universe u
variable {D : Type u} [CommRing D]

/-- The actual defining polynomial, with v an arbitrary scalar for now. -/
def binomial (ell v : D) (n : ℕ) : D[X] := X ^ n - C (ell * v)

/-- This is definitionally D[T]/(T^n-ell*v). -/
abbrev Order (ell v : D) (n : ℕ) := AdjoinRoot (binomial ell v n)

abbrev scalar (ell v : D) (n : ℕ) : D →+* Order ell v n :=
  AdjoinRoot.of (binomial ell v n)

abbrev tau (ell v : D) (n : ℕ) : Order ell v n :=
  AdjoinRoot.root (binomial ell v n)

lemma binomial_monic (ell v : D) {n : ℕ} (hn : 0 < n) :
    (binomial ell v n).Monic :=
  Polynomial.monic_X_pow_sub_C (ell * v) (Nat.ne_of_gt hn)

@[simp] lemma tau_pow (ell v : D) (n : ℕ) :
    tau ell v n ^ n = scalar ell v n (ell * v) := by
  apply sub_eq_zero.mp
  have h := AdjoinRoot.eval₂_root (binomial ell v n)
  change eval₂ (scalar ell v n) (tau ell v n) ((X : D[X]) ^ n - C (ell * v)) = 0 at h
  simpa only [eval₂_sub, eval₂_pow, eval₂_X, eval₂_C] using h

/-- The residue homomorphism exists by the actual quotient universal property. -/
def residue (ell v : D) {n : ℕ} (hn : 0 < n) :
    Order ell v n →+* D ⧸ Ideal.span ({ell} : Set D) :=
  AdjoinRoot.lift (Ideal.Quotient.mk _) 0 (by
    have hell : Ideal.Quotient.mk (Ideal.span ({ell} : Set D)) ell = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self ell)
    simp [binomial, Nat.ne_of_gt hn, map_mul, hell])

@[simp] lemma residue_scalar (ell v : D) {n : ℕ} (hn : 0 < n) (a : D) :
    residue ell v hn (scalar ell v n a) =
      Ideal.Quotient.mk (Ideal.span ({ell} : Set D)) a := by
  simp [residue, scalar]

@[simp] lemma residue_tau (ell v : D) {n : ℕ} (hn : 0 < n) :
    residue ell v hn (tau ell v n) = 0 := by
  simp [residue, tau]

@[simp] lemma residue_mk (ell v : D) {n : ℕ} (hn : 0 < n) (P : D[X]) :
    residue ell v hn (AdjoinRoot.mk (binomial ell v n) P) =
      Ideal.Quotient.mk (Ideal.span ({ell} : Set D)) (P.coeff 0) := by
  rw [residue, AdjoinRoot.lift_mk, Polynomial.eval₂_at_zero]

lemma residue_surjective (ell v : D) {n : ℕ} (hn : 0 < n) :
    Function.Surjective (residue ell v hn) := by
  intro z
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective z
  exact ⟨scalar ell v n a, residue_scalar ell v hn a⟩

/-- Every actual quotient class has a constant-plus-tau decomposition. -/
lemma exists_scalar_add_tau_mul (ell v : D) (n : ℕ) (z : Order ell v n) :
    ∃ a : D, ∃ w : Order ell v n, z = scalar ell v n a + tau ell v n * w := by
  obtain ⟨P, rfl⟩ := AdjoinRoot.mk_surjective z
  refine ⟨P.coeff 0, AdjoinRoot.mk (binomial ell v n) P.divX, ?_⟩
  have h := congrArg (AdjoinRoot.mk (binomial ell v n)) (Polynomial.X_mul_divX_add P)
  simpa only [map_add, map_mul, AdjoinRoot.mk_X, AdjoinRoot.mk_C, add_comm]
    using h.symm

/-- Unit v turns tau^n = ell*v into divisibility of the scalar ell by tau. -/
lemma tau_dvd_scalar_ell (ell v : D) {n : ℕ} (hn : 0 < n) (hv : IsUnit v) :
    tau ell v n ∣ scalar ell v n ell := by
  rcases hv with ⟨u, rfl⟩
  refine ⟨tau ell (u : D) n ^ (n - 1) * scalar ell (u : D) n (↑(u⁻¹) : D), ?_⟩
  rw [← mul_assoc, ← pow_succ', Nat.sub_add_cancel hn, tau_pow]
  rw [← map_mul, mul_assoc, Units.mul_inv, mul_one]

/-- Exact kernel statement in principal-ideal membership form. -/
lemma residue_eq_zero_iff (ell v : D) {n : ℕ} (hn : 0 < n) (hv : IsUnit v)
    (z : Order ell v n) :
    residue ell v hn z = 0 ↔ z ∈ Ideal.span ({tau ell v n} : Set (Order ell v n)) := by
  constructor
  · intro hz
    obtain ⟨a, w, rfl⟩ := exists_scalar_add_tau_mul ell v n z
    have ha : Ideal.Quotient.mk (Ideal.span ({ell} : Set D)) a = 0 := by
      simpa only [map_add, map_mul, residue_scalar, residue_tau, zero_mul, add_zero] using hz
    obtain ⟨b, hb⟩ := Ideal.mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp ha)
    apply Ideal.mem_span_singleton.mpr
    apply dvd_add
    · rw [hb, map_mul]
      exact dvd_mul_of_dvd_left (tau_dvd_scalar_ell ell v hn hv) _
    · exact dvd_mul_right _ _
  · intro hz
    obtain ⟨w, hw⟩ := Ideal.mem_span_singleton.mp hz
    rw [hw, map_mul, residue_tau, zero_mul]

lemma ker_residue (ell v : D) {n : ℕ} (hn : 0 < n) (hv : IsUnit v) :
    RingHom.ker (residue ell v hn) = Ideal.span ({tau ell v n} : Set (Order ell v n)) := by
  ext z
  exact residue_eq_zero_iff ell v hn hv z

/-- The residue of each class has a scalar lift whose difference is in tau*S. -/
lemma exists_scalar_sub_mem_tau (ell v : D) (n : ℕ)
    (z : Order ell v n) :
    ∃ a : D, z - scalar ell v n a ∈ Ideal.span ({tau ell v n} : Set (Order ell v n)) := by
  obtain ⟨a, w, hz⟩ := exists_scalar_add_tau_mul ell v n z
  refine ⟨a, Ideal.mem_span_singleton.mpr ?_⟩
  rw [hz, add_sub_cancel_left]
  exact dvd_mul_right _ _

section Coordinates

variable [Nontrivial D]

@[simp] lemma binomial_natDegree (ell v : D) (n : ℕ) :
    (binomial ell v n).natDegree = n :=
  Polynomial.natDegree_X_pow_sub_C

/-- The concrete power basis produced by monic polynomial division. -/
def powerBasis (ell v : D) {n : ℕ} (hn : 0 < n) :
    PowerBasis D (Order ell v n) :=
  AdjoinRoot.powerBasis' (binomial_monic ell v hn)

@[simp] lemma powerBasis_dim (ell v : D) {n : ℕ} (hn : 0 < n) :
    (powerBasis ell v hn).dim = n := by
  simp [powerBasis]

/-- A coordinate is the coefficient of the actual monic remainder, as a linear map. -/
def coord (ell v : D) {n : ℕ} (hn : 0 < n) (r : ℕ) :
    Order ell v n →ₗ[D] D :=
  (Polynomial.lcoeff D r).comp (AdjoinRoot.modByMonicHom (binomial_monic ell v hn))

omit [Nontrivial D] in
/-- This explicitly identifies the coordinate map with the concrete power-basis coordinate. -/
lemma coord_eq_powerBasis_repr (ell v : D) {n : ℕ} (hn : 0 < n)
    (z : Order ell v n) (i : Fin (binomial ell v n).natDegree) :
    coord ell v hn i z = (powerBasis ell v hn).basis.repr z i := by
  rfl

lemma coord_mk_of_natDegree_lt (ell v : D) {n : ℕ} (hn : 0 < n)
    (r : ℕ) (P : D[X]) (hP : P.natDegree < n) :
    coord ell v hn r (AdjoinRoot.mk (binomial ell v n) P) = P.coeff r := by
  change (P %ₘ binomial ell v n).coeff r = P.coeff r
  have hrem : P %ₘ binomial ell v n = P := by
    apply (Polynomial.modByMonic_eq_self_iff (binomial_monic ell v hn)).mpr
    apply Polynomial.degree_lt_degree
    simpa only [binomial_natDegree] using hP
  rw [hrem]

lemma coord_scalar_mul_tau_pow (ell v : D) {n : ℕ} (hn : 0 < n)
    (r k : ℕ) (hk : k < n) (a : D) :
    coord ell v hn r (scalar ell v n a * tau ell v n ^ k) =
      if r = k then a else 0 := by
  have hP : (C a * (X : D[X]) ^ k).natDegree < n :=
    (Polynomial.natDegree_C_mul_X_pow_le a k).trans_lt hk
  have h := coord_mk_of_natDegree_lt ell v hn r (C a * X ^ k) hP
  simpa only [map_mul, map_pow, AdjoinRoot.mk_C, AdjoinRoot.mk_X,
    Polynomial.coeff_C_mul_X_pow] using h

lemma coord_scalar (ell v : D) {n : ℕ} (hn : 0 < n) (r : ℕ) (a : D) :
    coord ell v hn r (scalar ell v n a) = if r = 0 then a else 0 := by
  simpa only [pow_zero, mul_one] using coord_scalar_mul_tau_pow ell v hn r 0 hn a

omit [Nontrivial D] in
lemma coord_scalar_mul (ell v : D) {n : ℕ} (hn : 0 < n)
    (r : ℕ) (a : D) (z : Order ell v n) :
    coord ell v hn r (scalar ell v n a * z) = a * coord ell v hn r z := by
  change coord ell v hn r (algebraMap D (Order ell v n) a * z) = _
  rw [← Algebra.smul_def, map_smul, smul_eq_mul]

omit [Nontrivial D] in
/-- Every coefficient of an element of ell*S is divisible by ell in D. -/
lemma ell_dvd_coord_of_mem (ell v : D) {n : ℕ} (hn : 0 < n) (r : ℕ)
    (z : Order ell v n)
    (hz : z ∈ Ideal.span ({scalar ell v n ell} : Set (Order ell v n))) :
    ell ∣ coord ell v hn r z := by
  obtain ⟨w, hw⟩ := Ideal.mem_span_singleton.mp hz
  rw [hw, coord_scalar_mul]
  exact dvd_mul_right _ _

/-- Smallest coherent obstruction: a unit coefficient below degree n cannot be absorbed
into the scalar coefficient modulo ell*S. No domain, DVR, residue field, or IsUnit v is needed. -/
theorem unit_coefficient_sub_scalar_not_mem (ell v : D) {n r : ℕ}
    (hell : ¬ IsUnit ell) (hr : 0 < r) (hrn : r < n)
    (c d : D) (hc : IsUnit c) :
    scalar ell v n c * tau ell v n ^ r - scalar ell v n d ∉
      Ideal.span ({scalar ell v n ell} : Set (Order ell v n)) := by
  have hn : 0 < n := hr.trans hrn
  intro hz
  have hcoord :
      coord ell v hn r (scalar ell v n c * tau ell v n ^ r - scalar ell v n d) = c := by
    rw [map_sub, coord_scalar_mul_tau_pow ell v hn r r hrn c, coord_scalar]
    simp [Nat.ne_of_gt hr]
  have hdiv := ell_dvd_coord_of_mem ell v hn r _ hz
  rw [hcoord] at hdiv
  exact hell (isUnit_of_dvd_unit hdiv hc)

/-- The corresponding divisibility formulation is often easiest in affine-power proofs. -/
theorem scalar_ell_not_dvd_unit_monomial_sub_scalar (ell v : D) {n r : ℕ}
    (hell : ¬ IsUnit ell) (hr : 0 < r) (hrn : r < n)
    (c d : D) (hc : IsUnit c) :
    ¬ scalar ell v n ell ∣ scalar ell v n c * tau ell v n ^ r - scalar ell v n d := by
  intro hdiv
  exact unit_coefficient_sub_scalar_not_mem ell v hell hr hrn c d hc
    (Ideal.mem_span_singleton.mpr hdiv)

end Coordinates

end PillaiParameterC
