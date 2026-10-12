import GenericBinomialConductor
import GenericBinomialResidue
import FiniteNewtonDescent

/-! Finite root descent in the actual quotient, given an explicit scalar-unit
seed. The later affine residue argument supplies this seed in a DVR. -/
set_option autoImplicit false
open Polynomial Algebra
namespace PillaiParameterC
universe u
variable {D : Type u} [CommRing D]

/-- The actual quotient conductor and fixed-derivative finite Newton theorem
put an existing affine power root in the smaller order. The scalar-unit seed
is an explicit helper hypothesis here, rather than an assumed final bridge. -/
theorem power_root_mem_smaller_order_of_scalar_unit_seed
    (ell v : D) (n r m : ℕ) (hcop : n.Coprime r) (c : Dˣ)
    (A : D) (x : Order ell v n)
    (hroot : x ^ m = scalar ell v n A - scalar ell v n (c : D) * tau ell v n ^ r)
    (hm : IsUnit (m : D)) (a : D) (ha : IsUnit a)
    (hclose : x - scalar ell v n a ∈ Ideal.span ({tau ell v n} : Set (Order ell v n))) :
    x ∈ Algebra.adjoin D ({scalar ell v n (c : D) * tau ell v n ^ r} :
      Set (Order ell v n)) := by
  let R := Algebra.adjoin D ({scalar ell v n (c : D) * tau ell v n ^ r} :
    Set (Order ell v n))
  let I : Ideal (Order ell v n) := Ideal.span {tau ell v n}
  let N : ℕ := (n - 1) * (r - 1)
  have hconductor (z : Order ell v n) (hz : z ∈ I ^ N) : z ∈ R :=
    PillaiParameterConductor.quotient_conductor n r hcop ell v c z hz
  by_cases hN : N = 0
  · exact hconductor x (by simp only [hN, pow_zero, Ideal.one_eq_top, Submodule.mem_top])
  have hNpos : 1 ≤ N := Nat.one_le_iff_ne_zero.mpr hN
  have hscalar (d : D) : scalar ell v n d ∈ R := R.algebraMap_mem d
  let w : R := ⟨scalar ell v n A - scalar ell v n (c : D) * tau ell v n ^ r,
    R.sub_mem (hscalar A) (Algebra.self_mem_adjoin_singleton D _)⟩
  let a₀ : R := algebraMap D R a
  have hmR : IsUnit (m : R) := by
    simpa only [map_natCast] using hm.map (algebraMap D R)
  have haR : IsUnit a₀ := ha.map (algebraMap D R)
  exact PillaiFiniteNewton.finite_power_root_descent R.toSubring I N hNpos
    hconductor m w a₀ x hroot hclose hmR haR

end PillaiParameterC
