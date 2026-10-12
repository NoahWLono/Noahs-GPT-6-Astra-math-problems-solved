import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Algebra.Algebra.Basic

/-! Recover an integral polynomial lift by undoing an integral translation. -/
set_option autoImplicit false
open Polynomial
namespace PillaiLocalCoefficients

universe u v

theorem integral_lift_of_integral_translate
    {R : Type u} {K : Type v} [CommRing R] [IsDomain R] [Field K] [Algebra R K]
    (n : ℕ) (a : R) (G : K[X]) (H : R[X])
    (hHdeg : H.natDegree < n)
    (hH : H.map (algebraMap R K) = G.comp (X + C (algebraMap R K a))) :
    ∃ P : R[X], P.natDegree < n ∧ P.map (algebraMap R K) = G := by
  refine ⟨H.comp (X - C a), ?_, ?_⟩
  · simpa only [natDegree_comp, natDegree_X_sub_C, mul_one] using hHdeg
  · rw [map_comp, hH]
    simp only [Polynomial.map_sub, map_X, map_C, comp_assoc, add_comp,
      X_comp, C_comp, sub_add_cancel, comp_X]

end PillaiLocalCoefficients
