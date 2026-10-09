import NormalizedPencil
import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.NormNum
import Mathlib.LinearAlgebra.Dual.Lemmas

namespace APNRedo
section
variable {E : Type*} [AddCommGroup E] [Module F E] [FiniteDimensional F E]

/-- The actual isomorphism from a nondegenerate bilinear form to the dual. -/
noncomputable def formEquiv (J : Bilin E) (hJ : Nondegenerate J) :
    E ≃ₗ[F] (E →ₗ[F] F) :=
  J.linearEquivOfInjective (by
    apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    intro x hx
    exact hJ x (fun y => LinearMap.congr_fun hx y))
    (Subspace.dual_finrank_eq.symm)

@[simp] theorem formEquiv_apply (J : Bilin E) (hJ : Nondegenerate J) (x : E) :
    formEquiv J hJ x=J x := rfl

/-- Normalize a form by a proven nondegenerate form. -/
noncomputable def normalizeForm (J : Bilin E) (hJ : Nondegenerate J) :
    Bilin E →ₗ[F] Module.End F E where
  toFun D := (formEquiv J hJ).symm.toLinearMap.comp D
  map_add' D C := by ext x; simp
  map_smul' c D := by ext x; simp

@[simp] theorem normalizeForm_apply (J : Bilin E) (hJ : Nondegenerate J)
    (D : Bilin E) (x : E) : normalizeForm J hJ D x=(formEquiv J hJ).symm (D x) := rfl

@[simp] theorem form_normalize (J : Bilin E) (hJ : Nondegenerate J)
    (D : Bilin E) (x y : E) : J (normalizeForm J hJ D x) y=D x y := by
  have he := (formEquiv J hJ).apply_symm_apply (D x)
  exact LinearMap.congr_fun he y

@[simp] theorem normalize_self (J : Bilin E) (hJ : Nondegenerate J) :
    normalizeForm J hJ J=1 := by
  ext x
  exact (formEquiv J hJ).symm_apply_apply x

/-- Alternating binary forms are symmetric, with their actual evaluations. -/
theorem alternating_symmetric (D : Bilin E) (hD : ∀x, D x x=0) :
    ∀x y, D x y=D y x := by
  intro x y
  have h := hD (x+y)
  simp only [map_add, LinearMap.add_apply, hD] at h
  have hz : D x y+D y x=0 := by simpa [add_comm] using h
  simpa only [CharTwo.neg_eq] using eq_neg_of_add_eq_zero_left hz

/-- Actual normalization preserves the adjoint property. -/
theorem normalize_selfAdjoint (J : Bilin E) (hJ : Nondegenerate J)
    (D : Bilin E) (hJA : ∀x, J x x=0) (hDA : ∀x, D x x=0) :
    SelfAdjoint J (normalizeForm J hJ D) := by
  intro x y
  rw [form_normalize, alternating_symmetric J hJA, form_normalize]
  exact alternating_symmetric D hDA x y

@[simp] theorem normalize_kernel (J : Bilin E) (hJ : Nondegenerate J)
    (D : Bilin E) : LinearMap.ker (normalizeForm J hJ D)=LinearMap.ker D := by
  ext x
  simp only [LinearMap.mem_ker, normalizeForm_apply, LinearEquiv.map_eq_zero_iff]

theorem normalize_rank (J : Bilin E) (hJ : Nondegenerate J) (D : Bilin E) :
    Module.finrank F (LinearMap.range (normalizeForm J hJ D))=
      Module.finrank F (LinearMap.range D) := by
  have h1 := (normalizeForm J hJ D).finrank_range_add_finrank_ker
  have h2 := D.finrank_range_add_finrank_ker
  rw [normalize_kernel] at h1
  omega

theorem normalize_injective (J : Bilin E) (hJ : Nondegenerate J)
    (D : Bilin E) (hD : Nondegenerate D) :
    Function.Injective (normalizeForm J hJ D) := by
  apply LinearMap.ker_eq_bot.mp
  rw [normalize_kernel]
  apply LinearMap.ker_eq_bot'.mpr
  intro x hx
  exact hD x (fun y => LinearMap.congr_fun hx y)

#print axioms normalize_rank
#print axioms normalize_selfAdjoint
end
end APNRedo
