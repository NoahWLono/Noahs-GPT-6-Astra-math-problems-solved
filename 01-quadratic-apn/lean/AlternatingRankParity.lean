import FormNormalization
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.RingTheory.Noetherian.Defs

namespace APNRedo
section
variable {E : Type*} [AddCommGroup E] [Module F E] [FiniteDimensional F E]

/-- A maximal totally isotropic subspace of an alternating binary form is its
own orthogonal complement, including for degenerate forms. -/
theorem exists_self_orthogonal (B : Bilin E) (hB : ∀ x, B x x = 0) :
    ∃ U : Submodule F E, LinearMap.BilinForm.orthogonal B U = U := by
  classical
  let S : Set (Submodule F E) := {U | U ≤ LinearMap.BilinForm.orthogonal B U}
  have hne : S.Nonempty := ⟨⊥, by
    change (⊥ : Submodule F E) ≤ _
    exact bot_le⟩
  obtain ⟨U, hU, hmax⟩ := (IsNoetherian.wf (inferInstance : IsNoetherian F E)).has_min S hne
  refine ⟨U, le_antisymm ?_ hU⟩
  intro x hx
  let W : Submodule F E := U ⊔ F ∙ x
  have hW : W ∈ S := by
    intro a ha b hb
    obtain ⟨u, hu, v, hv, rfl⟩ := Submodule.mem_sup.mp ha
    obtain ⟨w, hw, z, hz, rfl⟩ := Submodule.mem_sup.mp hb
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hv
    obtain ⟨d, rfl⟩ := Submodule.mem_span_singleton.mp hz
    change B (w + d • x) (u + c • x) = 0
    have hwu : B w u = 0 := hU hu w hw
    have hwx : B w x = 0 := hx w hw
    have hxu : B x u = 0 := by rw [alternating_symmetric B hB]; exact hx u hu
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
      hwu, hwx, hxu, hB, smul_zero, add_zero, zero_add]
  have hle : U ≤ W := le_sup_left
  have heq : U = W := eq_of_le_of_not_lt hle (hmax W hW)
  rw [heq]
  exact (le_sup_right : (F ∙ x) ≤ W) (Submodule.mem_span_singleton_self x)

/-- The rank of every alternating bilinear form over the binary field is even. -/
theorem alternating_rank_even (B : Bilin E) (hB : ∀ x, B x x = 0) :
    Even (Module.finrank F (LinearMap.range B)) := by
  obtain ⟨U, hU⟩ := exists_self_orthogonal B hB
  have hR : B.IsRefl := by
    intro x y hxy
    rw [alternating_symmetric B hB]
    exact hxy
  have hk : LinearMap.BilinForm.orthogonal B ⊤ = LinearMap.ker B :=
    LinearMap.BilinForm.orthogonal_top_eq_ker hR
  have hku : LinearMap.ker B ≤ U := by
    rw [← hk, ← hU]
    exact LinearMap.BilinForm.orthogonal_le le_top
  have hd := LinearMap.BilinForm.finrank_add_finrank_orthogonal hR U
  rw [hU, hk, inf_eq_right.mpr hku] at hd
  have hr := B.finrank_range_add_finrank_ker
  refine ⟨Module.finrank F U - Module.finrank F (LinearMap.ker B), ?_⟩
  omega

/-- In even ambient dimension, the radical of an alternating binary form
also has even dimension. -/
theorem alternating_radical_even (B : Bilin E) (hB : ∀ x, B x x = 0)
    (hdim : Even (Module.finrank F E)) :
    Even (Module.finrank F (LinearMap.ker B)) := by
  obtain ⟨r, hr⟩ := alternating_rank_even B hB
  obtain ⟨d, hd⟩ := hdim
  have hn := B.finrank_range_add_finrank_ker
  refine ⟨d - r, ?_⟩
  omega

#print axioms alternating_rank_even
#print axioms alternating_radical_even
end
end APNRedo
