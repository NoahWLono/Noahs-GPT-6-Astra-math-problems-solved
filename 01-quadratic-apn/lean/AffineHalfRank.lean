import FormNormalization
import NoThreePencil

namespace APNRedo

/-- A four-dimensional target cannot support a three-dimensional nonsingular
alternating pencil; the coordinates are transported by a genuine linear equivalence. -/
theorem no_three_pencil_finrank_four {E : Type*} [AddCommGroup E] [Module F E]
    [FiniteDimensional F E] (he : Module.finrank F E=4)
    (L : V 3 →ₗ[F] Bilin E) (hAlt : ∀u x, L u x x=0)
    (hNondeg : ∀u, u≠0 → Nondegenerate (L u)) : False := by
  let e : V 4 ≃ₗ[F] E := (Module.finBasisOfFinrankEq F E he).equivFun.symm
  let C : V 3 →ₗ[F] Bilin (V 4) :=
    { toFun u := (L u).compl₁₂ e.toLinearMap e.toLinearMap
      map_add' u v := by
        apply LinearMap.ext
        intro x
        apply LinearMap.ext
        intro y
        simp only [map_add, LinearMap.add_apply, LinearMap.compl₁₂_apply]
      map_smul' c u := by
        apply LinearMap.ext
        intro x
        apply LinearMap.ext
        intro y
        simp only [map_smul, LinearMap.smul_apply, RingHom.id_apply,
          LinearMap.compl₁₂_apply] }
  apply NoThreePencil.no_three_pencil C
  · intro u x
    exact hAlt u (e x)
  · intro u hu x hx
    have hz : e x=0 := by
      apply hNondeg u hu
      intro y
      have hh := hx (e.symm y)
      change L u (e x) (e (e.symm y))=0 at hh
      simpa only [e.apply_symm_apply] using hh
    apply e.injective
    simpa only [map_zero] using hz

/-- No affine three-flat of rank-four alternating forms can have all nonzero
directions nonsingular on an eight-dimensional binary vector space. The ranks
are the actual dimensions of the ranges of the curried forms. -/
theorem no_affine_three_half_rank {E : Type*} [AddCommGroup E] [Module F E]
    [FiniteDimensional F E] [Nontrivial E]
    (hdim : Module.finrank F E=8)
    (B : Bilin E) (L : V 3 →ₗ[F] Bilin E)
    (hB : ∀x, B x x=0) (hL : ∀u x, L u x x=0)
    (hN : ∀u, u≠0 → Nondegenerate (L u))
    (hR : ∀u, Module.finrank F (LinearMap.range (B+L u))=4) : False := by
  let u0 : V 3 := Pi.single 0 1
  have hu0 : u0≠0 := by
    intro he
    have hh := congrArg (fun v : V 3 => v (0:Fin 3)) he
    have hz : (1:F)=0 := by simpa [u0] using hh
    exact one_ne_zero hz
  let J := L u0
  have hJ : Nondegenerate J := hN u0 hu0
  let t := normalizeForm J hJ B
  let S : V 3 →ₗ[F] Module.End F E := (normalizeForm J hJ).comp L
  have hnorm : ∀u, t+S u=normalizeForm J hJ (B+L u) := by
    intro u
    exact (map_add (normalizeForm J hJ) B (L u)).symm
  have hsq : ∀u, (t+S u)*(t+S u)=t+S u := by
    intro u
    apply idempotent_of_half_ranks (t+S u) 4 hdim
    · rw [hnorm,normalize_rank]
      exact hR u
    · have hc : 1-(t+S u)=normalizeForm J hJ (B+L (u+u0)) := by
        rw [CharTwo.sub_eq_add, map_add L, map_add, map_add]
        change 1+(t+S u)=t+(S u+normalizeForm J hJ J)
        rw [normalize_self]
        rw [add_comm 1,add_assoc]
      rw [hc,normalize_rank]
      exact hR (u+u0)
  have ht : t*t=t := by simpa only [map_zero,add_zero] using hsq 0
  have htself : SelfAdjoint J t := normalize_selfAdjoint J hJ B (hL u0) hB
  have hSself : ∀u, SelfAdjoint J (S u) := by
    intro u
    exact normalize_selfAdjoint J hJ (L u) (hL u0) (hL u)
  have hSInj : ∀u, u≠0 → Function.Injective (S u) := by
    intro u hu
    exact normalize_injective J hJ (L u) (hN u hu)
  have htrank : Module.finrank F (LinearMap.range t)=4 := by
    change Module.finrank F (LinearMap.range (normalizeForm J hJ B))=4
    rw [normalize_rank]
    have hh := hR (0:V 3)
    rw [L.map_zero,add_zero] at hh
    exact hh
  have hk : Module.finrank F (LinearMap.ker t)=4 := by
    have := t.finrank_range_add_finrank_ker
    omega
  apply no_three_pencil_finrank_four hk (restrictedSquarePencil J t S ht hsq)
  · exact restrictedSquarePencil_alternating J t S ht hsq (hL u0) hSself
  · exact restrictedSquarePencil_nondegenerate J t S ht hsq hJ htself hSInj

#print axioms no_affine_three_half_rank
end APNRedo
