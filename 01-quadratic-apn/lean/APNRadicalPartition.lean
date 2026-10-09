import APNPolar

namespace APNRedo
section
variable {E : Type*} [AddCommGroup E] [Module F E] [FiniteDimensional F E]

/-- A binary one-dimensional vector space has exactly one nonzero vector. -/
theorem unique_nonzero_of_finrank_one (h : Module.finrank F E=1) :
    ∃!x:E, x≠0 := by
  let v : E := Module.finBasisOfFinrankEq F E h 0
  have hv : v≠0 := (Module.finBasisOfFinrankEq F E h).ne_zero 0
  refine ⟨v,hv,?_⟩
  intro y hy
  obtain ⟨c,hc⟩ := exists_smul_eq_of_finrank_eq_one h hv y
  have hc01 : c=0 ∨ c=1 := by
    have hcval := ZMod.val_lt c
    have hc' : c.val=0 ∨ c.val=1 := by omega
    rcases hc' with hc' | hc'
    · left; exact ZMod.val_injective 2 (by simpa using hc')
    · right; exact ZMod.val_injective 2 (by simpa using hc')
  rcases hc01 with rfl | rfl
  · simp only [zero_smul] at hc
    exact False.elim (hy hc.symm)
  · simpa only [one_smul] using hc.symm

/-- Actual scalar polar form of the component x -> b(Q(x)). -/
def componentPolarDual (Q : QuadraticMap F E E) (b : E →ₗ[F] F) : Bilin E :=
  Q.polarBilin.compr₂ b

@[simp] theorem componentPolarDual_apply (Q : QuadraticMap F E E)
    (b : E →ₗ[F] F) (a x : E) : componentPolarDual Q b a x=b (Q.polarBilin a x) := rfl

/-- The scalar polar comes from the actual scalar quadratic component. -/
theorem componentPolarDual_actual (Q : QuadraticMap F E E) (b : E →ₗ[F] F) :
    (b.compQuadraticMap' Q).polarBilin=componentPolarDual Q b :=
  LinearMap.compQuadraticMap_polarBilin b Q

def componentPencilDual (Q : QuadraticMap F E E) : (E →ₗ[F] F) →ₗ[F] Bilin E where
  toFun b := componentPolarDual Q b
  map_add' b c := by
    apply LinearMap.ext
    intro x
    apply LinearMap.ext
    intro y
    rfl
  map_smul' c b := by
    apply LinearMap.ext
    intro x
    apply LinearMap.ext
    intro y
    rfl

variable [Nontrivial E]

theorem componentPolarDual_alternating (Q : QuadraticMap F E E)
    (b : E →ₗ[F] F) : ∀x, componentPolarDual Q b x x=0 := by
  intro x
  rw [componentPolarDual_apply,quadratic_polar_diagonal,map_zero]

/-- The directional annihilator is genuinely one-dimensional, by rank-nullity. -/
theorem apn_direction_annihilator_finrank (Q : QuadraticMap F E E) (hQ : APN Q)
    (a : E) (ha : a≠0) :
    Module.finrank F (LinearMap.range (Q.polarBilin a)).dualAnnihilator=1 := by
  have h1 := apn_quadratic_direction_rank Q hQ a ha
  have h2 := Subspace.finrank_add_finrank_dualAnnihilator_eq
    (LinearMap.range (Q.polarBilin a))
  omega

/-- Every nonzero input belongs to exactly one nonzero component radical. -/
theorem apn_unique_nonzero_radical_label (Q : QuadraticMap F E E) (hQ : APN Q)
    (a : E) (ha : a≠0) :
    ∃! b : E →ₗ[F] F, b≠0 ∧ ∀x, componentPolarDual Q b a x=0 := by
  let W := (LinearMap.range (Q.polarBilin a)).dualAnnihilator
  obtain ⟨b,hb,huniq⟩ := unique_nonzero_of_finrank_one
    (apn_direction_annihilator_finrank Q hQ a ha)
  have hb' : (b:E →ₗ[F] F)≠0 := by
    intro he
    exact hb (Subtype.ext he)
  have hbmem : ∀x, componentPolarDual Q b a x=0 := by
    intro x
    exact (Submodule.mem_dualAnnihilator _).mp b.property _ ⟨x,rfl⟩
  refine ⟨b,⟨hb',hbmem⟩,?_⟩
  intro c hc
  have hcmem : c∈W := by
    apply (Submodule.mem_dualAnnihilator c).mpr
    rintro y ⟨x,rfl⟩
    exact hc.2 x
  have hcne : (⟨c,hcmem⟩:W)≠0 := by
    intro he
    exact hc.1 (congrArg Subtype.val he)
  exact congrArg Subtype.val (huniq ⟨c,hcmem⟩ hcne)

/-- APN forces distinct nonzero actual scalar-component radicals to be disjoint. -/
theorem apn_component_radicals_disjoint (Q : QuadraticMap F E E) (hQ : APN Q)
    (b c : E →ₗ[F] F) (hb : b≠0) (hc : c≠0) (hbc : b≠c) :
    Disjoint (LinearMap.ker (componentPolarDual Q b))
      (LinearMap.ker (componentPolarDual Q c)) := by
  rw [Submodule.disjoint_def]
  intro a hab hac
  by_contra ha
  obtain ⟨d,hd,huniq⟩ := apn_unique_nonzero_radical_label Q hQ a ha
  have hbD : b=d := huniq b ⟨hb,fun x => LinearMap.congr_fun hab x⟩
  have hcD : c=d := huniq c ⟨hc,fun x => LinearMap.congr_fun hac x⟩
  exact hbc (hbD.trans hcD.symm)

#print axioms apn_unique_nonzero_radical_label
#print axioms apn_component_radicals_disjoint
end
end APNRedo
