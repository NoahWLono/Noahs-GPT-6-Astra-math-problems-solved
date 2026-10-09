import APNRadicalPartition
import Mathlib.FieldTheory.Finiteness
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace APNRedo
open scoped BigOperators Classical
section
variable {E : Type*} [AddCommGroup E] [Module F E] [FiniteDimensional F E]
  [Nontrivial E] [Fintype E] [Fintype (E →ₗ[F] F)]

noncomputable def radicalPoints (Q : QuadraticMap F E E) (b : E →ₗ[F] F) : Finset E := by
  classical
  exact Finset.univ.filter fun a => componentPolarDual Q b a=0

@[simp] theorem mem_radicalPoints (Q : QuadraticMap F E E) (b : E →ₗ[F] F) (a : E) :
    a∈radicalPoints Q b ↔ componentPolarDual Q b a=0 := by
  classical
  simp [radicalPoints]

@[simp] theorem zero_mem_radicalPoints (Q : QuadraticMap F E E) (b : E →ₗ[F] F) :
    0∈radicalPoints Q b := by simp

theorem card_radicalPoints (Q : QuadraticMap F E E) (b : E →ₗ[F] F) :
    (radicalPoints Q b).card=2^Module.finrank F (LinearMap.ker (componentPolarDual Q b)) := by
  classical
  rw [radicalPoints,←Fintype.card_subtype]
  change Fintype.card (LinearMap.ker (componentPolarDual Q b))=_
  rw [Module.card_eq_pow_finrank (K:=F) (V:=LinearMap.ker (componentPolarDual Q b))]
  simp only [F,ZMod.card]

/-- Unconditional cardinal incidence identity from the actual APN radical partition. -/
theorem apn_radical_incidence (Q : QuadraticMap F E E) (hQ : APN Q) :
    ∑ b ∈ Finset.univ.erase (0:E →ₗ[F] F),
      (2^Module.finrank F (LinearMap.ker (componentPolarDual Q b))-1)=
        Fintype.card E-1 := by
  classical
  let S : Finset (E →ₗ[F] F) := Finset.univ.erase 0
  let R : (E →ₗ[F] F) → Finset E := fun b => (radicalPoints Q b).erase 0
  have hdis : S.toSet.PairwiseDisjoint R := by
    intro b hb c hc hbc
    apply Finset.disjoint_left.mpr
    intro a hab hac
    have hb0 : b≠0 := (Finset.mem_erase.mp hb).1
    have hc0 : c≠0 := (Finset.mem_erase.mp hc).1
    have ha0 : a≠0 := (Finset.mem_erase.mp hab).1
    have hab' : componentPolarDual Q b a=0 :=
      (mem_radicalPoints Q b a).mp (Finset.mem_erase.mp hab).2
    have hac' : componentPolarDual Q c a=0 :=
      (mem_radicalPoints Q c a).mp (Finset.mem_erase.mp hac).2
    have hd := apn_component_radicals_disjoint Q hQ b c hb0 hc0 hbc
    exact ha0 ((Submodule.disjoint_def.mp hd) a hab' hac')
  have hcover : S.biUnion R=Finset.univ.erase (0:E) := by
    ext a
    constructor
    · intro ha
      obtain ⟨b,hb,hab⟩ := Finset.mem_biUnion.mp ha
      exact Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp hab).1,Finset.mem_univ _⟩
    · intro ha
      have ha0 : a≠0 := (Finset.mem_erase.mp ha).1
      obtain ⟨b,⟨hb,hba⟩,huniq⟩ := apn_unique_nonzero_radical_label Q hQ a ha0
      apply Finset.mem_biUnion.mpr
      refine ⟨b,Finset.mem_erase.mpr ⟨hb,Finset.mem_univ _⟩,?_⟩
      apply Finset.mem_erase.mpr
      refine ⟨ha0,(mem_radicalPoints Q b a).mpr ?_⟩
      exact LinearMap.ext hba
  have hc := Finset.card_biUnion hdis
  rw [hcover] at hc
  have hR : ∀b, (R b).card=2^Module.finrank F (LinearMap.ker (componentPolarDual Q b))-1 := by
    intro b
    dsimp only [R]
    rw [Finset.card_erase_of_mem (zero_mem_radicalPoints Q b),card_radicalPoints]
  simp_rw [hR] at hc
  simpa only [S,Finset.card_erase_of_mem (Finset.mem_univ (0:E)),Finset.card_univ] using hc.symm

noncomputable instance dualEightFintype : Fintype (V 8 →ₗ[F] F) := by
  letI : Finite (V 8 →ₗ[F] F) :=
    Finite.of_injective (fun b : V 8 →ₗ[F] F => (b : V 8 → F)) DFunLike.coe_injective
  exact Fintype.ofFinite _

theorem apn_radical_incidence_eight (Q : QuadraticMap F (V 8) (V 8)) (hQ : APN Q) :
    ∑ b ∈ Finset.univ.erase (0:V 8 →ₗ[F] F),
      (2^Module.finrank F (LinearMap.ker (componentPolarDual Q b))-1)=255 := by
  have h := apn_radical_incidence Q hQ
  simpa [V,F,ZMod.card] using h

#print axioms apn_radical_incidence_eight
end
end APNRedo
