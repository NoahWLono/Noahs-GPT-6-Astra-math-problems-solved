import APNProfile29

set_option maxHeartbeats 300000
namespace APNRedo
open scoped BigOperators Classical

/-- At most four omitted points, including zero, leave an entire affine
three-flat inside a twelve-point subset of the binary four-space. -/
theorem twelve_points_contain_affine_three_flat (T : Finset (V 4))
    (hc : 12≤T.card) (h0 : (0:V 4)∉T) :
    ∃a:V 4, ∃D:V 3 →ₗ[F] V 4, Function.Injective D ∧ ∀u, a+D u∈T := by
  classical
  let H : Finset (V 4) := Finset.univ\T
  have hH0 : (0:V 4)∈H := by simp [H,h0]
  have hHcard : H.card≤4 := by
    have hcount : H.card=16-T.card := by
      simp [H,Finset.card_sdiff,Finset.subset_univ,V,F,ZMod.card]
    omega
  let W : Submodule F (V 4) := Submodule.span F (H.erase 0 : Set (V 4))
  have hW : Module.finrank F W≤3 := by
    have hh := finrank_span_finset_le_card (R:=F) (H.erase 0)
    change Module.finrank F W≤(H.erase 0).card at hh
    rw [Finset.card_erase_of_mem hH0] at hh
    omega
  have hann : 0<Module.finrank F W.dualAnnihilator := by
    have hh := Subspace.finrank_add_finrank_dualAnnihilator_eq W
    have hd : Module.finrank F (V 4)=4 := by simp [V]
    omega
  obtain ⟨phi,hphi⟩ := Module.finrank_pos_iff_exists_ne_zero.mp hann
  let f : V 4 →ₗ[F] F := phi.val
  have hf : f≠0 := by
    intro he
    exact hphi (Subtype.ext he)
  have hHzero : ∀x∈H, f x=0 := by
    intro x hx
    by_cases hx0 : x=0
    · simp [hx0]
    · apply (Submodule.mem_dualAnnihilator _).mp phi.property
      exact Submodule.subset_span (Finset.mem_erase.mpr ⟨hx0,hx⟩)
  have hsur : Function.Surjective f :=
    surjective_of_nonzero_of_finrank_eq_one (K:=F) (by simp) hf
  obtain ⟨a,ha⟩ := hsur 1
  have hk : Module.finrank F (LinearMap.ker f)=3 := by
    have hh := f.finrank_range_add_finrank_ker
    have hr : LinearMap.range f=⊤ := LinearMap.range_eq_top.mpr hsur
    rw [hr] at hh
    simp only [finrank_top] at hh
    have hd : Module.finrank F (V 4)=4 := by simp [V]
    have hf1 : Module.finrank F F=1 := by simp
    omega
  let e : V 3 ≃ₗ[F] LinearMap.ker f := (Module.finBasisOfFinrankEq F _ hk).equivFun.symm
  let D : V 3 →ₗ[F] V 4 := (LinearMap.ker f).subtype.comp e.toLinearMap
  refine ⟨a,D,?_,?_⟩
  · exact Subtype.coe_injective.comp e.injective
  · intro u
    by_contra hu
    have hmem : a+D u∈H := Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,hu⟩
    have hz := hHzero _ hmem
    have hd : f (D u)=0 := (e u).property
    rw [map_add,ha,hd,add_zero] at hz
    exact one_ne_zero hz

/-- If every distinct pair in a binary additive set has the same sum,
there are at most two points. -/
theorem card_le_two_of_constant_pair_sum {E : Type*} [AddCommGroup E] [Module F E]
    [Nontrivial E] (T : Finset E) (c : E)
    (hp : ∀x∈T, ∀y∈T, x≠y → x+y=c) : T.card≤2 := by
  classical
  by_cases ht : T.Nonempty
  · obtain ⟨a,ha⟩ := ht
    have hsub : T⊆{a,a+c} := by
      intro b hb
      by_cases he : a=b
      · simp [he]
      · have hh := hp a ha b hb he
        have hbval : b=a+c := by
          have h := congrArg (fun z => a+z) hh
          simpa only [←add_assoc,binary_add_self,zero_add] using h
        simp [hbval]
    have hp : ({a,a+c}:Finset E).card≤2 := by
      calc
        _ ≤ ({a+c}:Finset E).card+1 := Finset.card_insert_le _ _
        _ = 2 := by simp
    exact le_trans (Finset.card_le_card hsub) hp
  · have he : T=∅ := Finset.not_nonempty_iff_eq_empty.mp ht
    simp [he]

#print axioms twelve_points_contain_affine_three_flat
end APNRedo
