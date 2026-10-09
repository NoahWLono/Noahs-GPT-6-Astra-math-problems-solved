import FourFlatGeometry
import AffineHalfRank

set_option maxHeartbeats 400000
set_option maxRecDepth 2000
namespace APNRedo
open scoped BigOperators Classical

/-- The normalized two-flat support conclusion of the weight30 classification
is incompatible with the actual APN profile29. The coordinate equivalence and
support equation are explicit hypotheses; no forbidden pencil is assumed. -/
theorem apn_profile29_excluded_by_two_flat_support
    (Q : QuadraticMap F (V 8) (V 8)) (hQ : APN Q)
    (hcard : (degenerateLabels Q).card=29)
    (e : (V 4×V 4) ≃ₗ[F] V 8) (c : V 4) (hc : c≠0)
    (hSupport : ∀a v:V 4, e (a,v)∈degenerateLabels Q ↔
      (v=0 ∧ a≠0 ∧ a≠c) ∨ (a=c ∧ v≠0)) : False := by
  let R := (degenerateLabels Q).filter fun b =>
    Module.finrank F (LinearMap.ker (componentPencil Q b))=4
  have hRcard : R.card=14 := (apn_profile29 Q hQ hcard).2
  have hR : ∀b∈R, b≠0 ∧ b∈degenerateLabels Q ∧
      Module.finrank F (LinearMap.ker (componentPencil Q b))=4 := by
    intro b hb
    have hh := Finset.mem_filter.mp hb
    exact ⟨(Finset.mem_erase.mp (Finset.mem_filter.mp hh.1).1).1,hh.1,hh.2⟩
  let A := R.filter fun b => (e.symm b).2=0
  let T : Finset (V 4) := Finset.univ.filter fun v => e (c,v)∈R
  have hAcard : A.card≤2 := by
    apply card_le_two_of_constant_pair_sum A (e (c,0))
    intro b hb d hd hbd
    have hbb := Finset.mem_filter.mp hb
    have hdd := Finset.mem_filter.mp hd
    let a := (e.symm b).1
    let a' := (e.symm d).1
    have hbexpr : b=e (a,0) := by
      calc
        b=e (e.symm b) := (e.apply_symm_apply b).symm
        _=e (a,0) := congrArg e (Prod.ext rfl hbb.2)
    have hdexpr : d=e (a',0) := by
      calc
        d=e (e.symm d) := (e.apply_symm_apply d).symm
        _=e (a',0) := congrArg e (Prod.ext rfl hdd.2)
    have hsumexpr : b+d=e (a+a',0) := by
      rw [hbexpr,hdexpr,←map_add]
      rfl
    have hsumnz : b+d≠0 := by
      intro hh
      have he := eq_neg_of_add_eq_zero_left hh
      exact hbd (by simpa only [binary_neg_eq] using he)
    have ha0 : a+a'≠0 := by
      intro hh
      apply hsumnz
      rw [hsumexpr,hh]
      exact e.map_zero
    have hnondeg := apn_rank_four_pair_sum_nondegenerate Q hQ b d
      (hR b hbb.1).1 (hR d hdd.1).1 hbd (hR b hbb.1).2.2 (hR d hdd.1).2.2
    have hac : a+a'=c := by
      by_contra hne
      have hm := (hSupport (a+a') 0).mpr (Or.inl ⟨rfl,ha0,hne⟩)
      rw [←hsumexpr] at hm
      exact (Finset.mem_filter.mp hm).2 hnondeg
    rw [hsumexpr,hac]
  have hcover : R⊆A∪T.image (fun v => e (c,v)) := by
    intro b hb
    have hm : e ((e.symm b).1,(e.symm b).2)∈degenerateLabels Q := by
      simpa only [Prod.eta,e.apply_symm_apply] using (hR b hb).2.1
    rcases (hSupport _ _).mp hm with hA | hT
    · exact Finset.mem_union.mpr (Or.inl (Finset.mem_filter.mpr ⟨hb,hA.1⟩))
    · apply Finset.mem_union.mpr
      apply Or.inr
      have he : e (c,(e.symm b).2)=b := by
        rw [←hT.1]
        exact e.apply_symm_apply b
      apply Finset.mem_image.mpr
      refine ⟨(e.symm b).2,?_,he⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,by rwa [he]⟩
  have hTcard : 12≤T.card := by
    have h1 := Finset.card_le_card hcover
    have h2 := Finset.card_union_le A (T.image fun v => e (c,v))
    have h3 := Finset.card_image_le (s:=T) (f:=fun v => e (c,v))
    omega
  have hT0 : (0:V 4)∉T := by
    intro hh
    have hr : e (c,0)∈R := (Finset.mem_filter.mp hh).2
    have hs := (hSupport c 0).mp (hR _ hr).2.1
    simp only [ne_eq,not_true_eq_false,and_false,or_self] at hs
  obtain ⟨a,D,hD,hinside⟩ := twelve_points_contain_affine_three_flat T hTcard hT0
  let G : V 3 →ₗ[F] V 8 := e.toLinearMap.comp ((LinearMap.inr F (V 4) (V 4)).comp D)
  let L : V 3 →ₗ[F] Bilin (V 8) := (componentPencil Q).comp G
  let B : Bilin (V 8) := componentPencil Q (e (c,a))
  have hG : ∀u, G u=e (0,D u) := fun _ => rfl
  have hL : ∀u, L u=componentPencil Q (e (0,D u)) := fun _ => rfl
  have hfamily : ∀u, B+L u=componentPencil Q (e (c,a+D u)) := by
    intro u
    rw [hL]
    change componentPencil Q (e (c,a))+componentPencil Q (e (0,D u))=_
    rw [←map_add,←map_add]
    congr 1
    simp only [Prod.mk_add_mk,add_zero]
  apply no_affine_three_half_rank (by simp [V]) B L
  · exact componentPolarDual_alternating Q (coordinateDotForm 8 (e (c,a)))
  · intro u
    exact componentPolarDual_alternating Q (coordinateDotForm 8 (G u))
  · intro u hu
    have hd0 : D u≠0 := by
      intro hh
      exact hu (hD (hh.trans D.map_zero.symm))
    have hlabel : e (0,D u)≠0 := by
      intro hh
      have hprod := e.injective (hh.trans e.map_zero.symm)
      exact hd0 (congrArg Prod.snd hprod)
    rw [hL]
    by_contra hn
    have hm : e (0,D u)∈degenerateLabels Q :=
      Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨hlabel,Finset.mem_univ _⟩,hn⟩
    have hs := (hSupport 0 (D u)).mp hm
    rcases hs with hs | hs
    · exact hs.2.1 rfl
    · exact hc hs.1.symm
  · intro u
    rw [hfamily]
    have hm : e (c,a+D u)∈R := (Finset.mem_filter.mp (hinside u)).2
    have hk := (hR _ hm).2.2
    have hh := (componentPencil Q (e (c,a+D u))).finrank_range_add_finrank_ker
    have hd : Module.finrank F (V 8)=8 := by simp [V]
    omega

/-- Raw degeneracy includes the zero label. This wrapper makes the zero-mask
removal explicit when consuming a support classification of 1+Pfaffian. -/
theorem apn_profile29_excluded_by_raw_two_flat_support
    (Q : QuadraticMap F (V 8) (V 8)) (hQ : APN Q)
    (hcard : (degenerateLabels Q).card=29)
    (e : (V 4×V 4) ≃ₗ[F] V 8) (c : V 4) (hc : c≠0)
    (hRaw : ∀a v:V 4, ¬Nondegenerate (componentPencil Q (e (a,v))) ↔
      (v=0 ∧ a≠c) ∨ (a=c ∧ v≠0)) : False := by
  apply apn_profile29_excluded_by_two_flat_support Q hQ hcard e c hc
  intro a v
  have hz : e (a,v)=0 ↔ a=0 ∧ v=0 := by
    rw [LinearEquiv.map_eq_zero_iff]
    exact Prod.mk_eq_zero
  rw [degenerateLabels,Finset.mem_filter]
  simp only [Finset.mem_erase,Finset.mem_univ,and_true]
  rw [hRaw]
  simp only [ne_eq,hz]
  tauto

#print axioms apn_profile29_excluded_by_raw_two_flat_support
#print axioms apn_profile29_excluded_by_two_flat_support
end APNRedo
