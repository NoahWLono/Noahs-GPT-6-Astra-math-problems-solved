import QuadraticSemantics
import RankFourPair

set_option maxRecDepth 2000
set_option maxHeartbeats 300000

namespace APNRedo
open scoped BigOperators Classical

/-- Pure finite arithmetic for an actual partition by positive even-dimensional
radicals. Pairwise dimensional bounds are explicit, not assumed APN semantics. -/
theorem profile29_dimensions {α : Type*} (S : Finset α) (r : α → ℕ)
    (hc : S.card=29)
    (hr : ∀b∈S, 0<r b ∧ r b≤8 ∧ r b%2=0)
    (hp : ∀b∈S, ∀c∈S, b≠c → r b+r c≤8)
    (hi : ∑b∈S, (2^r b-1)=255) :
    (∀b∈S, r b=2 ∨ r b=4) ∧ (S.filter fun b => r b=4).card=14 := by
  have hsmall : ∀b∈S, r b=2 ∨ r b=4 := by
    intro b hb
    obtain ⟨hpos,hle,hev⟩ := hr b hb
    have he : r b=2 ∨ r b=4 ∨ r b=6 ∨ r b=8 := by omega
    rcases he with he | he | he | he
    · exact Or.inl he
    · exact Or.inr he
    · have hother : ∀c∈S.erase b, r c=2 := by
        intro c hcm
        obtain ⟨hcb,hcS⟩ := Finset.mem_erase.mp hcm
        have hpp := hp b hb c hcS hcb.symm
        obtain ⟨hcpos,hcle,hcev⟩ := hr c hcS
        omega
      have hsum : ∑c∈S.erase b, (2^r c-1)=84 := by
        have hrewrite : (∑c∈S.erase b, (2^r c-1))=∑c∈S.erase b, (3:ℕ) := by
          apply Finset.sum_congr rfl
          intro c hcm
          rw [hother c hcm]
          decide
        rw [hrewrite]
        simp [Finset.card_erase_of_mem hb,hc]
      have hsplit := Finset.sum_erase_add S (fun c => 2^r c-1) hb
      dsimp only at hsplit
      rw [hsum,he,hi] at hsplit
      norm_num at hsplit
    · have hsub : S⊆{b} := by
        intro c hcS
        by_cases hcb : b=c
        · simp [hcb]
        · have hpp := hp b hb c hcS hcb
          have hcpos := (hr c hcS).1
          omega
      have hcard := Finset.card_le_card hsub
      simp only [Finset.card_singleton,hc] at hcard
      omega
  refine ⟨hsmall,?_⟩
  have hw : ∑b∈S, (2^r b-1)=∑b∈S, (3+12*(if r b=4 then 1 else 0)) := by
    apply Finset.sum_congr rfl
    intro b hb
    rcases hsmall b hb with he | he <;> rw [he] <;> decide
  rw [hw,Finset.sum_add_distrib,←Finset.mul_sum] at hi
  have hcount : (∑b∈S, if r b=4 then 1 else 0)=(S.filter fun b => r b=4).card := by
    rw [Finset.card_eq_sum_ones,Finset.sum_filter]
  rw [hcount] at hi
  simp only [Finset.sum_const,Nat.nsmul_eq_mul,hc] at hi
  omega

/-- Actual APN incidence restricted to the actual degenerate labels. -/
theorem apn_degenerate_radical_incidence (Q : QuadraticMap F (V 8) (V 8)) (hQ : APN Q) :
    ∑b∈degenerateLabels Q,
      (2^Module.finrank F (LinearMap.ker (componentPencil Q b))-1)=255 := by
  have h := apn_coordinate_radical_incidence Q hQ
  refine Eq.trans ?_ h
  apply Finset.sum_subset
  · exact Finset.filter_subset _ _
  · intro b hb hbn
    have hn : Nondegenerate (componentPencil Q b) := by
      by_contra hdeg
      exact hbn (Finset.mem_filter.mpr ⟨hb,hdeg⟩)
    rw [(nondegenerate_iff_kernel_finrank_zero _).mp hn]
    decide

/-- Profile i3 is derived from genuine APN, incidence and the cardinal29 claim;
no radical spectrum is assumed. -/
theorem apn_profile29 (Q : QuadraticMap F (V 8) (V 8)) (hQ : APN Q)
    (hcard : (degenerateLabels Q).card=29) :
    (∀b∈degenerateLabels Q,
      Module.finrank F (LinearMap.ker (componentPencil Q b))=2 ∨
      Module.finrank F (LinearMap.ker (componentPencil Q b))=4) ∧
    ((degenerateLabels Q).filter fun b =>
      Module.finrank F (LinearMap.ker (componentPencil Q b))=4).card=14 := by
  apply profile29_dimensions _ _ hcard
  · intro b hb
    have hdeg : ¬Nondegenerate (componentPencil Q b) := (Finset.mem_filter.mp hb).2
    have hn := mt (nondegenerate_iff_kernel_finrank_zero _).mpr hdeg
    have hle := Submodule.finrank_le (LinearMap.ker (componentPencil Q b))
    have hev := Nat.even_iff.mp (component_radical_even Q b)
    refine ⟨Nat.pos_of_ne_zero hn,?_,hev⟩
    simpa [V] using hle
  · intro b hb c hc hbc
    have hb0 : b≠0 := (Finset.mem_erase.mp (Finset.mem_filter.mp hb).1).1
    have hc0 : c≠0 := (Finset.mem_erase.mp (Finset.mem_filter.mp hc).1).1
    have hd := apn_coordinate_radicals_disjoint Q hQ b c hb0 hc0 hbc
    have hh := Submodule.finrank_add_finrank_le_of_disjoint hd
    simpa [V] using hh
  · exact apn_degenerate_radical_incidence Q hQ

/-- Two distinct rank-four actual APN components have a nonsingular sum. -/
theorem apn_rank_four_pair_sum_nondegenerate
    (Q : QuadraticMap F (V 8) (V 8)) (hQ : APN Q)
    (b c : V 8) (hb : b≠0) (hc : c≠0) (hbc : b≠c)
    (hbr : Module.finrank F (LinearMap.ker (componentPencil Q b))=4)
    (hcr : Module.finrank F (LinearMap.ker (componentPencil Q c))=4) :
    Nondegenerate (componentPencil Q (b+c)) := by
  rw [map_add]
  apply sum_nondegenerate_of_disjoint_half_rank _ _ 4
  · simp [V]
  · exact componentPolarDual_alternating Q (coordinateDotForm 8 b)
  · exact componentPolarDual_alternating Q (coordinateDotForm 8 c)
  · have hh := (componentPencil Q b).finrank_range_add_finrank_ker
    rw [hbr] at hh
    have hd : Module.finrank F (V 8)=8 := by simp [V]
    omega
  · have hh := (componentPencil Q c).finrank_range_add_finrank_ker
    rw [hcr] at hh
    have hd : Module.finrank F (V 8)=8 := by simp [V]
    omega
  · exact apn_coordinate_radicals_disjoint Q hQ b c hb hc hbc

#print axioms apn_rank_four_pair_sum_nondegenerate
#print axioms apn_profile29
end APNRedo
