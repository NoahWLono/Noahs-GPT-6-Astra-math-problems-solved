import APNCoordinateLabels
import AlternatingRankParity

namespace APNRedo
open scoped BigOperators Classical

section
variable {E : Type*} [AddCommGroup E] [Module F E] [FiniteDimensional F E]

theorem nondegenerate_iff_kernel_finrank_zero (B : Bilin E) :
    Nondegenerate B ↔ Module.finrank F (LinearMap.ker B)=0 := by
  rw [Submodule.finrank_eq_zero,LinearMap.ker_eq_bot']
  constructor
  · intro h x hx
    exact h x (fun y => LinearMap.congr_fun hx y)
  · intro h x hx
    exact h x (LinearMap.ext hx)
end

/-- Actual degenerate nonzero coordinate components; Walsh identification is a
separate bridge, not part of this definition. -/
noncomputable def degenerateLabels (Q : QuadraticMap F (V 8) (V 8)) : Finset (V 8) :=
  (Finset.univ.erase 0).filter fun b => ¬Nondegenerate (componentPencil Q b)

/-- Finite residue arithmetic, with explicit even-dimensional hypotheses. -/
theorem incidence_count_residue {α : Type*} (S : Finset α) (r : α → ℕ)
    (hr : ∀b∈S, r b≤8 ∧ r b%2=0)
    (hi : ∑b∈S, (2^r b-1)=255) :
    (S.filter fun b => r b≠0).card%4=1 := by
  have heach : ∀b∈S, (2^r b-1+(if r b=0 then 0 else 1))%4=0 := by
    intro b hb
    obtain ⟨hle,hev⟩ := hr b hb
    have hx : r b=0 ∨ r b=2 ∨ r b=4 ∨ r b=6 ∨ r b=8 := by omega
    rcases hx with hx | hx | hx | hx | hx <;> rw [hx] <;> decide
  have hs : (∑b∈S, (2^r b-1+(if r b=0 then 0 else 1)))%4=0 := by
    rw [Finset.sum_nat_mod]
    have hz : (∑b∈S, (2^r b-1+(if r b=0 then 0 else 1))%4)=0 :=
      Finset.sum_eq_zero heach
    rw [hz]
  rw [Finset.sum_add_distrib,hi] at hs
  have hcount : (∑b∈S, if r b=0 then 0 else 1)=(S.filter fun b => r b≠0).card := by
    rw [Finset.card_eq_sum_ones,Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro b hb
    split_ifs <;> simp_all
  rw [hcount] at hs
  omega

/-- The real APN count congruence, conditional only on the remaining alternating
rank-parity theorem, explicitly stated here until that independent proof lands. -/
theorem apn_degenerate_count_congruence_of_even_radicals
    (Q : QuadraticMap F (V 8) (V 8)) (hQ : APN Q)
    (heven : ∀b, Module.finrank F (LinearMap.ker (componentPencil Q b))%2=0) :
    (degenerateLabels Q).card%4=1 := by
  have h := incidence_count_residue (Finset.univ.erase (0:V 8))
    (fun b => Module.finrank F (LinearMap.ker (componentPencil Q b)))
    (fun b hb => ⟨by
      have hh := Submodule.finrank_le (LinearMap.ker (componentPencil Q b))
      simpa [V] using hh, heven b⟩)
    (apn_coordinate_radical_incidence Q hQ)
  have heq : degenerateLabels Q=(Finset.univ.erase (0:V 8)).filter
      (fun b => Module.finrank F (LinearMap.ker (componentPencil Q b))≠0) := by
    apply Finset.filter_congr
    intro b hb
    exact not_congr (nondegenerate_iff_kernel_finrank_zero (componentPencil Q b))
  rw [heq]
  exact h

theorem component_radical_even (Q : QuadraticMap F (V 8) (V 8)) (b : V 8) :
    Even (Module.finrank F (LinearMap.ker (componentPencil Q b))) := by
  apply alternating_radical_even (componentPencil Q b)
  · exact componentPolarDual_alternating Q (coordinateDotForm 8 b)
  · simpa [V] using (show Even (8:ℕ) from by decide)

/-- Unconditional component-count congruence for genuine quadratic APN maps. -/
theorem apn_degenerate_count_congruence (Q : QuadraticMap F (V 8) (V 8)) (hQ : APN Q) :
    (degenerateLabels Q).card%4=1 := by
  apply apn_degenerate_count_congruence_of_even_radicals Q hQ
  intro b
  exact Nat.even_iff.mp (component_radical_even Q b)

#print axioms apn_degenerate_count_congruence
end APNRedo
