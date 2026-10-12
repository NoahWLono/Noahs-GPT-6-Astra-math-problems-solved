import QuarticSeparatorValue
import QuarticSeparatorAnnihilation
noncomputable section
namespace NakaiQuartic
open MvPolynomial
open scoped BigOperators

/-- Annihilation applies to the entire gradient ideal, with arbitrary multipliers. -/
theorem separator_zero_of_mem_J {p : P} (hp : p ∈ J) : separator p = 0 := by
  obtain ⟨c, rfl⟩ := Ideal.mem_span_range_iff_exists_fun.mp hp
  simp only [map_sum]
  apply Finset.sum_eq_zero
  intro i _
  simpa only [mul_comm] using separator_G_mul i (c i)

theorem h_not_mem_J : h ∉ J := by
  intro hh
  have hz := separator_zero_of_mem_J hh
  rw [separator_h] at hz
  norm_num at hz


#print axioms NakaiQuartic.h_not_mem_J
end NakaiQuartic
