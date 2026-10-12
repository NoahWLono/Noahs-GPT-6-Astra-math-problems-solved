module
public import ZariskiActions
public import Mathlib.Tactic.LinearCombination

@[expose] public section

noncomputable section
namespace ZariskiCylinder
open Polynomial
variable {k : Type*} [Field k]

/-- Points on a common nonzero x-fibre are connected in three standard moves. -/
theorem same_fibre (P : k[X]) (p q : Point k)
    (hp : equation P p = 0) (hq : equation P q = 0)
    (hx : p.x ≠ 0) (hqx : q.x = p.x) : Reaches P 3 p q := by
  let p₁ := tau p (q.u - p.u)
  let p₂ := deltaZ p₁ ((q.z - p₁.z) / p.x ^ 2)
  let p₃ := deltaT P p₂ ((q.t - p₂.t) / p.x ^ 2)
  have h₁x : p₁.x = p.x := rfl
  have h₁u : p₁.u = q.u := by dsimp [p₁, tau]; ring
  have h₂x : p₂.x = p.x := rfl
  have h₂u : p₂.u = q.u := h₁u
  have h₂z : p₂.z = q.z := by
    change p₁.z + (q.z - p₁.z) / p.x ^ 2 * p.x ^ 2 = q.z
    field_simp
    ring
  have h₃x : p₃.x = p.x := rfl
  have h₃u : p₃.u = q.u := h₂u
  have h₃z : p₃.z = q.z := h₂z
  have h₃t : p₃.t = q.t := by
    change p₂.t + (q.t - p₂.t) / p.x ^ 2 * p.x ^ 2 = q.t
    field_simp
    ring
  have hreach : Reaches P 3 p p₃ :=
    .step (.step (.step (.refl p) (.tau p _)) (.deltaZ p₁ _)) (.deltaT p₂ _)
  have h₃eq : equation P p₃ = 0 := hreach.preserves.trans hp
  have h₃y : p₃.y = q.y := by
    apply mul_left_cancel₀ (pow_ne_zero 2 hx)
    dsimp only [equation] at h₃eq hq
    rw [h₃x, h₃u, h₃z, h₃t] at h₃eq
    rw [hqx] at hq
    linear_combination h₃eq - hq
  have heq : p₃ = q := by
    ext
    · exact h₃x.trans hqx.symm
    · exact h₃y
    · exact h₃z
    · exact h₃t
    · exact h₃u
  simpa only [heq] using hreach

end ZariskiCylinder
