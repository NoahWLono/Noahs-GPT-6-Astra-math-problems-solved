module
public import ZariskiEscape
public import Mathlib.FieldTheory.IsAlgClosed.Basic

@[expose] public section

noncomputable section
namespace ZariskiCylinder
open Polynomial
variable {k : Type*} [Field k] [CharZero k]

/-- A point where the extra action is a translation of the x coordinate. -/
def bridgePoint (z t ξ : k) : Point k := ⟨ξ, -1, z, t, (ξ - 1) / (2 * z)⟩

theorem av_bridgePoint (z t ξ : k) (hz : z ≠ 0) : av (bridgePoint z t ξ) = 0 := by
  dsimp [av, bridgePoint]
  field_simp
  ring

theorem equation_bridgePoint (P : k[X]) (z t ξ : k) (hz : z ≠ 0)
    (he : z ^ 2 + P.eval t = 0) : equation P (bridgePoint z t ξ) = 0 := by
  rw [equation_av, av_bridgePoint z t ξ hz]
  simpa [bridgePoint] using he

theorem extra_bridge_x (P : k[X]) (z t ξ s : k) (hz : z ≠ 0) :
    (extra P (bridgePoint z t ξ) s).x = ξ - 2 * z * P.derivative.eval t * s := by
  unfold extra
  rw [eStep_x, av_bridgePoint z t ξ hz]
  simp only [mul_zero, zero_mul, sub_zero, difference_q_zero, divided_eval_zero]
  simp only [mv, av_bridgePoint z t ξ hz]
  simp only [bridgePoint]
  ring

/-- Seven moves suffice between any two nonzero-x fibres. -/
theorem nonzero_connected (P : k[X]) (z t : k) (hz : z ≠ 0)
    (he : z ^ 2 + P.eval t = 0) (hd : P.derivative.eval t ≠ 0)
    (p q : Point k) (hp : equation P p = 0) (hq : equation P q = 0)
    (hpx : p.x ≠ 0) (hqx : q.x ≠ 0) : Reaches P 7 p q := by
  let b := bridgePoint z t p.x
  let s := (p.x - q.x) / (2 * z * P.derivative.eval t)
  let r := extra P b s
  have hb : equation P b = 0 := equation_bridgePoint P z t p.x hz he
  have hpr : Reaches P 4 p r :=
    .step (same_fibre P p b hp hb hpx rfl) (.extra b s)
  have hrx : r.x = q.x := by
    dsimp only [r, b]
    rw [extra_bridge_x P z t p.x s hz]
    dsimp [s]
    field_simp
    ring
  have hr : equation P r = 0 := hpr.preserves.trans hp
  have hrq : Reaches P 3 r q := same_fibre P r q hr hq (by rwa [hrx]) hrx.symm
  exact hpr.trans hrq

/-- Full pointwise transitivity, with a uniform 13-generator word bound. -/
theorem transitive_thirteen_of_witness (P : k[X]) (hP : Function.Surjective P.eval)
    (z t : k) (hz : z ≠ 0) (he : z ^ 2 + P.eval t = 0)
    (hd : P.derivative.eval t ≠ 0)
    (p q : Point k) (hp : equation P p = 0) (hq : equation P q = 0) :
    Reaches P 13 p q := by
  obtain ⟨p', hpp', hp'x⟩ := reach_nonzero P hP p
  obtain ⟨q', hqq', hq'x⟩ := reach_nonzero P hP q
  have hp' : equation P p' = 0 := hpp'.preserves.trans hp
  have hq' : equation P q' = 0 := hqq'.preserves.trans hq
  have hm := nonzero_connected P z t hz he hd p' q' hp' hq' hp'x hq'x
  exact (hpp'.trans hm).trans hqq'.symm

/-- The geometric witness is automatic for any nonconstant polynomial over
an algebraically closed characteristic-zero field. -/
theorem exists_bridge [IsAlgClosed k] (P : k[X]) (hP : P.natDegree ≠ 0) :
    ∃ z t : k, z ≠ 0 ∧ z ^ 2 + P.eval t = 0 ∧ P.derivative.eval t ≠ 0 := by
  have hp : P ≠ 0 := by intro h; exact hP (by simp [h])
  have hd : P.derivative ≠ 0 := derivative_ne_zero.mpr hP
  have hh : P * P.derivative ≠ 0 := mul_ne_zero hp hd
  have hsome : ∃ t : k, (P * P.derivative).eval t ≠ 0 := by
    by_contra! hn
    apply hh
    apply Polynomial.funext
    intro t
    simpa using hn t
  obtain ⟨t, ht⟩ := hsome
  rw [eval_mul] at ht
  have hpt : P.eval t ≠ 0 := (mul_ne_zero_iff.mp ht).1
  have hdt : P.derivative.eval t ≠ 0 := (mul_ne_zero_iff.mp ht).2
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (-P.eval t) (by decide : 0 < 2)
  refine ⟨z, t, ?_, ?_, hdt⟩
  · intro hzero
    rw [hzero, zero_pow (by decide : 2 ≠ 0)] at hz
    exact hpt (by simpa using hz.symm)
  · rw [hz]
    ring

/-- Exact scoped main theorem. No cancellation conclusion is asserted. -/
theorem transitive_thirteen [IsAlgClosed k] (P : k[X]) (hP : P.natDegree ≠ 0)
    (p q : Point k) (hp : equation P p = 0) (hq : equation P q = 0) :
    Reaches P 13 p q := by
  obtain ⟨z, t, hz, he, hd⟩ := exists_bridge P hP
  exact transitive_thirteen_of_witness P (IsAlgClosed.eval_surjective hP)
    z t hz he hd p q hp hq

#print axioms transitive_thirteen
end ZariskiCylinder
