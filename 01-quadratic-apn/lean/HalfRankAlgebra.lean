import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.CharP.Two
import Mathlib.Tactic.NoncommRing

namespace APNRedo

section Ring
variable {R : Type*} [Ring R] [CharP R 2]

/-- In an affine space of idempotents, the direction elements commute. -/
theorem affine_idempotent_directions_commute (t a b : R)
    (ht : t*t=t) (ha : (t+a)*(t+a)=t+a)
    (hb : (t+b)*(t+b)=t+b)
    (hab : (t+(a+b))*(t+(a+b))=t+(a+b)) : a*b=b*a := by
  have h : a*b + b*a = 0 := by
    calc
      a*b+b*a = (t+(a+b))*(t+(a+b)) - (t+a)*(t+a) - (t+b)*(t+b) + t*t := by noncomm_ring
      _ = 0 := by rw [hab, ha, hb, ht]; noncomm_ring
  have he := eq_neg_of_add_eq_zero_left h
  simpa only [CharTwo.neg_eq] using he

/-- Squaring an affine idempotent direction commutes with the base projection. -/
theorem affine_idempotent_square_commutes (t a : R)
    (ht : t*t=t) (ha : (t+a)*(t+a)=t+a) : t*(a*a)=(a*a)*t := by
  have h : t*a+a*t+a*a=a := by
    calc
      t*a+a*t+a*a = (t+a)*(t+a)-t*t := by noncomm_ring
      _ = a := by rw [ha, ht]; noncomm_ring
  have hl : t*(t*a+a*t+a*a)=t*a := congrArg (fun z : R => t*z) h
  have hr : (t*a+a*t+a*a)*t=a*t := congrArg (fun z : R => z*t) h
  have hcomm : t*(a*a) - (a*a)*t = 0 := by
    calc
      t*(a*a) - (a*a)*t = (t*(t*a+a*t+a*a)-t*a) - ((t*a+a*t+a*a)*t-a*t) := by
        symm
        calc
          _ = t*(a*a) - (a*a)*t + (t*t-t)*a - a*(t*t-t) := by noncomm_ring
          _ = _ := by rw [ht]; simp
      _ = 0 := by rw [hl, hr]; noncomm_ring
  exact sub_eq_zero.mp hcomm

end Ring
section Projection
variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
    [FiniteDimensional K E]

/-- Two complementary half-rank kernels force an actual linear projection. -/
theorem idempotent_of_half_ranks (q : Module.End K E) (k : ℕ)
    (hdim : Module.finrank K E = 2*k)
    (hq : Module.finrank K (LinearMap.range q) = k)
    (hc : Module.finrank K (LinearMap.range (1-q)) = k) : q*q=q := by
  have hk : Module.finrank K (LinearMap.ker q) = k := by
    have := q.finrank_range_add_finrank_ker
    omega
  have hl : Module.finrank K (LinearMap.ker (1-q)) = k := by
    have := (1-q).finrank_range_add_finrank_ker
    omega
  have hd : Disjoint (LinearMap.ker q) (LinearMap.ker (1-q)) := by
    rw [Submodule.disjoint_def]
    intro x hx hy
    have hx' : q x=0 := hx
    have hy' : x-q x=0 := hy
    simpa [hx'] using hy'
  have hs : LinearMap.ker q ⊔ LinearMap.ker (1-q) = ⊤ :=
    Submodule.eq_top_of_disjoint _ _ (by rw [hdim,hk,hl]; omega) hd
  ext x
  have hm : x ∈ LinearMap.ker q ⊔ LinearMap.ker (1-q) := by rw [hs]; trivial
  obtain ⟨y,hy,z,hz,hx⟩ := Submodule.mem_sup.mp hm
  have hy' : q y=0 := hy
  have hz' : q z=z := (sub_eq_zero.mp (show z-q z=0 from hz)).symm
  rw [← hx]
  change q (q (y+z))=q (y+z)
  simp [map_add,hy',hz']

end Projection

#print axioms affine_idempotent_directions_commute
#print axioms affine_idempotent_square_commutes
#print axioms idempotent_of_half_ranks
end APNRedo
