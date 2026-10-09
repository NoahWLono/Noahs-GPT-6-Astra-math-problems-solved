import BooleanANF
import Mathlib.Data.Finset.Sum

namespace BooleanANF
open scoped BigOperators
variable {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]

/-- Splitting the subcube transform into two blocks of coordinates. -/
theorem transform_disjSum (F : Finset (ι ⊕ κ) → F₂) (s : Finset ι) (t : Finset κ) :
    transform F (s.disjSum t) =
      ∑ a ∈ s.powerset, ∑ b ∈ t.powerset, F (a.disjSum b) := by
  rw [← Finset.sum_product s.powerset t.powerset (fun p => F (p.1.disjSum p.2))]
  symm
  apply Finset.sum_bij (fun p _ => p.1.disjSum p.2)
  · intro p hp
    rcases Finset.mem_product.mp hp with ⟨ha, hb⟩
    simpa [Finset.mem_powerset, Finset.subset_disjSum] using
      And.intro (Finset.mem_powerset.mp ha) (Finset.mem_powerset.mp hb)
  · intro a ha b hb hab
    apply Prod.ext
    · simpa using congrArg Finset.toLeft hab
    · simpa using congrArg Finset.toRight hab
  · intro u hu
    refine ⟨(u.toLeft, u.toRight), ?_, Finset.toLeft_disjSum_toRight⟩
    simpa [Finset.mem_powerset, Finset.subset_disjSum] using hu
  · intro p hp
    rfl

theorem point_disjSum (s : Finset ι) (t : Finset κ) :
    point (s.disjSum t) = Sum.elim (point s) (point t) := by
  funext i
  cases i <;> simp [point]

/-- Coefficient of an x-monomial, retained as a function of the other coordinates. -/
def fiberCoefficient (f : ((ι ⊕ κ) → F₂) → F₂) (s : Finset ι)
    (y : κ → F₂) : F₂ := coefficient (fun x => f (Sum.elim x y)) s

/-- Coefficient extraction commutes with splitting variables; no degree assumption is needed. -/
theorem coefficient_fiberCoefficient (f : ((ι ⊕ κ) → F₂) → F₂)
    (s : Finset ι) (t : Finset κ) :
    coefficient (fiberCoefficient f s) t = coefficient f (s.disjSum t) := by
  unfold coefficient fiberCoefficient
  rw [transform_disjSum]
  simp only [transform, point_disjSum]
  exact Finset.sum_comm

/-- Extracting k x-coordinates lowers the remaining y-degree by k. -/
theorem HasDegreeLE.fiberCoefficient {f : ((ι ⊕ κ) → F₂) → F₂}
    {d e : ℕ} (hf : HasDegreeLE f (d + e)) (s : Finset ι) (hs : d ≤ s.card) :
    HasDegreeLE (fiberCoefficient f s) e := by
  intro t ht
  rw [coefficient_fiberCoefficient]
  apply hf
  rw [Finset.card_disjSum]
  exact Nat.add_lt_add_of_le_of_lt hs ht

end BooleanANF

namespace BooleanANF
open scoped BigOperators
variable {ι κ : Type*} [DecidableEq ι] [DecidableEq κ] [Fintype ι] [Fintype κ]

/-- The indicator of a singleton, as an actual Boolean function. -/
def delta (a : ι → F₂) (x : ι → F₂) : F₂ := if x = a then 1 else 0

theorem coefficient_delta (a : ι → F₂) (s : Finset ι) :
    coefficient (delta a) s = if support a ⊆ s then 1 else 0 := by
  have hp (t : Finset ι) : point t = a ↔ t = support a := by
    constructor
    · intro h
      simpa using congrArg support h
    · intro h
      simp [h]
  simp [coefficient, transform, delta, hp]

@[simp] theorem coefficient_delta_top (a : ι → F₂) :
    coefficient (delta a) Finset.univ = 1 := by
  simp [coefficient_delta]

/-- The next-to-top singleton coefficient determines its unique support point. -/
theorem coefficient_delta_cubic (a : ι → F₂) (i : ι) :
    coefficient (delta a) (Finset.univ.erase i) = 1 + a i := by
  rw [coefficient_delta]
  have h : a i = 0 ∨ a i = 1 := by
    generalize a i = z
    fin_cases z <;> simp_all
  rcases h with h | h <;> simp [Finset.subset_erase, support, h, CharTwo.add_self_eq_zero]

/-- Degree zero in canonical ANF means the function is constant. -/
theorem HasDegreeLE.eq_const {f : (κ → F₂) → F₂} (hf : HasDegreeLE f 0)
    (y : κ → F₂) : f y = f 0 := by
  rw [← reconstruction_all f y, ← reconstruction_all f 0]
  apply Finset.sum_congr rfl
  intro s hs
  by_cases he : s = ∅
  · subst s
    simp [monomial_empty]
  · have hc : 0 < s.card := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr he)
    simp [hf s hc]

/-- For total degree at most the x-dimension, the top x-coefficient is independent of y. -/
theorem top_fiber_constant {f : ((ι ⊕ κ) → F₂) → F₂}
    (hf : HasDegreeLE f (Fintype.card ι)) (y : κ → F₂) :
    fiberCoefficient f Finset.univ y = fiberCoefficient f Finset.univ 0 := by
  apply HasDegreeLE.eq_const
  apply HasDegreeLE.fiberCoefficient (d := Fintype.card ι) (e := 0)
  · simpa using hf
  · simp

/-- In four plus four variables, each cubic x-coefficient is affine in y. -/
theorem cubic_fiber_affine {f : ((Fin 4 ⊕ Fin 4) → F₂) → F₂}
    (hf : HasDegreeLE f 4) (i : Fin 4) :
    HasDegreeLE (fiberCoefficient f (Finset.univ.erase i)) 1 := by
  apply HasDegreeLE.fiberCoefficient (d := 3) (e := 1) hf
  simp

end BooleanANF
