import BooleanANFDescentSpec
import BooleanANFSupportBounds
import Mathlib.Data.Fin.Tuple.Basic

namespace BooleanANF
open scoped BigOperators

private theorem add_self_vec {ι : Type*} (x : ι → F₂) : x + x = 0 := by
  funext i
  exact CharTwo.add_self_eq_zero (x i)

def descentMap {n : ℕ} (a : Fin (n+1) → F₂) (i : Fin (n+1))
    (z : (Unit ⊕ Fin n) → F₂) : Fin (n+1) → F₂ :=
  Fin.insertNth i (z (.inl ()))
    (fun j => z (.inr j) + z (.inl ()) * a (i.succAbove j))

def descentInv {n : ℕ} (a : Fin (n+1) → F₂) (i : Fin (n+1))
    (x : Fin (n+1) → F₂) : (Unit ⊕ Fin n) → F₂ :=
  Sum.elim (fun _ => x i) (fun j => x (i.succAbove j) + x i * a (i.succAbove j))

def descentEquiv {n : ℕ} (a : Fin (n+1) → F₂) (i : Fin (n+1)) :
    ((Unit ⊕ Fin n) → F₂) ≃ (Fin (n+1) → F₂) where
  toFun := descentMap a i
  invFun := descentInv a i
  left_inv z := by
    funext j
    cases j with
    | inl u => cases u; simp [descentInv, descentMap]
    | inr j => simp [descentInv, descentMap, add_assoc, CharTwo.add_self_eq_zero]
  right_inv x := by
    apply Fin.insertNth_eq_iff.mpr
    constructor
    · simp [descentInv, descentMap]
    · funext j
      simp [descentInv, descentMap, Fin.removeNth, add_assoc, CharTwo.add_self_eq_zero]

theorem degree_descentMap {n : ℕ} (a : Fin (n+1) → F₂) (i j : Fin (n+1)) :
    HasDegreeLE (fun z => descentMap a i z j) 1 := by
  refine Fin.succAboveCases i ?_ (fun k => ?_) j
  · simpa [descentMap] using (degree_coordinate (ι := Unit ⊕ Fin n) (.inl ()))
  · simpa [descentMap, mul_comm] using
      (degree_coordinate (ι := Unit ⊕ Fin n) (.inr k)).add
        ((degree_coordinate (ι := Unit ⊕ Fin n) (.inl ())).smul (a (i.succAbove k)))

/-- The first coordinate coefficient is the XOR of the two slices. -/
theorem fiberCoefficient_unit (F : ((Unit ⊕ Fin n) → F₂) → F₂)
    (y : Fin n → F₂) :
    fiberCoefficient F ({()} : Finset Unit) y =
      F (Sum.elim (fun _ => 0) y) + F (Sum.elim (fun _ => 1) y) := by
  have h0 : point (∅ : Finset Unit) = fun _ => (0 : F₂) := by funext u; simp [point]
  have h1 : point ({()} : Finset Unit) = fun _ => (1 : F₂) := by
    funext u; cases u; simp [point]
  unfold fiberCoefficient coefficient
  rw [show ({()} : Finset Unit) = insert () ∅ from rfl,
    transform_insert _ _ _ (by simp)]
  simp [h0, h1]

theorem descentMap_flip {n : ℕ} (a : Fin (n+1) → F₂) (i : Fin (n+1))
    (hi : a i = 1) (t : F₂) (y : Fin n → F₂) :
    descentMap a i (Sum.elim (fun _ => t+1) y) =
      descentMap a i (Sum.elim (fun _ => t) y) + a := by
  apply Fin.insertNth_eq_iff.mpr
  constructor
  · simp [descentMap, hi]
  · funext j
    simp [descentMap, Fin.removeNth]
    ring

/-- Every nonzero Boolean direction admits a degree-lowering quotient on one fewer variable. -/
theorem derivative_descent (n r : ℕ) : DerivativeDescent n r := by
  intro f hf a ha
  have hai : ∃ i, a i = 1 := by
    by_contra hn
    apply ha
    funext i
    have h : a i ≠ 1 := fun h => hn ⟨i, h⟩
    generalize he : a i = z at *
    fin_cases z <;> simp_all
  obtain ⟨i, hi⟩ := hai
  let F : ((Unit ⊕ Fin n) → F₂) → F₂ := fun z => f (descentMap a i z)
  let g : (Fin n → F₂) → F₂ := fiberCoefficient F {()}
  have hF : HasDegreeLE F (r+1) :=
    hf.comp_affine (descentMap a i) (degree_descentMap a i)
  have hg : HasDegreeLE g r := by
    apply HasDegreeLE.fiberCoefficient (d := 1) (e := r)
    · simpa [Nat.add_comm] using hF
    · simp
  have hval (t : Unit → F₂) (y : Fin n → F₂) :
      derivative f a (descentMap a i (Sum.elim t y)) = g y := by
    have ht : t = fun _ => t () := by funext u; cases u; rfl
    rw [ht]
    change f (descentMap a i (Sum.elim (fun _ => t ()) y) + a) +
      f (descentMap a i (Sum.elim (fun _ => t ()) y)) = g y
    rw [← descentMap_flip a i hi]
    change _ = fiberCoefficient F {()} y
    rw [fiberCoefficient_unit]
    generalize he : t () = b
    fin_cases b <;> simp [F, add_comm, CharTwo.add_self_eq_zero]
  have hweight : weight (derivative f a) = 2 * weight g := by
    rw [← weight_equiv (derivative f a) (descentEquiv a i), ← weight_fibers]
    change (∑ y, weight (fun t : Unit → F₂ =>
      derivative f a (descentMap a i (Sum.elim t y)))) = _
    simp_rw [hval]
    simp [weight, Fintype.card_fun, ZMod.card, ← Finset.mul_sum]
  exact ⟨g, hg, hweight, by have hb := weight_derivative_le f a; omega⟩

end BooleanANF
