import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.CharP.Two
import Mathlib.Tactic.FinCases

/-! Canonical squarefree Boolean algebraic normal form, using subcube sums.
These are standard Boolean Fourier/Möbius facts used by the APN application. -/
namespace BooleanANF
open scoped BigOperators
variable {ι : Type*} [DecidableEq ι]
abbrev F₂ := ZMod 2

/-- The characteristic point of a finite set of coordinates. -/
def point (s : Finset ι) : ι → F₂ := fun i => if i ∈ s then 1 else 0

/-- Boolean Möbius transform. In characteristic two it is its own inverse. -/
def transform (f : Finset ι → F₂) (s : Finset ι) : F₂ :=
  ∑ t ∈ s.powerset, f t

@[simp] theorem transform_empty (f : Finset ι → F₂) : transform f ∅ = f ∅ := by
  simp [transform]

theorem transform_insert (f : Finset ι → F₂) (s : Finset ι) (i : ι) (hi : i ∉ s) :
    transform f (insert i s) = transform f s + transform (fun t => f (insert i t)) s := by
  exact Finset.sum_powerset_insert hi f

theorem transform_add (f g : Finset ι → F₂) (s : Finset ι) :
    transform (fun t => f t + g t) s = transform f s + transform g s := by
  simp [transform, Finset.sum_add_distrib]

/-- Canonical inversion, proved for arbitrary dimension rather than enumerated. -/
theorem transform_involutive (f : Finset ι → F₂) (s : Finset ι) :
    transform (transform f) s = f s := by
  induction s using Finset.induction_on generalizing f with
  | empty => simp
  | @insert i s hi ih =>
    rw [transform_insert _ _ _ hi, ih]
    have h : transform (fun t => transform f (insert i t)) s =
        transform (fun t => transform f t + transform (fun u => f (insert i u)) t) s := by
      apply Finset.sum_congr rfl
      intro t ht
      exact transform_insert f t i (fun hit => hi ((Finset.mem_powerset.mp ht) hit))
    rw [h, transform_add, ih, ih]
    simpa only [← add_assoc, CharTwo.add_self_eq_zero, zero_add]

/-- Coefficient of the squarefree monomial indexed by `s`. -/
def coefficient (f : (ι → F₂) → F₂) (s : Finset ι) : F₂ :=
  transform (fun t => f (point t)) s

/-- Degree is defined directly by the canonical coefficients, not by a chosen expression. -/
def HasDegreeLE (f : (ι → F₂) → F₂) (d : ℕ) : Prop :=
  ∀ s : Finset ι, d < s.card → coefficient f s = 0

theorem coefficient_add (f g : (ι → F₂) → F₂) (s : Finset ι) :
    coefficient (fun x => f x + g x) s = coefficient f s + coefficient g s :=
  transform_add _ _ _

/-- Evaluation of the canonical ANF at a characteristic point. -/
theorem reconstruction_point (f : (ι → F₂) → F₂) (s : Finset ι) :
    (∑ t ∈ s.powerset, coefficient f t) = f (point s) :=
  transform_involutive _ _

section Finite
variable [Fintype ι]

def support (x : ι → F₂) : Finset ι := Finset.univ.filter (fun i => x i = 1)

@[simp] theorem point_support (x : ι → F₂) : point (support x) = x := by
  funext i
  have h : x i = 0 ∨ x i = 1 := by
    generalize x i = z
    fin_cases z <;> simp_all
  rcases h with h | h <;> simp [point, support, h]

@[simp] theorem support_point (s : Finset ι) : support (point s) = s := by
  ext i
  simp [support, point]

/-- Every Boolean function equals its unique squarefree ANF. -/
theorem reconstruction (f : (ι → F₂) → F₂) (x : ι → F₂) :
    (∑ s ∈ (support x).powerset, coefficient f s) = f x := by
  simpa using reconstruction_point f (support x)

theorem coefficient_injective {f g : (ι → F₂) → F₂}
    (h : coefficient f = coefficient g) : f = g := by
  funext x
  rw [← reconstruction f x, ← reconstruction g x, h]

/-- A coefficient array determines precisely those coefficients under reconstruction. -/
theorem coefficient_reconstruct (c : Finset ι → F₂) :
    coefficient (fun x => transform c (support x)) = c := by
  funext s
  simp only [coefficient, support_point]
  exact transform_involutive c s


/-- Squarefree monomial, evaluated as the indicator that all its coordinates are one. -/
def monomial (s : Finset ι) (x : ι → F₂) : F₂ :=
  if s ⊆ support x then 1 else 0

theorem monomial_eq_transform (s : Finset ι) (x : ι → F₂) :
    monomial s x = transform (fun t => if t = s then 1 else 0) (support x) := by
  simp [monomial, transform]

theorem coefficient_monomial (s t : Finset ι) :
    coefficient (monomial s) t = if t = s then 1 else 0 := by
  have h : monomial s = fun x => transform (fun u => if u = s then 1 else 0) (support x) :=
    funext (monomial_eq_transform s)
  rw [h, coefficient_reconstruct]

theorem monomial_union (s t : Finset ι) (x : ι → F₂) :
    monomial (s ∪ t) x = monomial s x * monomial t x := by
  by_cases hs : s ⊆ support x <;> by_cases ht : t ⊆ support x <;>
    simp [monomial, Finset.union_subset_iff, hs, ht]

theorem coefficient_smul (a : F₂) (f : (ι → F₂) → F₂) (s : Finset ι) :
    coefficient (fun x => a * f x) s = a * coefficient f s := by
  simp [coefficient, transform, Finset.mul_sum]

theorem coefficient_sum {κ : Type*} (I : Finset κ) (f : κ → (ι → F₂) → F₂)
    (s : Finset ι) :
    coefficient (fun x => ∑ k ∈ I, f k x) s = ∑ k ∈ I, coefficient (f k) s := by
  simp only [coefficient, transform]
  exact Finset.sum_comm

theorem reconstruction_all (f : (ι → F₂) → F₂) (x : ι → F₂) :
    (∑ s : Finset ι, coefficient f s * monomial s x) = f x := by
  rw [← reconstruction f x]
  simp only [monomial, mul_ite, mul_one, mul_zero]
  rw [← Finset.sum_filter]
  congr 1
  ext s
  simp

theorem HasDegreeLE.mono {f : (ι → F₂) → F₂} {d e : ℕ}
    (h : HasDegreeLE f d) (hde : d ≤ e) : HasDegreeLE f e := by
  intro s hs
  exact h s (lt_of_le_of_lt hde hs)

theorem HasDegreeLE.add {f g : (ι → F₂) → F₂} {d : ℕ}
    (hf : HasDegreeLE f d) (hg : HasDegreeLE g d) :
    HasDegreeLE (fun x => f x + g x) d := by
  intro s hs
  rw [coefficient_add, hf s hs, hg s hs, zero_add]

theorem HasDegreeLE.smul {f : (ι → F₂) → F₂} {d : ℕ}
    (hf : HasDegreeLE f d) (a : F₂) : HasDegreeLE (fun x => a * f x) d := by
  intro s hs
  rw [coefficient_smul, hf s hs, mul_zero]

theorem HasDegreeLE.sum {κ : Type*} (I : Finset κ) (f : κ → (ι → F₂) → F₂)
    (d : ℕ) (hf : ∀ k ∈ I, HasDegreeLE (f k) d) :
    HasDegreeLE (fun x => ∑ k ∈ I, f k x) d := by
  intro s hs
  rw [coefficient_sum]
  exact Finset.sum_eq_zero (fun k hk => hf k hk s hs)

theorem degree_monomial (s : Finset ι) : HasDegreeLE (monomial s) s.card := by
  intro t ht
  rw [coefficient_monomial, if_neg]
  intro h
  subst t
  exact (lt_irrefl _ ht)


theorem degree_zero (d : ℕ) : HasDegreeLE (fun _ : ι → F₂ => 0) d := by
  intro s hs
  simp [coefficient, transform]

theorem HasDegreeLE.mul {f g : (ι → F₂) → F₂} {d e : ℕ}
    (hf : HasDegreeLE f d) (hg : HasDegreeLE g e) :
    HasDegreeLE (fun x => f x * g x) (d + e) := by
  have hrepr : (fun x => f x * g x) =
      fun x => ∑ s : Finset ι, ∑ t : Finset ι,
        (coefficient f s * coefficient g t) * monomial (s ∪ t) x := by
    funext x
    rw [← reconstruction_all f x, ← reconstruction_all g x, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro s hs
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro t ht
    rw [monomial_union]
    ring
  rw [hrepr]
  apply HasDegreeLE.sum
  intro s hs
  apply HasDegreeLE.sum
  intro t ht
  by_cases hsd : d < s.card
  · simp only [hf s hsd, zero_mul]
    exact degree_zero _
  by_cases hte : e < t.card
  · simp only [hg t hte, mul_zero, zero_mul]
    exact degree_zero _
  exact ((degree_monomial (s ∪ t)).mono
    (le_trans (Finset.card_union_le s t) (Nat.add_le_add (Nat.le_of_not_gt hsd)
      (Nat.le_of_not_gt hte)))).smul _

theorem monomial_empty : monomial (∅ : Finset ι) = fun _ => 1 := by
  funext x
  simp [monomial]

theorem degree_const (a : F₂) : HasDegreeLE (fun _ : ι → F₂ => a) 0 := by
  have h := (degree_monomial (∅ : Finset ι)).smul a
  simpa [monomial_empty] using h

theorem monomial_singleton (i : ι) : monomial {i} = fun x => x i := by
  funext x
  have h : x i = 0 ∨ x i = 1 := by
    generalize x i = z
    fin_cases z <;> simp_all
  rcases h with h | h <;> simp [monomial, support, h]

theorem degree_coordinate (i : ι) : HasDegreeLE (fun x : ι → F₂ => x i) 1 := by
  simpa [monomial_singleton] using degree_monomial ({i} : Finset ι)

theorem monomial_eq_prod (s : Finset ι) (x : ι → F₂) :
    monomial s x = ∏ i ∈ s, x i := by
  induction s using Finset.induction_on with
  | empty => simp [monomial_empty]
  | @insert i s hi ih =>
    have he : insert i s = ({i} : Finset ι) ∪ s := by ext j; simp
    rw [he, monomial_union, monomial_singleton, ih]
    rw [← he, Finset.prod_insert hi]

theorem HasDegreeLE.prod {κ : Type*} (I : Finset κ) (f : κ → (ι → F₂) → F₂)
    (d : κ → ℕ) (hf : ∀ k ∈ I, HasDegreeLE (f k) (d k)) :
    HasDegreeLE (fun x => ∏ k ∈ I, f k x) (∑ k ∈ I, d k) := by
  classical
  induction I using Finset.induction_on with
  | empty => simpa using degree_const (ι := ι) 1
  | @insert i I hi ih =>
    simp only [Finset.prod_insert hi, Finset.sum_insert hi]
    exact (hf i (Finset.mem_insert_self i I)).mul
      (ih (fun k hk => hf k (Finset.mem_insert_of_mem hk)))

/-- Affine coordinate substitutions preserve canonical algebraic degree. -/
theorem HasDegreeLE.comp_affine {κ : Type*} [DecidableEq κ] [Fintype κ]
    {f : (ι → F₂) → F₂} {d : ℕ} (hf : HasDegreeLE f d)
    (a : (κ → F₂) → (ι → F₂))
    (ha : ∀ i, HasDegreeLE (fun x => a x i) 1) :
    HasDegreeLE (fun x => f (a x)) d := by
  have hrepr : (fun x => f (a x)) =
      fun x => ∑ s : Finset ι, coefficient f s * monomial s (a x) := by
    funext x
    exact (reconstruction_all f (a x)).symm
  rw [hrepr]
  apply HasDegreeLE.sum
  intro s hs
  by_cases hsd : d < s.card
  · simp only [hf s hsd, zero_mul]
    exact degree_zero _
  have hm : HasDegreeLE (fun x => monomial s (a x)) s.card := by
    simp only [monomial_eq_prod]
    simpa using HasDegreeLE.prod s (fun i x => a x i) (fun _ => 1)
      (fun i _ => ha i)
  exact (hm.mono (Nat.le_of_not_gt hsd)).smul _

end Finite
end BooleanANF
