import BinarySmallCodeEquality
import AffineSingletonNormalization
import QuadraticFourWeights

namespace BooleanANF
open scoped BigOperators
local instance : Fact (Nat.Prime 2) := ⟨by decide⟩

/-- Canonical degree bounds form genuine linear subspaces of Boolean functions. -/
def degreeSubmodule {ι : Type*} [DecidableEq ι] [Fintype ι] (d : ℕ) :
    Submodule F₂ ((ι → F₂) → F₂) where
  carrier := {f | HasDegreeLE f d}
  zero_mem' := degree_zero d
  add_mem' hf hg := hf.add hg
  smul_mem' a f hf := hf.smul a

/-- Functions whose support lies in a specified finite set form a subspace. -/
def supportedSubmodule {Y : Type*} [DecidableEq Y] (E : Finset Y) :
    Submodule F₂ (Y → F₂) where
  carrier := {f | ∀ y, y ∉ E → f y = 0}
  zero_mem' := by simp
  add_mem' := by intro f g hf hg y hy; simp [hf y hy, hg y hy]
  smul_mem' := by intro a f hf y hy; simp [hf y hy]

/-- The six quadratic x-coefficient functions generate the small coefficient code. -/
def quadraticCoefficientSpace (q : DoubleBlock → F₂) : Submodule F₂ (Block → F₂) :=
  Submodule.span F₂ (Set.range (fun s : {s : Finset (Fin 4) // s.card = 2} =>
    fiberCoefficient q s.val))

def activeRows (q : DoubleBlock → F₂) : Finset Block :=
  Finset.univ.filter (fun y => fiber q y ≠ 0)

theorem quadraticCoefficientSpace_degree {q : DoubleBlock → F₂}
    (hq : HasDegreeLE q 4) : quadraticCoefficientSpace q ≤ degreeSubmodule 2 := by
  apply Submodule.span_le.mpr
  rintro g ⟨s,rfl⟩
  exact HasDegreeLE.fiberCoefficient (d := 2) (e := 2) hq s.val (by omega)

theorem quadraticCoefficientSpace_supported (q : DoubleBlock → F₂) :
    quadraticCoefficientSpace q ≤ supportedSubmodule (activeRows q) := by
  apply Submodule.span_le.mpr
  rintro g ⟨s,rfl⟩
  intro y hy
  have hzero : fiber q y = 0 := by
    simpa [activeRows] using hy
  change coefficient (fiber q y) s.val = 0
  rw [hzero]
  simp [coefficient, transform]

/-- The dimension-three bound for the actual coefficient space of the normalized quartic. -/
theorem quadraticCoefficientSpace_finrank {q : DoubleBlock → F₂}
    (hq : HasDegreeLE q 4) (hs : (activeRows q).card ≤ 7) :
    Module.finrank F₂ (quadraticCoefficientSpace q) ≤ 3 := by
  apply small_code_finrank_le_three (quadraticCoefficientSpace q) (activeRows q) hs
  · intro f hf
    exact quadraticCoefficientSpace_supported q hf
  · intro f hf hn
    exact QuadraticFour.quadratic_min_weight (quadraticCoefficientSpace_degree hq hf) hn

/-- The normalized weight-thirty residual has a code of dimension at most three. -/
theorem residual_coefficientSpace_finrank {f : DoubleBlock → F₂}
    (hf : HasDegreeLE f 4) (hw : weight f = 30) (y₀ a : Block)
    (hsingle : fiber f y₀ = delta a) :
    Module.finrank F₂ (quadraticCoefficientSpace (residual f)) ≤ 3 := by
  apply quadraticCoefficientSpace_finrank (residual_degree hf)
  exact residual_active_count hf hw y₀ a hsingle


/-- Coordinates where the quadratic part is active; affine-only rows are excluded. -/
def coefficientRows (q : DoubleBlock → F₂) : Finset Block :=
  Finset.univ.filter (fun y => ∃ s : {s : Finset (Fin 4) // s.card = 2},
    fiberCoefficient q s.val y ≠ 0)

theorem coefficientRows_subset_active (q : DoubleBlock → F₂) :
    coefficientRows q ⊆ activeRows q := by
  intro y hy
  obtain ⟨s,hs⟩ := (Finset.mem_filter.mp hy).2
  simp only [activeRows, Finset.mem_filter, Finset.mem_univ, true_and]
  intro hz
  apply hs
  change coefficient (fiber q y) s.val = 0
  rw [hz]
  simp [coefficient, transform]

theorem quadraticCoefficientSpace_supported_coefficients (q : DoubleBlock → F₂) :
    quadraticCoefficientSpace q ≤ supportedSubmodule (coefficientRows q) := by
  apply Submodule.span_le.mpr
  rintro g ⟨s,rfl⟩
  intro y hy
  by_contra hn
  exact hy (Finset.mem_filter.mpr ⟨Finset.mem_univ y, ⟨s,hn⟩⟩)

/-- The equality case rules out every affine-only active row and yields a simplex code. -/
theorem coefficientSpace_dimension_three {q : DoubleBlock → F₂}
    (hq : HasDegreeLE q 4) (hs : (activeRows q).card ≤ 7)
    (hd : Module.finrank F₂ (quadraticCoefficientSpace q) = 3) :
    (coefficientRows q).card = 7 ∧ coefficientRows q = activeRows q ∧
      ∀ f ∈ quadraticCoefficientSpace q, f ≠ 0 → weight f = 4 := by
  have hsub := coefficientRows_subset_active q
  have he : (coefficientRows q).card ≤ 7 := (Finset.card_le_card hsub).trans hs
  have hh := small_code_dimension_three (quadraticCoefficientSpace q) (coefficientRows q) he
    (fun f hf => quadraticCoefficientSpace_supported_coefficients q hf)
    (fun f hf hn => QuadraticFour.quadratic_min_weight
      (quadraticCoefficientSpace_degree hq hf) hn) hd
  refine ⟨hh.1, ?_, hh.2⟩
  exact Finset.eq_of_subset_of_card_le hsub (by omega)

/-- Code dimension zero means every already-quadratic x-row is affine. -/
theorem affine_rows_of_coefficientSpace_zero {q : DoubleBlock → F₂}
    (hrows : ∀ y, HasDegreeLE (fiber q y) 2)
    (hD : quadraticCoefficientSpace q = ⊥) :
    ∀ y, HasDegreeLE (fiber q y) 1 := by
  intro y s hs
  by_cases hcard : s.card = 2
  · have hm : fiberCoefficient q s ∈ quadraticCoefficientSpace q :=
      Submodule.subset_span ⟨⟨s,hcard⟩,rfl⟩
    rw [hD] at hm
    have hz : fiberCoefficient q s = 0 := by simpa using hm
    exact congrFun hz y
  · exact hrows y s (by omega)

end BooleanANF
