import WeightThirtyModel
import BinaryPatternCounts

namespace BooleanANF
open scoped BigOperators
local instance : Fact (Nat.Prime 2) := ⟨by decide⟩
variable {Y : Type*} [DecidableEq Y] [Fintype Y]

noncomputable def codeEquiv (D : Submodule F₂ (Y → F₂)) (d : ℕ)
    (hd : Module.finrank F₂ D = d) : (Fin d → F₂) ≃ₗ[F₂] D :=
  LinearEquiv.ofFinrankEq _ _ (by simp [Module.finrank_pi, hd])

def codeBasisWord {d : ℕ} {D : Submodule F₂ (Y → F₂)}
    (e : (Fin d → F₂) ≃ₗ[F₂] D) (i : Fin d) : Y → F₂ :=
  (e (Pi.single i 1)).val

theorem code_word_expansion {d : ℕ} {D : Submodule F₂ (Y → F₂)}
    (e : (Fin d → F₂) ≃ₗ[F₂] D) (u : Fin d → F₂) (y : Y) :
    (e u).val y = ∑ i : Fin d, u i * codeBasisWord e i y := by
  have hu : u = ∑ i : Fin d, u i • (Pi.single i 1 : Fin d → F₂) := by
    funext j
    simp [Finset.sum_apply, Pi.smul_apply, Pi.single_apply]
  conv_lhs => rw [hu, map_sum]
  simp [map_smul, codeBasisWord, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]

theorem code_word_ne_zero {d : ℕ} {D : Submodule F₂ (Y → F₂)}
    (e : (Fin d → F₂) ≃ₗ[F₂] D) {u : Fin d → F₂} (hu : u ≠ 0) :
    (e u).val ≠ 0 := by
  intro h
  apply hu
  apply e.injective
  apply Subtype.ext
  simpa using h

theorem codeBasisWord_ne_zero {d : ℕ} {D : Submodule F₂ (Y → F₂)}
    (e : (Fin d → F₂) ≃ₗ[F₂] D) (i : Fin d) : codeBasisWord e i ≠ 0 := by
  apply code_word_ne_zero
  intro h
  have hi := congrFun h i
  simpa using hi

abbrev QuadraticIndex := {s : Finset (Fin 4) // s.card = 2}

def coefficientCodeWord (q : DoubleBlock → F₂) (s : QuadraticIndex) :
    quadraticCoefficientSpace q :=
  ⟨fiberCoefficient q s.val, Submodule.subset_span ⟨s,rfl⟩⟩

noncomputable def quadraticCoordinates {q : DoubleBlock → F₂} {d : ℕ}
    (e : (Fin d → F₂) ≃ₗ[F₂] quadraticCoefficientSpace q) (s : QuadraticIndex) :
    Fin d → F₂ := e.symm (coefficientCodeWord q s)

def quadraticPart (q : DoubleBlock → F₂) (y x : Block) : F₂ :=
  ∑ s : QuadraticIndex, fiberCoefficient q s.val y * monomial s.val x

noncomputable def quadraticBasisPart {q : DoubleBlock → F₂} {d : ℕ}
    (e : (Fin d → F₂) ≃ₗ[F₂] quadraticCoefficientSpace q) (i : Fin d) (x : Block) : F₂ :=
  ∑ s : QuadraticIndex, quadraticCoordinates e s i * monomial s.val x

theorem coefficient_code_expansion {q : DoubleBlock → F₂} {d : ℕ}
    (e : (Fin d → F₂) ≃ₗ[F₂] quadraticCoefficientSpace q) (s : QuadraticIndex) (y : Block) :
    fiberCoefficient q s.val y =
      ∑ i : Fin d, quadraticCoordinates e s i * codeBasisWord e i y := by
  have hh := code_word_expansion e (quadraticCoordinates e s) y
  simpa [quadraticCoordinates, coefficientCodeWord] using hh

/-- Canonical tensor decomposition of the actual quadratic x-part along a basis of its code. -/
theorem quadraticPart_code_expansion {q : DoubleBlock → F₂} {d : ℕ}
    (e : (Fin d → F₂) ≃ₗ[F₂] quadraticCoefficientSpace q) (y x : Block) :
    quadraticPart q y x = ∑ i : Fin d, codeBasisWord e i y * quadraticBasisPart e i x := by
  unfold quadraticPart quadraticBasisPart
  simp_rw [coefficient_code_expansion e, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro s hs
  ring

end BooleanANF

namespace BooleanANF
open scoped BigOperators

/-- Extracting a basis quadratic's squarefree coefficient recovers the code-coordinate matrix. -/
theorem coefficient_quadraticBasisPart {q : DoubleBlock → F₂} {d : ℕ}
    (e : (Fin d → F₂) ≃ₗ[F₂] quadraticCoefficientSpace q) (i : Fin d)
    (s : QuadraticIndex) :
    coefficient (quadraticBasisPart e i) s.val = quadraticCoordinates e s i := by
  classical
  unfold quadraticBasisPart
  rw [coefficient_sum]
  simp_rw [coefficient_smul, coefficient_monomial]
  rw [Finset.sum_eq_single s]
  · simp
  · intro t ht hts
    have hval : s.val ≠ t.val := fun h => hts (Subtype.ext h.symm)
    simp [hval]
  · simp

def dotLinear {d : ℕ} (u : Fin d → F₂) : (Fin d → F₂) →ₗ[F₂] F₂ where
  toFun v := ∑ i, u i * v i
  map_add' v w := by simp [mul_add, Finset.sum_add_distrib]
  map_smul' a v := by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring

/-- The homogeneous quadratic parts are independent because their coordinate words span D. -/
theorem quadraticBasis_combination_eq_zero {q : DoubleBlock → F₂} {d : ℕ}
    (e : (Fin d → F₂) ≃ₗ[F₂] quadraticCoefficientSpace q) (u : Fin d → F₂)
    (hu : (fun x => ∑ i : Fin d, u i * quadraticBasisPart e i x) = 0) : u = 0 := by
  classical
  let L : quadraticCoefficientSpace q →ₗ[F₂] F₂ := (dotLinear u).comp e.symm.toLinearMap
  have hgen (s : QuadraticIndex) : L (coefficientCodeWord q s) = 0 := by
    have hc := congrArg (fun f : Block → F₂ => coefficient f s.val) hu
    dsimp only at hc
    rw [coefficient_sum] at hc
    simp_rw [coefficient_smul, coefficient_quadraticBasisPart] at hc
    simpa [L, dotLinear, quadraticCoordinates, coefficient, transform] using hc
  have hkill (g : Block → F₂) (hg : g ∈ quadraticCoefficientSpace q) : L ⟨g,hg⟩ = 0 := by
    induction hg using Submodule.span_induction with
    | mem g hg =>
      obtain ⟨s,rfl⟩ := hg
      exact hgen s
    | zero => exact L.map_zero
    | add x y hx hy ihx ihy =>
      change L (⟨x,hx⟩ + ⟨y,hy⟩) = 0
      rw [map_add, ihx, ihy, zero_add]
    | smul a x hx ih =>
      change L (a • ⟨x,hx⟩) = 0
      rw [map_smul, ih, smul_zero]
  funext i
  have hh := hkill (e (Pi.single i 1)).val (e (Pi.single i 1)).property
  simpa [L, dotLinear, Pi.single_apply] using hh

theorem quadraticBasis_combination_ne_zero {q : DoubleBlock → F₂} {d : ℕ}
    (e : (Fin d → F₂) ≃ₗ[F₂] quadraticCoefficientSpace q) {u : Fin d → F₂}
    (hu : u ≠ 0) : (fun x => ∑ i : Fin d, u i * quadraticBasisPart e i x) ≠ 0 :=
  fun h => hu (quadraticBasis_combination_eq_zero e u h)

end BooleanANF
