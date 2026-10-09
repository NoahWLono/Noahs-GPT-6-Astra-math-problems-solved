import CodeBasisProperties
import QuadraticThreeRadicalShape

namespace BooleanANF
open scoped BigOperators
open QuadraticFour

theorem code_polar_expansion {q : DoubleBlock → F₂} {d : ℕ}
    (e : (Fin d → F₂) ≃ₗ[F₂] quadraticCoefficientSpace q)
    (y : Block) (hq : HasDegreeLE (fiber q y) 2) (x z : Block) :
    polar (fiber q y) x z = ∑ i, codeBasisWord e i y * polar (quadraticBasisPart e i) x z := by
  rw [quadraticPart_polar q y hq]
  simp only [polar, quadraticPart_code_expansion e, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem polar_comp_linear (f : Block → F₂) (e : Block →ₗ[F₂] Block) (x y : Block) :
    polar (fun z => f (e z)) x y = polar f (e x) (e y) := by
  simp only [polar, map_add, map_zero]

/-- Reverse three alternating entries, read linearly from the actual code basis
in any chosen x-coordinates. -/
noncomputable def codeRadicalVectorLinear {q : DoubleBlock → F₂}
    (e : TripleBlock ≃ₗ[F₂] quadraticCoefficientSpace q)
    (ex : Block →ₗ[F₂] Block) : TripleBlock →ₗ[F₂] TripleBlock :=
  ∑ i : Fin 3, (LinearMap.proj i).smulRight
    (radicalVector (fun x => quadraticBasisPart e i (ex x)))

theorem radicalVector_code_expansion {q : DoubleBlock → F₂}
    (e : TripleBlock ≃ₗ[F₂] quadraticCoefficientSpace q)
    (ex : Block →ₗ[F₂] Block) (y : Block) (hq : HasDegreeLE (fiber q y) 2) :
    radicalVector (fun x => fiber q y (ex x)) =
      codeRadicalVectorLinear e ex (fun i => codeBasisWord e i y) := by
  funext k
  fin_cases k <;>
    simp only [codeRadicalVectorLinear, LinearMap.sum_apply, LinearMap.smulRight_apply,
      LinearMap.proj_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, radicalVector,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, polar_comp_linear]
  all_goals exact code_polar_expansion e y hq _ _

end BooleanANF
