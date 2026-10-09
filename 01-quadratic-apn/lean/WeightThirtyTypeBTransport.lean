import WeightThirtyTypeB

namespace BooleanANF

def blockDiagonalEquiv (ex ey : Block ≃ₗ[F₂] Block) : DoubleBlock ≃ₗ[F₂] DoubleBlock :=
  (LinearEquiv.sumArrowLequivProdArrow (Fin 4) (Fin 4) F₂ F₂).trans
    ((ex.prodCongr ey).trans
      (LinearEquiv.sumArrowLequivProdArrow (Fin 4) (Fin 4) F₂ F₂).symm)

@[simp] theorem blockDiagonalEquiv_apply (ex ey : Block ≃ₗ[F₂] Block) (x y : Block) :
    blockDiagonalEquiv ex ey (Sum.elim x y) = Sum.elim (ex x) (ey y) := rfl

theorem cost_linearEquiv (f : Block → F₂) (e : Block ≃ₗ[F₂] Block) :
    cost (fun x => f (e x)) = cost f := by
  have hw : weight (fun x => f (e x)) = weight f := weight_equiv f e.toEquiv
  simp only [cost, hw, map_zero]

/-- Separate linear x/y coordinates and a translation in y transport the actual
residual signal without moving its distinguished delta-zero x-fiber. -/
theorem typeB_of_coordinates (q : DoubleBlock → F₂) (p : Block)
    (ex ey : Block ≃ₗ[F₂] Block)
    (hq : ∀ x y : Block, q (Sum.elim (ex x) (p + ey y)) = typeBResidual (Sum.elim x y)) :
    TwoTransverseFlats (residualSignal q) := by
  have heq : (fun z => residualSignal q (Sum.elim (0 : Block) p + blockDiagonalEquiv ex ey z)) =
      residualSignal typeBResidual := by
    funext z
    let x : Block := fun i => z (.inl i)
    let y : Block := fun i => z (.inr i)
    have hz : z = Sum.elim x y := by funext i; cases i <;> rfl
    rw [hz]
    have hadd : Sum.elim (0 : Block) p + Sum.elim (ex x) (ey y) =
        Sum.elim (ex x) (p + ey y) := by
      funext i
      cases i <;> simp
    rw [blockDiagonalEquiv_apply, hadd]
    change delta 0 (ex x) + q (Sum.elim (ex x) (p+ey y)) =
      delta 0 x + typeBResidual (Sum.elim x y)
    rw [hq]
    have hd : delta 0 (ex x) = delta 0 x := by
      have hx : ex x = 0 ↔ x = 0 := by
        constructor
        · intro hh
          exact ex.injective (hh.trans (map_zero ex).symm)
        · intro hh
          rw [hh,map_zero]
      simp only [delta, hx]
    rw [hd]
  apply TwoTransverseFlats.of_affine_coordinates (residualSignal q)
    (Sum.elim (0 : Block) p) (blockDiagonalEquiv ex ey)
  rw [heq]
  exact typeB_twoTransverseFlats

end BooleanANF
