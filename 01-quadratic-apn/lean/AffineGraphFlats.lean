import WeightThirtyModel

namespace BooleanANF

def graphShearLinear (L : Block →ₗ[F₂] Block) : DoubleBlock →ₗ[F₂] DoubleBlock where
  toFun z := Sum.elim (fun i => z (.inl i))
    (fun i => z (.inr i) + L (fun j => z (.inl j)) i)
  map_add' z w := by
    funext i
    cases i with
    | inl i => rfl
    | inr i =>
      change (z (.inr i) + w (.inr i)) + L ((fun j => z (.inl j)) + (fun j => w (.inl j))) i = _
      rw [map_add]
      simp only [Pi.add_apply, Sum.elim_inr]
      ring
  map_smul' a z := by
    funext i
    cases i with
    | inl i => rfl
    | inr i =>
      change a * z (.inr i) + L (a • (fun j => z (.inl j))) i = _
      rw [map_smul]
      simp only [Pi.smul_apply, smul_eq_mul, Sum.elim_inr, RingHom.id_apply]
      ring

theorem graphShearLinear_involutive (L : Block →ₗ[F₂] Block) (z : DoubleBlock) :
    graphShearLinear L (graphShearLinear L z) = z := by
  funext i
  cases i with
  | inl i => rfl
  | inr i => simp [graphShearLinear, add_assoc, CharTwo.add_self_eq_zero]

/-- An affine graph and the vertical four-flat are always transverse. -/
theorem affine_graph_two_flats (q : DoubleBlock → F₂) (c : Block)
    (L : Block →ₗ[F₂] Block)
    (hq : ∀ x y : Block, q (Sum.elim x y) = delta (c + L x) y) :
    TwoTransverseFlats (residualSignal q) := by
  let e : DoubleBlock ≃ₗ[F₂] DoubleBlock := LinearEquiv.ofBijective (graphShearLinear L)
    (Function.Involutive.bijective (graphShearLinear_involutive L))
  refine ⟨Sum.elim 0 c, e, ?_⟩
  intro x y
  have he : Sum.elim (0 : Block) c + e (Sum.elim x y) = Sum.elim x (c + y + L x) := by
    funext i
    cases i with
    | inl i => simp [e, graphShearLinear]
    | inr i => simp [e, graphShearLinear, add_assoc]
  rw [he]
  change delta 0 x + q (Sum.elim x (c+y+L x)) = delta 0 x + delta 0 y
  rw [hq, add_right_comm c y (L x)]
  congr 1
  simp [delta, add_eq_left]

end BooleanANF
