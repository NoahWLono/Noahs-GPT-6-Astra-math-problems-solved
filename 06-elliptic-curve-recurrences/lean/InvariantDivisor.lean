import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Data.Finsupp.Basic
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

/-! The finite weighted-orbit step of ASTRA-01's invariant-fiber argument.
This proves a genuine combinatorial theorem. It does not assume or assert
that an elliptic-curve fiber divisor has the needed geometric properties. -/
namespace Astra01
noncomputable section

private theorem free_action_card_dvd {G X : Type*} [Group G] [Finite G] [Finite X]
    [MulAction G X] [IsCancelSMul G X] : Nat.card G ∣ Nat.card X := by
  let e := MulAction.selfEquivOrbitsQuotientProd
    (fun x : X => IsCancelSMul.stabilizer_eq_bot (G := G) x)
  rw [Nat.card_congr e, Nat.card_prod]
  exact Nat.dvd_mul_left _ _

private abbrev WeightedCopies {X : Type*} (w : X → ℕ) :=
  {p : X × ℕ // p.2 < w p.1}

private def copiesEquivSigma {X : Type*} (w : X → ℕ) :
    WeightedCopies w ≃ (Σ x : X, Fin (w x)) where
  toFun p := ⟨p.val.1, ⟨p.val.2,p.property⟩⟩
  invFun p := ⟨(p.1,p.2.val),p.2.isLt⟩
  left_inv _ := rfl
  right_inv _ := rfl

@[implicit_reducible] private def copiesAction {G X : Type*} [Group G] [MulAction G X]
    (w : X → ℕ) (hw : ∀ (g : G) (x : X), w (g • x) = w x) : MulAction G (WeightedCopies w) where
  smul g p := ⟨(g • p.val.1, p.val.2), by rw [hw]; exact p.property⟩
  one_smul p := Subtype.ext (by
    change ((1 : G) • p.val.1, p.val.2) = (p.val.1,p.val.2)
    rw [one_smul])
  mul_smul g h p := Subtype.ext (by
    change ((g*h) • p.val.1,p.val.2) = (g • h • p.val.1,p.val.2)
    rw [mul_smul])

/-- A finite group acting freely on a finite set has order dividing the sum
of any natural-valued weight that is invariant under its action. -/
theorem invariant_weight_sum_dvd {G X : Type*} [Group G] [Fintype G] [Fintype X]
    [MulAction G X] [IsCancelSMul G X]
    (w : X → ℕ) (hw : ∀ (g : G) (x : X), w (g • x) = w x) :
    Fintype.card G ∣ ∑ x, w x := by
  letI : Fintype (WeightedCopies w) := Fintype.ofEquiv _ (copiesEquivSigma w).symm
  letI : MulAction G (WeightedCopies w) := copiesAction w hw
  letI : IsCancelSMul G (WeightedCopies w) := {
    right_cancel' := fun g h p heq =>
      IsCancelSMul.right_cancel g h p.val.1 (congrArg (fun q : WeightedCopies w => q.val.1) heq) }
  have hdvd := free_action_card_dvd (G := G) (X := WeightedCopies w)
  rw [Nat.card_congr (copiesEquivSigma w)] at hdvd
  simpa only [Nat.card_eq_fintype_card, Fintype.card_sigma, Fintype.card_fin] using hdvd

@[implicit_reducible] private def supportAction {G X : Type*} [Group G] [MulAction G X]
    (d : X →₀ ℕ) (hd : ∀ (g : G) (x : X), d (g • x) = d x) : MulAction G {x // x ∈ d.support} where
  smul g x := ⟨g • x.val, by
    rw [Finsupp.mem_support_iff, hd]
    exact Finsupp.mem_support_iff.mp x.property⟩
  one_smul x := Subtype.ext (by
    change (1 : G) • x.val = x.val
    exact one_smul G x.val)
  mul_smul g h x := Subtype.ext (by
    change (g*h) • x.val = g • h • x.val
    exact mul_smul g h x.val)

/-- A finite-support effective divisor invariant under a free finite group
action has degree divisible by the group order. The ambient set may be infinite. -/
theorem invariant_finsupp_degree_dvd {G X : Type*} [Group G] [Fintype G]
    [MulAction G X] [IsCancelSMul G X]
    (d : X →₀ ℕ) (hd : ∀ (g : G) (x : X), d (g • x) = d x) :
    Fintype.card G ∣ d.sum (fun _ m => m) := by
  classical
  let S := {x // x ∈ d.support}
  letI : MulAction G S := supportAction d hd
  letI : IsCancelSMul G S := {
    right_cancel' := fun g h x heq =>
      IsCancelSMul.right_cancel g h x.val (congrArg (fun y : S => y.val) heq) }
  have hweight : ∀ g (x : S), d (g • x).val = d x.val := fun g x => hd g x.val
  have h := invariant_weight_sum_dvd (G := G) (X := S) (fun x => d x.val) hweight
  simpa only [S, Finsupp.sum, Finset.sum_coe_sort] using h

/-- The finite-support effective-divisor conclusion used by T1: invariance
under translation by a finite-order point forces its order to divide total
multiplicity. This holds in any additive commutative group. -/
theorem translation_invariant_degree_dvd {A : Type*} [AddCommGroup A]
    (G : A) (d : A →₀ ℕ) (hG : 0 < addOrderOf G)
    (hd : ∀ P, d (P+G) = d P) : addOrderOf G ∣ d.sum (fun _ m => m) := by
  classical
  let H := AddSubgroup.zmultiples G
  let R := Multiplicative H
  let e : Fin (addOrderOf G) ≃ H := finEquivZMultiples (addOrderOf_pos_iff.mp hG)
  letI : Fintype H := Fintype.ofEquiv _ e
  letI : Fintype R := Fintype.ofEquiv H
    ⟨Multiplicative.ofAdd, Multiplicative.toAdd, fun _ => rfl, fun _ => rfl⟩
  letI : MulAction R A := {
    smul := fun g P => ((Multiplicative.toAdd g : H) : A) + P
    one_smul := fun P => by change (0 : A)+P=P; exact zero_add P
    mul_smul := fun g h P => by
      change (((Multiplicative.toAdd g : H) : A)+((Multiplicative.toAdd h : H) : A))+P =
        ((Multiplicative.toAdd g : H) : A)+(((Multiplicative.toAdd h : H) : A)+P)
      exact add_assoc _ _ _ }
  letI : IsCancelSMul R A := {
    right_cancel' := fun g h P heq => by
      change ((Multiplicative.toAdd g : H) : A)+P = ((Multiplicative.toAdd h : H) : A)+P at heq
      have heq' : Multiplicative.toAdd g = Multiplicative.toAdd h := Subtype.ext (add_right_cancel heq)
      exact congrArg Multiplicative.ofAdd heq' }
  have hdnat : ∀ i : ℕ, ∀ P : A, d (i • G + P) = d P := by
    intro i
    induction i with
    | zero => intro P; simp
    | succ i ih =>
      intro P
      calc
        d ((i+1) • G + P) = d ((i • G + P)+G) := by
          congr 1
          simp [add_nsmul, add_comm, add_left_comm]
        _ = d (i • G + P) := hd _
        _ = d P := ih P
  have hinvariant : ∀ (g : R) (P : A), d (g • P) = d P := by
    intro g P
    obtain ⟨i,hi⟩ := e.surjective (Multiplicative.toAdd g)
    have hval := congrArg Subtype.val hi
    change i.val • G = ((Multiplicative.toAdd g : H) : A) at hval
    change d (((Multiplicative.toAdd g : H) : A)+P) = d P
    rw [← hval]
    exact hdnat i.val P
  have hcard : Fintype.card R = addOrderOf G := by
    calc
      Fintype.card R = Fintype.card H := Fintype.card_congr
        ⟨Multiplicative.toAdd, Multiplicative.ofAdd, fun _ => rfl, fun _ => rfl⟩
      _ = Fintype.card (Fin (addOrderOf G)) := (Fintype.card_congr e).symm
      _ = addOrderOf G := Fintype.card_fin _
  simpa only [hcard] using invariant_finsupp_degree_dvd (G := R) d hinvariant

#print axioms translation_invariant_degree_dvd
#print axioms invariant_weight_sum_dvd
#print axioms invariant_finsupp_degree_dvd
end
end Astra01
