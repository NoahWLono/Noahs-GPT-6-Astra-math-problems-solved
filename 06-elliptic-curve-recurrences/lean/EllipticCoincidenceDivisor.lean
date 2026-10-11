import EllipticFiberDegree
import ValuationResidueArithmetic

/-! The actual coincidence divisor div(f-g)+poles(f)+poles(g).
This includes simultaneous poles, where a naive zero-divisor argument fails.
Agreement is stated directly through the actual valuations and constant residues. -/
namespace Astra01.EllipticPointDivisor
noncomputable section
open WeierstrassCurve.Affine.Chart FunctionField.Chart
open scoped RatFunc Polynomial
variable {k : Type*} [Field k] [IsAlgClosed k]
variable (W : WeierstrassCurve.Affine k) [W.IsElliptic]
variable (K : Type*) [Field K] [Algebra W.CoordinateRing K] [IsFractionRing W.CoordinateRing K]
variable [Algebra k[X] K] [IsScalarTower k[X] W.CoordinateRing K]
  [Algebra k⟮X⟯ K] [IsScalarTower k[X] k⟮X⟯ K]
  [_root_.FunctionField k K] [Algebra.IsSeparable k⟮X⟯ K]

theorem point_valuation_unit (f : Kˣ) (P : W.Point) :
    placeValuation k K (placeOfPoint W K P) (f : K) =
      WithZero.exp (-principalDivisor W K (Additive.ofMul f) P) :=
  point_valuation_eq W K (Additive.ofMul f) P

/-- Signed expression for the coincidence divisor. Its effectivity is proved below. -/
def coincidenceDivisor (f g h : Kˣ) : W.Point →₀ ℤ :=
  principalDivisor W K (Additive.ofMul h) +
    (poleDivisor W K f).mapRange (fun n : ℕ => (n : ℤ)) (by rfl) +
    (poleDivisor W K g).mapRange (fun n : ℕ => (n : ℤ)) (by rfl)

theorem coincidenceDivisor_apply (f g h : Kˣ) (P : W.Point) :
    coincidenceDivisor W K f g h P = principalDivisor W K (Additive.ofMul h) P +
      (-(principalDivisor W K (Additive.ofMul f) P)).toNat +
      (-(principalDivisor W K (Additive.ofMul g) P)).toNat := by
  rfl

theorem order_sub_ge_min (f g h : Kˣ) (hh : (h : K) = (f : K) - (g : K)) (P : W.Point) :
    min (principalDivisor W K (Additive.ofMul f) P)
      (principalDivisor W K (Additive.ofMul g) P) ≤
      principalDivisor W K (Additive.ofMul h) P := by
  let v := placeValuation k K (placeOfPoint W K P)
  have hv : v (h : K) ≤ max (v (f : K)) (v (g : K)) := by
    rw [hh]
    exact v.map_sub _ _
  dsimp only [v] at hv
  rw [point_valuation_unit W K h P, point_valuation_unit W K f P, point_valuation_unit W K g P] at hv
  rcases le_total (principalDivisor W K (Additive.ofMul f) P)
    (principalDivisor W K (Additive.ofMul g) P) with hle | hle
  · rw [min_eq_left hle]
    rw [max_eq_left (WithZero.exp_le_exp.mpr (neg_le_neg hle))] at hv
    exact neg_le_neg_iff.mp (WithZero.exp_le_exp.mp hv)
  · rw [min_eq_right hle]
    rw [max_eq_right (WithZero.exp_le_exp.mpr (neg_le_neg hle))] at hv
    exact neg_le_neg_iff.mp (WithZero.exp_le_exp.mp hv)

theorem coincidenceDivisor_nonneg (f g h : Kˣ)
    (hh : (h : K) = (f : K) - (g : K)) (P : W.Point) :
    0 ≤ coincidenceDivisor W K f g h P := by
  rw [coincidenceDivisor_apply]
  have ho := order_sub_ge_min W K f g h hh P
  omega

theorem coincidenceDivisor_degree (f g h : Kˣ) :
    (coincidenceDivisor W K f g h).sum (fun _ n => n) =
      (divisorDegree W (poleDivisor W K f) : ℤ) +
      (divisorDegree W (poleDivisor W K g) : ℤ) := by
  classical
  simp only [coincidenceDivisor, Finsupp.sum_add_index' (h := fun (_ : W.Point) (n : ℤ) => n) (fun _ => rfl) (fun _ _ _ => rfl),
    sum_principalDivisor_eq_zero, zero_add,
    Finsupp.sum_mapRange_index (h := fun (_ : W.Point) (n : ℤ) => n) (fun _ => (rfl : (0 : ℤ) = 0))]
  simp only [divisorDegree, Finsupp.sum, Nat.cast_sum]

variable [Algebra k K] [IsScalarTower k k[X] K]

/-- Equality of projective values, expressed intrinsically through valuations:
either both values are infinity, or they have the same finite constant residue. -/
def ProjectiveAgreement (f g : K) (P : W.Point) : Prop :=
  let v := placeValuation k K (placeOfPoint W K P)
  (1 < v f ∧ 1 < v g) ∨ ∃ c : k,
    v (f - algebraMap k K c) < 1 ∧ v (g - algebraMap k K c) < 1

theorem coincidenceDivisor_pos_of_agreement (f g h : Kˣ)
    (hh : (h : K) = (f : K) - (g : K)) (P : W.Point)
    (hagree : ProjectiveAgreement W K (f : K) (g : K) P) :
    1 ≤ coincidenceDivisor W K f g h P := by
  let v := placeValuation k K (placeOfPoint W K P)
  rw [coincidenceDivisor_apply]
  rcases hagree with ⟨hf, hg⟩ | ⟨c, hf, hg⟩
  · rw [point_valuation_unit W K f P, ← WithZero.exp_zero] at hf
    rw [point_valuation_unit W K g P, ← WithZero.exp_zero] at hg
    have hfo := WithZero.exp_lt_exp.mp hf
    have hgo := WithZero.exp_lt_exp.mp hg
    have ho := order_sub_ge_min W K f g h hh P
    omega
  · have hv : v (h : K) < 1 := by
      rw [hh, show (f : K) - (g : K) =
        ((f : K) - algebraMap k K c) - ((g : K) - algebraMap k K c) by ring]
      exact v.map_sub_lt hf hg
    dsimp only [v] at hv
    rw [point_valuation_unit W K h P, ← WithZero.exp_zero] at hv
    have ho := WithZero.exp_lt_exp.mp hv
    omega

/-- The genuine coincidence bound on any finite set of distinct curve points.
It counts both finite-value agreements and simultaneous poles. -/
theorem projective_agreement_card_le (f g h : Kˣ)
    (hh : (h : K) = (f : K) - (g : K)) (S : Finset W.Point)
    (hS : ∀ P ∈ S, ProjectiveAgreement W K (f : K) (g : K) P) :
    S.card ≤ divisorDegree W (poleDivisor W K f) +
      divisorDegree W (poleDivisor W K g) := by
  classical
  let d := coincidenceDivisor W K f g h
  have hs : S ⊆ d.support := by
    intro P hP
    apply Finsupp.mem_support_iff.mpr
    have hp := coincidenceDivisor_pos_of_agreement W K f g h hh P (hS P hP)
    change d P ≠ 0
    change 1 ≤ d P at hp
    omega
  have hle : (S.card : ℤ) ≤ d.sum (fun _ n => n) := by
    calc
      (S.card : ℤ) = ∑ _P ∈ S, (1 : ℤ) := by simp
      _ ≤ ∑ P ∈ S, d P := Finset.sum_le_sum fun P hP =>
        coincidenceDivisor_pos_of_agreement W K f g h hh P (hS P hP)
      _ ≤ ∑ P ∈ d.support, d P := Finset.sum_le_sum_of_subset_of_nonneg hs
        (fun P _ _ => coincidenceDivisor_nonneg W K f g h hh P)
      _ = d.sum (fun _ n => n) := rfl
  rw [show d.sum (fun _ n => n) = _ from coincidenceDivisor_degree W K f g h] at hle
  exact_mod_cast hle

end
end Astra01.EllipticPointDivisor
#print axioms Astra01.EllipticPointDivisor.projective_agreement_card_le
