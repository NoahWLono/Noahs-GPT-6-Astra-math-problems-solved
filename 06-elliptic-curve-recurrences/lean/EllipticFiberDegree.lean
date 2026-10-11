import EllipticPointDivisor

/-! Actual zero/pole divisors on the elliptic point type. The finite-fiber
multiplicity for f = c is the positive part of div(f-c). Its degree is
proved equal to the pole degree of f, using the global product formula
and the actual point valuations. Translation covariance is not assumed
or established in this module. -/
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

def zeroDivisor (f : Kˣ) : W.Point →₀ ℕ :=
  (principalDivisor W K (Additive.ofMul f)).mapRange Int.toNat (by rfl)

def poleDivisor (f : Kˣ) : W.Point →₀ ℕ :=
  (principalDivisor W K (Additive.ofMul f)).mapRange (fun z => (-z).toNat) (by rfl)

def divisorDegree (d : W.Point →₀ ℕ) : ℕ := d.sum (fun _ n => n)

theorem zero_degree_eq_pole_degree (f : Kˣ) :
    divisorDegree W (zeroDivisor W K f) = divisorDegree W (poleDivisor W K f) := by
  classical
  unfold divisorDegree zeroDivisor poleDivisor
  rw [Finsupp.sum_mapRange_index (fun _ => (rfl : (0 : ℕ) = 0)),
    Finsupp.sum_mapRange_index (fun _ => (rfl : (0 : ℕ) = 0))]
  have hz := sum_principalDivisor_eq_zero W K f
  set d := principalDivisor W K (Additive.ofMul f)
  change d.sum (fun _ z => z) = 0 at hz
  have hsum : ((d.sum (fun _ z => z.toNat) : ℕ) : ℤ) -
      ((d.sum (fun _ z => (-z).toNat) : ℕ) : ℤ) = d.sum (fun _ z => z) := by
    simp only [Finsupp.sum, Nat.cast_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro P _
    omega
  apply Int.ofNat.inj
  exact sub_eq_zero.mp (hsum.trans hz)

variable [Algebra k K] [IsScalarTower k k[X] K]

theorem poleDivisor_sub_constant (f g : Kˣ) (c : k)
    (hg : (g : K) = (f : K) - algebraMap k K c) :
    poleDivisor W K g = poleDivisor W K f := by
  classical
  ext P
  simp only [poleDivisor, Finsupp.mapRange_apply]
  let v := placeValuation k K (placeOfPoint W K P)
  let df := principalDivisor W K (Additive.ofMul f) P
  let dg := principalDivisor W K (Additive.ofMul g) P
  have hfval : v (f : K) = WithZero.exp (-df) := point_valuation_eq W K _ P
  have hgval : v (g : K) = WithZero.exp (-dg) := point_valuation_eq W K _ P
  have hc : v (algebraMap k K c) ≤ 1 := placeValuation_algebraMap_le_one k K _ c
  change (-dg).toNat = (-df).toNat
  by_cases hd : 0 ≤ df
  · have hf_le : v (f : K) ≤ 1 := by
      rw [hfval, ← WithZero.exp_zero]
      exact WithZero.exp_le_exp.mpr (neg_nonpos.mpr hd)
    have hg_le : v (g : K) ≤ 1 := by
      rw [hg]
      exact v.map_sub_le hf_le hc
    have hdg : 0 ≤ dg := by
      rw [hgval, ← WithZero.exp_zero] at hg_le
      exact neg_nonpos.mp (WithZero.exp_le_exp.mp hg_le)
    omega
  · have hf_gt : 1 < v (f : K) := by
      rw [hfval, ← WithZero.exp_zero]
      exact WithZero.exp_lt_exp.mpr (neg_pos.mpr (lt_of_not_ge hd))
    have heq : v (g : K) = v (f : K) := by
      rw [hg]
      exact v.map_sub_eq_of_lt_left (hc.trans_lt hf_gt)
    rw [hgval, hfval] at heq
    have hdf : dg = df := neg_injective (WithZero.exp_injective heq)
    rw [hdf]

/-- Every finite fiber f=c, counted by its actual zero multiplicities,
has the same degree as the pole divisor, provided f and f-c are nonzero. -/
theorem finite_fiber_degree_eq_pole_degree (f g : Kˣ) (c : k)
    (hg : (g : K) = (f : K) - algebraMap k K c) :
    divisorDegree W (zeroDivisor W K g) = divisorDegree W (poleDivisor W K f) := by
  rw [zero_degree_eq_pole_degree, poleDivisor_sub_constant W K f g c hg]

/-- For an actual nonconstant elliptic function, every finite fiber has
pole degree. Nonconstancy means it is not any base-field constant; it
supplies both required nonzero proofs rather than hiding them in a witness. -/
theorem nonconstant_finite_fiber_degree (f : K)
    (hf : ∀ c : k, f ≠ algebraMap k K c) (c : k) :
    divisorDegree W (zeroDivisor W K
      (Units.mk0 (f - algebraMap k K c) (sub_ne_zero.mpr (hf c)))) =
    divisorDegree W (poleDivisor W K
      (Units.mk0 f (by simpa using hf (0 : k)))) := by
  exact finite_fiber_degree_eq_pole_degree W K _ _ c rfl

#print axioms nonconstant_finite_fiber_degree
#print axioms zero_degree_eq_pole_degree
#print axioms poleDivisor_sub_constant
#print axioms finite_fiber_degree_eq_pole_degree
end
end Astra01.EllipticPointDivisor
