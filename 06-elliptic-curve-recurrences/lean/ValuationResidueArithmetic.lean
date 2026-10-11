import Mathlib.RingTheory.Valuation.IsTrivialOn
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! Arithmetic of prescribed constant residues, stated directly using the
actual valuation inequality v(a-c)<1. No residue-field oracle is introduced. -/
namespace Astra01
noncomputable section
variable {k K : Type*} [Field k] [Field K] [Algebra k K]
variable (v : Valuation K (WithZero (Multiplicative ℤ))) [v.IsTrivialOn k]

def HasConstantResidue (a : K) (c : k) : Prop := v (a - algebraMap k K c) < 1
namespace HasConstantResidue
variable {v} {a b : K} {c d : k}

theorem constant (c : k) : HasConstantResidue v (algebraMap k K c) c := by
  simp [HasConstantResidue]

theorem le_one (h : HasConstantResidue v a c) : v a ≤ 1 := by
  rw [← sub_add_cancel a (algebraMap k K c)]
  exact v.map_add_le h.le (Valuation.IsTrivialOn.valuation_algebraMap_le_one v c)

theorem add (ha : HasConstantResidue v a c) (hb : HasConstantResidue v b d) :
    HasConstantResidue v (a + b) (c + d) := by
  unfold HasConstantResidue at *
  rw [map_add, show a + b - (algebraMap k K c + algebraMap k K d) =
    (a - algebraMap k K c) + (b - algebraMap k K d) by ring]
  exact v.map_add_lt ha hb

theorem neg (ha : HasConstantResidue v a c) : HasConstantResidue v (-a) (-c) := by
  unfold HasConstantResidue at *
  rw [map_neg, show -a - -algebraMap k K c = -(a - algebraMap k K c) by ring, v.map_neg]
  exact ha

theorem sub (ha : HasConstantResidue v a c) (hb : HasConstantResidue v b d) :
    HasConstantResidue v (a - b) (c - d) := by
  simpa only [sub_eq_add_neg] using ha.add hb.neg

theorem mul (ha : HasConstantResidue v a c) (hb : HasConstantResidue v b d) :
    HasConstantResidue v (a * b) (c * d) := by
  unfold HasConstantResidue
  rw [map_mul, show a * b - algebraMap k K c * algebraMap k K d =
    (a - algebraMap k K c) * b + algebraMap k K c * (b - algebraMap k K d) by ring]
  apply v.map_add_lt
  · rw [map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_right zero_le hb.le_one) ha
  · rw [map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_left zero_le
      (Valuation.IsTrivialOn.valuation_algebraMap_le_one v c)) hb

theorem pow (ha : HasConstantResidue v a c) (n : ℕ) :
    HasConstantResidue v (a ^ n) (c ^ n) := by
  induction n with
  | zero => simpa using (constant (v := v) (1 : k))
  | succ n ih => simpa only [pow_succ] using ih.mul ha

theorem valuation_eq_one (ha : HasConstantResidue v a c) (hc : c ≠ 0) : v a = 1 := by
  have hcv : v (algebraMap k K c) = 1 := Valuation.IsTrivialOn.eq_one c hc
  have hv : v ((a - algebraMap k K c) + algebraMap k K c) = v (algebraMap k K c) :=
    v.map_add_eq_of_lt_right (hcv ▸ ha)
  simpa only [sub_add_cancel, hcv] using hv

theorem inv (ha : HasConstantResidue v a c) (hc : c ≠ 0) :
    HasConstantResidue v a⁻¹ c⁻¹ := by
  have hav := ha.valuation_eq_one hc
  have ha0 : a ≠ 0 := by intro h; simpa [h] using hav
  have hc0 : algebraMap k K c ≠ 0 := (map_ne_zero _).mpr hc
  have hcv : v (algebraMap k K c) = 1 := Valuation.IsTrivialOn.eq_one c hc
  unfold HasConstantResidue
  rw [map_inv₀, show a⁻¹ - (algebraMap k K c)⁻¹ =
    -(a - algebraMap k K c) / (a * algebraMap k K c) by field_simp; ring]
  rw [map_div₀, v.map_neg, map_mul, hav, hcv, one_mul, div_one]
  exact ha

theorem div (ha : HasConstantResidue v a c) (hb : HasConstantResidue v b d) (hd : d ≠ 0) :
    HasConstantResidue v (a / b) (c / d) := by
  simpa only [div_eq_mul_inv] using ha.mul (hb.inv hd)

end HasConstantResidue
end
end Astra01
#print axioms Astra01.HasConstantResidue.div
