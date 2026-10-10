import CertifiedField
import ParameterCertificate

namespace ProgressivePool


 theorem certified_field_margin : 262144*128+64 < Fintype.card ParameterField := by
  rw [parameter_field_card]
  norm_num

lemma cast_certificate {a b c : ℕ} (h : a*b < c) : (a : ℚ)*(b : ℚ) < (c : ℚ) := by
  exact_mod_cast h

 theorem certified_tail_probability :
    ((Nat.choose (262144*128+64) 33 : ℕ) : ℚ) /
      (((Fintype.card ParameterField-(262144*128+64) : ℕ) : ℚ)^33) <
        (1 : ℚ) / 2^286 := by
  rw [parameter_field_card]
  apply (div_lt_div_iff₀ (by norm_num) (by norm_num)).mpr
  have hh := cast_certificate choose_tail_certificate
  simp only [Nat.cast_pow] at hh
  convert hh using 1 <;> norm_num

 theorem certified_confidence_ratio : (((33-1 : ℕ) : ℚ)/(64 : ℚ)) = 1/2 := by
  norm_num

theorem certified_global_error (E : ℕ) (hE : E ≤ 2^64) :
    (E : ℚ) * (((Nat.choose (262144*128+64) 33 : ℕ) : ℚ) /
      (((Fintype.card ParameterField-(262144*128+64) : ℕ) : ℚ)^33)) <
        (1 : ℚ) / 2^222 := by
  let delta : ℚ := ((Nat.choose (262144*128+64) 33 : ℕ) : ℚ) /
    (((Fintype.card ParameterField-(262144*128+64) : ℕ) : ℚ)^33)
  have hd : 0 ≤ delta := div_nonneg (Nat.cast_nonneg _) (pow_nonneg (Nat.cast_nonneg _) _)
  have he : (E : ℚ) ≤ (2 : ℚ)^64 := by exact_mod_cast hE
  calc
    _ ≤ (2 : ℚ)^64 * delta := mul_le_mul_of_nonneg_right he hd
    _ < (2 : ℚ)^64 * (1 / 2^286) :=
      mul_lt_mul_of_pos_left certified_tail_probability (by norm_num)
    _ = (1 : ℚ) / 2^222 := by norm_num

#print axioms certified_field_margin
#print axioms certified_tail_probability
#print axioms certified_confidence_ratio
#print axioms certified_global_error
end ProgressivePool
