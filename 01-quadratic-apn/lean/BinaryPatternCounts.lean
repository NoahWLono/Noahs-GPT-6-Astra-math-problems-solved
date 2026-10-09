import BinarySmallCodeEquality

namespace BooleanANF
open scoped BigOperators
variable {Y : Type*} [Fintype Y]

/-- Exact multiplicity of a two-bit evaluation column. -/
def pairPatternCount (a b : Y → F₂) (u v : F₂) : ℕ :=
  ∑ y, if a y = u ∧ b y = v then 1 else 0

/-- Exact multiplicity of a three-bit evaluation column. -/
def triplePatternCount (a b c : Y → F₂) (u v w : F₂) : ℕ :=
  ∑ y, if a y = u ∧ b y = v ∧ c y = w then 1 else 0

private theorem pair_bit_decomposition (a b u v : F₂) :
    (u*a+v*b).val = u.val * (if a=1 ∧ b=0 then 1 else 0) +
      v.val * (if a=0 ∧ b=1 then 1 else 0) +
      (u+v).val * (if a=1 ∧ b=1 then 1 else 0) := by
  fin_cases a <;> fin_cases b <;> fin_cases u <;> fin_cases v <;> decide

theorem pair_pattern_weight (a b : Y → F₂) (u v : F₂) :
    weight (fun y => u*a y + v*b y) =
      u.val * pairPatternCount a b 1 0 + v.val * pairPatternCount a b 0 1 +
      (u+v).val * pairPatternCount a b 1 1 := by
  simp only [weight, pairPatternCount, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun y _ => pair_bit_decomposition (a y) (b y) u v)

private theorem triple_bit_decomposition (a b c u v w : F₂) :
    (u*a+v*b+w*c).val =
      u.val * (if a=1 ∧ b=0 ∧ c=0 then 1 else 0) +
      v.val * (if a=0 ∧ b=1 ∧ c=0 then 1 else 0) +
      (u+v).val * (if a=1 ∧ b=1 ∧ c=0 then 1 else 0) +
      w.val * (if a=0 ∧ b=0 ∧ c=1 then 1 else 0) +
      (u+w).val * (if a=1 ∧ b=0 ∧ c=1 then 1 else 0) +
      (v+w).val * (if a=0 ∧ b=1 ∧ c=1 then 1 else 0) +
      (u+v+w).val * (if a=1 ∧ b=1 ∧ c=1 then 1 else 0) := by
  fin_cases a <;> fin_cases b <;> fin_cases c <;>
    fin_cases u <;> fin_cases v <;> fin_cases w <;> decide

/-- Truth-table weights are the seven character sums of evaluation-column multiplicities. -/
theorem triple_pattern_weight (a b c : Y → F₂) (u v w : F₂) :
    weight (fun y => u*a y + v*b y + w*c y) =
      u.val * triplePatternCount a b c 1 0 0 +
      v.val * triplePatternCount a b c 0 1 0 +
      (u+v).val * triplePatternCount a b c 1 1 0 +
      w.val * triplePatternCount a b c 0 0 1 +
      (u+w).val * triplePatternCount a b c 1 0 1 +
      (v+w).val * triplePatternCount a b c 0 1 1 +
      (u+v+w).val * triplePatternCount a b c 1 1 1 := by
  simp only [weight, triplePatternCount, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun y _ => triple_bit_decomposition (a y) (b y) (c y) u v w)

/-- The actual seven weight-four equations imply the simplex evaluation columns. -/
theorem simplex_pattern_counts (a b c : Y → F₂)
    (h100 : weight a=4) (h010 : weight b=4) (h001 : weight c=4)
    (h110 : weight (fun y => a y+b y)=4)
    (h101 : weight (fun y => a y+c y)=4)
    (h011 : weight (fun y => b y+c y)=4)
    (h111 : weight (fun y => a y+b y+c y)=4) :
    triplePatternCount a b c 1 0 0=1 ∧ triplePatternCount a b c 0 1 0=1 ∧
    triplePatternCount a b c 1 1 0=1 ∧ triplePatternCount a b c 0 0 1=1 ∧
    triplePatternCount a b c 1 0 1=1 ∧ triplePatternCount a b c 0 1 1=1 ∧
    triplePatternCount a b c 1 1 1=1 := by
  have h1 := triple_pattern_weight a b c 1 0 0
  have h2 := triple_pattern_weight a b c 0 1 0
  have h3 := triple_pattern_weight a b c 0 0 1
  have h12 := triple_pattern_weight a b c 1 1 0
  have h13 := triple_pattern_weight a b c 1 0 1
  have h23 := triple_pattern_weight a b c 0 1 1
  have h123 := triple_pattern_weight a b c 1 1 1
  simp only [zero_mul, one_mul, zero_add, add_zero, CharTwo.add_self_eq_zero,
    show (0 : F₂).val = 0 from rfl, show (1 : F₂).val = 1 from rfl,
    h100,h010,h001,h110,h101,h011,h111] at h1 h2 h3 h12 h13 h23 h123
  omega

end BooleanANF
