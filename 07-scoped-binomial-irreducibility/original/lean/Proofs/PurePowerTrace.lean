import Mathlib.RingTheory.Trace.Basic
import Mathlib.Algebra.GCDMonoid.IntegrallyClosed
import Mathlib.Tactic.Ring
import Mathlib.Data.Nat.ModEq

/-! Actual multiplication-matrix trace formulas for a pure power basis. -/
set_option autoImplicit false
open scoped BigOperators
open Algebra
namespace PillaiTrace
universe u v
variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
variable [Nontrivial S]

lemma power_reduce (B : PowerBasis R S) (k : R)
    (hpow : B.gen^B.dim=algebraMap R S k) (m : ℕ) :
    B.gen^m=k^(m/B.dim) • B.basis ⟨m%B.dim,Nat.mod_lt _ B.dim_pos⟩ := by
  rw [B.basis_eq_pow,Algebra.smul_def,map_pow,← hpow,← pow_mul,← pow_add]
  congr 1
  exact (Nat.div_add_mod m B.dim).symm

lemma repr_power (B : PowerBasis R S) (k : R)
    (hpow : B.gen^B.dim=algebraMap R S k) (m : ℕ) (i : Fin B.dim) :
    B.basis.repr (B.gen^m) i=if m%B.dim=i.val then k^(m/B.dim) else 0 := by
  rw [power_reduce B k hpow m]
  simp only [map_smul,Finsupp.smul_apply,Module.Basis.repr_self,Finsupp.single_apply,smul_eq_mul]
  split_ifs with h h' h'
  · simp
  · exact False.elim (h' (congrArg Fin.val h))
  · exact False.elim (h (Fin.ext h'))
  · simp

/-- The trace is computed directly from all diagonal entries of the multiplication matrix. -/
theorem trace_power (B : PowerBasis R S) (k : R)
    (hpow : B.gen^B.dim=algebraMap R S k) (m : ℕ) :
    Algebra.trace R S (B.gen^m)=if B.dim∣m then (B.dim : R)*k^(m/B.dim) else 0 := by
  classical
  rw [Algebra.trace_eq_matrix_trace B.basis,Matrix.trace]
  simp only [Matrix.diag,Algebra.leftMulMatrix_eq_repr_mul,B.basis_eq_pow,← pow_add]
  simp_rw [repr_power B k hpow]
  by_cases hd : B.dim∣m
  · rw [if_pos hd]
    have hm : m%B.dim=0 := Nat.mod_eq_zero_of_dvd hd
    have hh (i : Fin B.dim) : (m+i.val)%B.dim=i.val ∧ (m+i.val)/B.dim=m/B.dim := by
      constructor
      · simp [Nat.add_mod,hm,Nat.mod_eq_of_lt i.isLt]
      · calc
          (m+i.val)/B.dim = (i.val+B.dim*(m/B.dim))/B.dim := by rw [Nat.mul_div_cancel' hd,Nat.add_comm]
          _ = i.val/B.dim+m/B.dim := Nat.add_mul_div_left _ _ B.dim_pos
          _ = m/B.dim := by rw [Nat.div_eq_of_lt i.isLt,zero_add]
    simp only [(hh _).1,(hh _).2,if_true,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  · rw [if_neg hd]
    apply Finset.sum_eq_zero
    intro i _
    rw [if_neg]
    intro hi
    apply hd
    apply Nat.dvd_of_mod_eq_zero
    have hh : Nat.ModEq B.dim (m+i.val) (0+i.val) := by
      simpa only [Nat.ModEq,zero_add,Nat.mod_eq_of_lt i.isLt] using hi
    simpa only [Nat.ModEq,Nat.zero_mod] using hh.add_right_cancel' i.val

lemma trace_basis (B : PowerBasis R S) (k : R)
    (hpow : B.gen^B.dim=algebraMap R S k) (i : Fin B.dim) :
    Algebra.trace R S (B.basis i)=if i.val=0 then (B.dim : R) else 0 := by
  rw [B.basis_eq_pow,trace_power B k hpow]
  by_cases hi : i.val=0
  · simp [hi]
  · rw [if_neg hi,if_neg (Nat.not_dvd_of_pos_of_lt (Nat.pos_of_ne_zero hi) i.isLt)]

/-- The trace extracts the constant coordinate with its exact degree factor. -/
theorem trace_eq_constant_coordinate (B : PowerBasis R S) (k : R)
    (hpow : B.gen^B.dim=algebraMap R S k) (z : S) :
    Algebra.trace R S z=(B.dim : R)*B.basis.repr z ⟨0,B.dim_pos⟩ := by
  classical
  conv_lhs => rw [← B.basis.sum_repr z]
  rw [map_sum]
  simp_rw [map_smul,trace_basis B k hpow,smul_eq_mul]
  simp only [mul_ite,mul_zero]
  have heq (i : Fin B.dim) : i.val=0 ↔ i=⟨0,B.dim_pos⟩ := ⟨fun h ↦ Fin.ext h,fun h ↦ congrArg Fin.val h⟩
  simp_rw [heq]
  simp only [Finset.sum_ite_eq',Finset.mem_univ,if_true]
  ring

lemma trace_basis_mul (B : PowerBasis R S) (k : R)
    (hpow : B.gen^B.dim=algebraMap R S k) (i j : Fin B.dim) (hj : 0<j.val) :
    Algebra.trace R S (B.basis i*B.gen^(B.dim-j.val))=
      if i=j then (B.dim : R)*k else 0 := by
  classical
  rw [B.basis_eq_pow,← pow_add,trace_power B k hpow]
  by_cases hij : i=j
  · subst i
    have hh : j.val+(B.dim-j.val)=B.dim := by omega
    simp [hh,Nat.div_self B.dim_pos]
  · rw [if_neg hij,if_neg]
    intro hd
    have hh := Nat.eq_of_dvd_of_lt_two_mul (by omega : i.val+(B.dim-j.val)≠0) hd
      (by omega : i.val+(B.dim-j.val)<2*B.dim)
    apply hij
    apply Fin.ext
    omega

/-- Multiplication by the complementary generator power extracts any nonconstant coordinate. -/
theorem trace_mul_eq_coordinate (B : PowerBasis R S) (k : R)
    (hpow : B.gen^B.dim=algebraMap R S k) (z : S) (j : Fin B.dim) (hj : 0<j.val) :
    Algebra.trace R S (z*B.gen^(B.dim-j.val))=
      (B.dim : R)*k*B.basis.repr z j := by
  classical
  conv_lhs => rw [← B.basis.sum_repr z]
  rw [Finset.sum_mul,map_sum]
  simp_rw [smul_mul_assoc,map_smul,trace_basis_mul B k hpow _ j hj,smul_eq_mul]
  simp only [mul_ite,mul_zero,Finset.sum_ite_eq',Finset.mem_univ,if_true]
  ring

end PillaiTrace
