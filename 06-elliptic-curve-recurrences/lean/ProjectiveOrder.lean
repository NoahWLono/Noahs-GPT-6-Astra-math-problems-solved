import ProjectiveFieldCondition
import PrimeOrbit
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic.FinCases

/-! Three fixed projective points force scalar action in dimension two.
This is the missing fixed-point bridge toward exact projective order. -/
namespace Astra01
noncomputable section
open scoped MatrixGroups LinearAlgebra.Projectivization

variable {K : Type*} [Field K]
abbrev Plane (K : Type*) := Fin 2 → K

private theorem scalar_of_two_eigenvectors (F : Module.End K (Plane K))
    (v w : Plane K) (a : K) (hind : LinearIndependent K ![v,w])
    (hv : F v = a • v) (hw : F w = a • w) : F = a • LinearMap.id := by
  apply LinearMap.ext_on_range (hind.span_eq_top_of_card_eq_finrank (by simp))
  intro i
  fin_cases i <;> simp [hv, hw]

/-- Three pairwise independent eigenlines in dimension two force a scalar
linear map. This uses genuine linear independence and dimension, not a
fixed-point cardinality assumption. -/
theorem scalar_of_three_eigenlines (F : Module.End K (Plane K))
    (v w u : Plane K) (hv0 : v ≠ 0) (hw0 : w ≠ 0) (hu0 : u ≠ 0)
    (hvw : LinearIndependent K ![v,w])
    (hvu : LinearIndependent K ![v,u])
    (hwu : LinearIndependent K ![w,u])
    (a b c : K) (hv : F v = a • v) (hw : F w = b • w) (hu : F u = c • u) :
    ∃ d : K, F = d • LinearMap.id := by
  by_cases hab : a = b
  · exact ⟨a, scalar_of_two_eigenvectors F v w a hvw hv (by simpa only [hab] using hw)⟩
  by_cases hac : a = c
  · exact ⟨a, scalar_of_two_eigenvectors F v u a hvu hv (by simpa only [hac] using hu)⟩
  by_cases hbc : b = c
  · exact ⟨b, scalar_of_two_eigenvectors F w u b hwu hw (by simpa only [hbc] using hu)⟩
  have hvalues : Function.Injective (![a,b,c] : Fin 3 → K) := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all
  have hev : ∀ i : Fin 3, F.HasEigenvector (![a,b,c] i) (![v,w,u] i) := by
    intro i
    fin_cases i
    · exact ⟨Module.End.mem_eigenspace_iff.mpr hv, hv0⟩
    · exact ⟨Module.End.mem_eigenspace_iff.mpr hw, hw0⟩
    · exact ⟨Module.End.mem_eigenspace_iff.mpr hu, hu0⟩
  have hlin := F.eigenvectors_linearIndependent' ![a,b,c] hvalues ![v,w,u] hev
  have hdim := hlin.fintype_card_le_finrank
  simp at hdim

private theorem eigenvector_of_projective_fixed
    (F : Module.End K (Plane K)) (hF : Function.Injective F)
    (x : ℙ K (Plane K)) (hx : Projectivization.map F hF x = x) :
    ∃ a : K, F x.rep = a • x.rep := by
  rw [← Projectivization.mk_rep x, Projectivization.map_mk,
    Projectivization.mk_eq_mk_iff'] at hx
  obtain ⟨a, ha⟩ := hx
  exact ⟨a, ha.symm⟩

/-- Three distinct fixed points on the actual projective line imply that
an injective linear map is scalar. No algebraic closure is required. -/
theorem scalar_of_three_projective_fixed
    (F : Module.End K (Plane K)) (hF : Function.Injective F)
    (x y z : ℙ K (Plane K)) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hx : Projectivization.map F hF x = x)
    (hy : Projectivization.map F hF y = y)
    (hz : Projectivization.map F hF z = z) : ∃ a : K, F = a • LinearMap.id := by
  obtain ⟨a, ha⟩ := eigenvector_of_projective_fixed F hF x hx
  obtain ⟨b, hb⟩ := eigenvector_of_projective_fixed F hF y hy
  obtain ⟨c, hc⟩ := eigenvector_of_projective_fixed F hF z hz
  exact scalar_of_three_eigenlines F x.rep y.rep z.rep
    x.rep_nonzero y.rep_nonzero z.rep_nonzero
    (Projectivization.linearIndependent_pair_iff_ne.mpr hxy)
    (Projectivization.linearIndependent_pair_iff_ne.mpr hxz)
    (Projectivization.linearIndependent_pair_iff_ne.mpr hyz)
    a b c ha hb hc

local instance : MulAction (GL (Fin 2) K) (ℙ K (Plane K)) := projectiveMatrixAction

/-- A projective transformation fixing three distinct points fixes every
point. This refers to its actual action, not the order of a matrix lift. -/
theorem projective_identity_of_three_fixed
    (M : GL (Fin 2) K) (x y z : ℙ K (Plane K))
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hx : M • x = x) (hy : M • y = y) (hz : M • z = z) :
    ∀ t : ℙ K (Plane K), M • t = t := by
  let F : Module.End K (Plane K) := Matrix.GeneralLinearGroup.toLin M
  have hF : Function.Injective F := (Matrix.GeneralLinearGroup.toLin M).toLinearEquiv.injective
  obtain ⟨a, ha⟩ := scalar_of_three_projective_fixed F hF x y z hxy hxz hyz hx hy hz
  intro t
  change Projectivization.map F hF t = t
  rw [← Projectivization.mk_rep t, Projectivization.map_mk,
    Projectivization.mk_eq_mk_iff']
  exact ⟨a, by simp [ha]⟩

/-- For a nonconstant prime cyclic recurrence of length at least three,
the induced projective permutation has exact order n. The matrix lift itself
is deliberately not asserted to have that order. -/
theorem projective_recurrence_exact_order
    (M : GL (Fin 2) K) (z : ℕ → ℙ K (Plane K)) (n : ℕ)
    (hn : n.Prime) (hn3 : 3 ≤ n)
    (hstep : ∀ i < n, z (i+1) = M • z i)
    (hclose : z n = z 0) (hnonconstant : ∃ i < n, z i ≠ z 0) :
    orderOf (MulAction.toPermHom (GL (Fin 2) K) (ℙ K (Plane K)) M) = n := by
  have hinj := prime_recurrence_injective (M • ·) z n hn hstep hclose hnonconstant
  have hindex : ∀ i j, i < n → j < n → z i = z j → i = j := by
    intro i j hi hj hij
    exact congrArg Fin.val (hinj (a₁ := ⟨i,hi⟩) (a₂ := ⟨j,hj⟩) hij)
  have h01 : z 0 ≠ z 1 := by intro h; have := hindex 0 1 (by omega) (by omega) h; omega
  have h02 : z 0 ≠ z 2 := by intro h; have := hindex 0 2 (by omega) (by omega) h; omega
  have h12 : z 1 ≠ z 2 := by intro h; have := hindex 1 2 (by omega) (by omega) h; omega
  have hz : ∀ i, i ≤ n → z i = (M • ·)^[i] (z 0) := by
    intro i
    induction i with
    | zero => intro _; rfl
    | succ i ih =>
      intro hi
      rw [hstep i (Nat.lt_of_succ_le hi), ih (Nat.le_of_succ_le hi)]
      exact (Function.iterate_succ_apply' (M • ·) i (z 0)).symm
  have hper : Function.IsPeriodicPt (M • ·) n (z 0) := by
    change (M • ·)^[n] (z 0) = z 0
    rw [← hz n (Nat.le_refl n)]
    exact hclose
  have hfix : ∀ i, i ≤ n → M^n • z i = z i := by
    intro i hi
    apply MulAction.isPeriodicPt_smul_iff.mp
    rw [hz i hi]
    exact hper.apply_iterate i
  have hid := projective_identity_of_three_fixed (M^n) (z 0) (z 1) (z 2)
    h01 h02 h12 (hfix 0 (by omega)) (hfix 1 (by omega)) (hfix 2 (by omega))
  have hpow : (MulAction.toPermHom (GL (Fin 2) K) (ℙ K (Plane K)) M)^n = 1 := by
    rw [← map_pow]
    ext t
    exact hid t
  rcases (Nat.dvd_prime hn).mp (orderOf_dvd_of_pow_eq_one hpow) with hone | heq
  · have hm := orderOf_eq_one_iff.mp hone
    have hf : M • z 0 = z 0 := congrArg (fun e : Equiv.Perm (ℙ K (Plane K)) => e (z 0)) hm
    exact (h01 (by rw [hstep 0 hn.pos, hf])).elim
  · exact heq

#print axioms projective_recurrence_exact_order
#print axioms scalar_of_three_eigenlines
#print axioms scalar_of_three_projective_fixed
#print axioms projective_identity_of_three_fixed
end
end Astra01
