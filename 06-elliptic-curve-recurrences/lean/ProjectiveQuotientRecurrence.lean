import ProjectiveQuotientAction
import CyclicFieldTheorem

namespace Astra01
noncomputable section
open scoped MatrixGroups LinearAlgebra.Projectivization
variable {F K : Type*} [Field F] [Fintype F] [Field K] [Fintype K] [Algebra F K]
local instance : MulAction (GL (Fin 2) K) (ℙ K (Plane K)) := projectiveMatrixAction
local instance : MulAction (PGL(2,K)) (ℙ K (Plane K)) := projectiveQuotientAction

theorem pgl_recurrence_exact_order (m : PGL(2,K)) (z : ℕ → ℙ K (Plane K)) (n : ℕ)
    (hn : n.Prime) (hn3 : 3 ≤ n)
    (hstep : ∀ i < n, z (i+1) = m • z i)
    (hclose : z n = z 0) (hnonconstant : ∃ i < n, z i ≠ z 0) : orderOf m = n := by
  obtain ⟨M,rfl⟩ := Matrix.ProjGenLinGroup.mk_surjective m
  simp only [pgl_mk_smul] at hstep
  have horder := projective_recurrence_exact_order M z n hn hn3 hstep hclose hnonconstant
  have hinj := prime_recurrence_injective (M • ·) z n hn hstep hclose hnonconstant
  have hindex : ∀ i j, i < n → j < n → z i = z j → i = j := by
    intro i j hi hj hij
    exact congrArg Fin.val (hinj (a₁ := ⟨i,hi⟩) (a₂ := ⟨j,hj⟩) hij)
  have h01 : z 0 ≠ z 1 := by intro h; have := hindex 0 1 (by omega) (by omega) h; omega
  have h02 : z 0 ≠ z 2 := by intro h; have := hindex 0 2 (by omega) (by omega) h; omega
  have h12 : z 1 ≠ z 2 := by intro h; have := hindex 1 2 (by omega) (by omega) h; omega
  have hperm : MulAction.toPermHom (GL (Fin 2) K) (ℙ K (Plane K)) (M^n) = 1 := by
    rw [map_pow,← horder]
    exact pow_orderOf_eq_one _
  have hfix (t : ℙ K (Plane K)) : M^n • t = t :=
    congrArg (fun e : Equiv.Perm (ℙ K (Plane K)) => e t) hperm
  have hpow : (Matrix.ProjGenLinGroup.mk M)^n = 1 := by
    rw [← map_pow]
    exact pgl_eq_one_of_three_fixed (M^n) (z 0) (z 1) (z 2) h01 h02 h12
      (hfix _) (hfix _) (hfix _)
  rcases (Nat.dvd_prime hn).mp (orderOf_dvd_of_pow_eq_one hpow) with h | h
  · have hm := orderOf_eq_one_iff.mp h
    have hf : M • z 0 = z 0 := by rw [← pgl_mk_smul,hm,one_smul]
    exact (h01 (by rw [hstep 0 hn.pos,hf])).elim
  · exact h

theorem pgl_finite_extension_recurrence
    (m : PGL(2,K)) (z : ℕ → ℙ K (Plane K)) (n : ℕ)
    (hn : n.Prime) (hn3 : 3 ≤ n)
    (hstep : ∀ i < n, z (i+1) = m • z i)
    (hclose : z n = z 0) (hnonconstant : ∃ i < n, z i ≠ z 0) :
    Function.Injective (fun i : Fin n => z i.val) ∧ orderOf m = n ∧
    (n = ringChar F ∨ n ∣ (Fintype.card F)^(Module.finrank F K)-1 ∨
      n ∣ (Fintype.card F)^(Module.finrank F K)+1) ∧
    (n ≠ ringChar F → 0 < Module.finrank F K ∧
      orderOf (Fintype.card F : ZMod n) ∣ 2 * Module.finrank F K ∧
      orderOf (Fintype.card F : ZMod n) /
        Nat.gcd (orderOf (Fintype.card F : ZMod n)) 2 ∣ Module.finrank F K) := by
  have ho := pgl_recurrence_exact_order m z n hn hn3 hstep hclose hnonconstant
  obtain ⟨M,rfl⟩ := Matrix.ProjGenLinGroup.mk_surjective m
  simp only [pgl_mk_smul] at hstep
  have h := finite_extension_projective_recurrence (F := F) M z n hn hn3 hstep hclose hnonconstant
  exact ⟨h.1,ho,h.2.2⟩

theorem pgl_cyclic_subgroup_recurrence
    {A : Type*} [AddGroup A] (G : A) (f : A → ℙ K (Plane K))
    (M : PGL(2,K)) (n : ℕ) (hn : n.Prime) (hn3 : 3 ≤ n)
    (horder : addOrderOf G = n)
    (hrec : ∀ P ∈ AddSubgroup.zmultiples G, f (P+G) = M • f P)
    (hnonconstant : ∃ P ∈ AddSubgroup.zmultiples G, f P ≠ f 0) :
    Set.InjOn f (AddSubgroup.zmultiples G) ∧
    orderOf M = n ∧
    (n = ringChar F ∨ n ∣ (Fintype.card F)^(Module.finrank F K)-1 ∨
      n ∣ (Fintype.card F)^(Module.finrank F K)+1) ∧
    (n ≠ ringChar F →
      0 < Module.finrank F K ∧
      orderOf (Fintype.card F : ZMod n) ∣ 2 * Module.finrank F K ∧
      orderOf (Fintype.card F : ZMod n) /
        Nat.gcd (orderOf (Fintype.card F : ZMod n)) 2 ∣ Module.finrank F K) := by
  classical
  let z : ℕ → ℙ K (Plane K) := fun i => f (i • G)
  have hG : IsOfFinAddOrder G := addOrderOf_pos_iff.mp (by rw [horder]; exact hn.pos)
  have hreps : ∀ P ∈ AddSubgroup.zmultiples G, ∃ i : Fin n, i.val • G = P := by
    intro P hP
    obtain ⟨i, hi⟩ := (finEquivZMultiples hG).surjective ⟨P,hP⟩
    have hval := congrArg Subtype.val hi
    change i.val • G = P at hval
    exact ⟨⟨i.val, by simpa only [horder] using i.isLt⟩, hval⟩
  have hstep : ∀ i < n, z (i+1) = M • z i := by
    intro i _
    simpa [z, add_nsmul] using hrec (i • G) (AddSubgroup.nsmul_mem_zmultiples G i)
  have hclose : z n = z 0 := by
    have hg0 : n • G = 0 := by rw [← horder]; exact addOrderOf_nsmul_eq_zero G
    simp [z, hg0]
  have hnon : ∃ i < n, z i ≠ z 0 := by
    obtain ⟨P,hP,hne⟩ := hnonconstant
    obtain ⟨i,hi⟩ := hreps P hP
    exact ⟨i.val, i.isLt, by simpa [z,hi] using hne⟩
  obtain ⟨hinj, hrest⟩ := pgl_finite_extension_recurrence (F := F) M z n hn hn3
    hstep hclose hnon
  refine ⟨?_, hrest⟩
  intro P hP Q hQ heq
  obtain ⟨i,hi⟩ := hreps P hP
  obtain ⟨j,hj⟩ := hreps Q hQ
  have hij : i = j := hinj (by simpa [z,hi,hj] using heq)
  calc
    P = i.val • G := hi.symm
    _ = j.val • G := by rw [hij]
    _ = Q := hj

end
end Astra01
#print axioms Astra01.pgl_recurrence_exact_order
#print axioms Astra01.pgl_finite_extension_recurrence

#print axioms Astra01.pgl_cyclic_subgroup_recurrence
