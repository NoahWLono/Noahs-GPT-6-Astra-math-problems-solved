import FamilyAlgebra.TraceCoordinates
import Mathlib.FieldTheory.Finite.Trace
import Mathlib.FieldTheory.PrimitiveElement

namespace FamilyAlgebra
open scoped BigOperators
variable {E : Type*} [Field E] [Algebra (ZMod 2) E]

theorem binarySum_eq_smul_sum (weight : Nat → E) (bits : Nat → Bool) (n : Nat) :
    binarySum weight bits n = ∑ i ∈ Finset.range n, (bit (bits i) : ZMod 2) • weight i := by
  induction n with
  | zero => simp [binarySum]
  | succ n ih =>
    rw [binarySum, Finset.sum_range_succ, ih]
    cases bits n <;> simp [bit]

theorem powerBasis_binary_independent (pb : PowerBasis (ZMod 2) E) :
    ∀ bits, binarySum (fun k => pb.gen^k) bits pb.dim = 0 ↔
      ∀ k, k<pb.dim → bits k=false := by
  intro bits
  constructor
  · intro h k hk
    have root : ∑ i : Fin pb.dim, (bit (bits i) : ZMod 2) • pb.basis i = 0 := by
      simp only [pb.basis_eq_pow]
      rw [← Finset.sum_range (fun i => (bit (bits i) : ZMod 2) • pb.gen^i)]
      rwa [← binarySum_eq_smul_sum]
    have hc := (Fintype.linearIndependent_iff.mp pb.basis.linearIndependent)
      (fun i : Fin pb.dim => (bit (bits i) : ZMod 2)) root ⟨k,hk⟩
    cases hb : bits k <;> simp_all [bit]
  · intro h
    rw [binarySum_congr _ bits (fun _ => false) pb.dim h, binarySum_false]

local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

/-- Realization of every field/basis hypothesis of the concrete algebraic
zero-locus theorem in a field of exactly 2^n elements. -/
theorem galois_power_basis (n : Nat) (positive : 0<n) :
    ∃ a : GaloisField 2 n,
      ∀ bits, binarySum (fun k => a^k) bits n = 0 ↔ ∀ k, k<n → bits k=false := by
  let pb := Field.powerBasisOfFiniteOfSeparable (ZMod 2) (GaloisField 2 n)
  have hd : pb.dim=n := pb.finrank.symm.trans (GaloisField.finrank 2 (by omega))
  refine ⟨pb.gen, ?_⟩
  simpa only [hd] using powerBasis_binary_independent pb

/-- The concrete Pfaffian classification now holds in a realized field GF(2^n),
with no remaining field-existence or basis-independence hypotheses. -/
theorem realized_zero_locus (n : Nat) (positive : 0<n) :
    ∃ a : GaloisField 2 n, ∀ (u v w z : Bool) (s t : Nat → Bool),
      Pfaffian.pf (pencil a (family u v w z s t) n) = 0 ↔
        (u,v,w,z) ∈ sixBaseTuples ∧ ∀ j, 0<j → j<n → s j=false ∧ t j=false := by
  rcases galois_power_basis n positive with ⟨a,ha⟩
  refine ⟨a, ?_⟩
  intro u v w z s t
  exact concrete_zero_locus_six (CharP.cast_eq_zero (GaloisField 2 n) 2)
    a n positive ha u v w z s t

theorem realized_field_card (n : Nat) (positive : 0<n) :
    Nat.card (GaloisField 2 n) = 2^n := GaloisField.card 2 n (by omega)

theorem realized_field_finrank (n : Nat) (positive : 0<n) :
    Module.finrank (ZMod 2) (GaloisField 2 n) = n := GaloisField.finrank 2 (by omega)

/-- The actual field trace is nonzero, including even extension degrees. -/
theorem realized_trace_nonzero (n : Nat) :
    (Algebra.trace (ZMod 2) (GaloisField 2 n)).toAddMonoidHom ≠ 0 := by
  intro h
  apply Algebra.trace_ne_zero (ZMod 2) (GaloisField 2 n)
  ext x
  exact congrArg (fun f : GaloisField 2 n →+ ZMod 2 => f x) h

theorem realized_trace_radical (n : Nat) (K : TraceCoordinates.Matrix4 (GaloisField 2 n))
    (x : TraceCoordinates.V4 (GaloisField 2 n)) :
    (∀ y, TraceCoordinates.form (Algebra.trace (ZMod 2) (GaloisField 2 n)).toAddMonoidHom K x y=0) ↔
      ∀ i, TraceCoordinates.action K x i=0 :=
  TraceCoordinates.radical_iff _ (realized_trace_nonzero n) K x

theorem realized_trace_injective (n : Nat) :
    Function.Injective (TraceCoordinates.form
      (Algebra.trace (ZMod 2) (GaloisField 2 n)).toAddMonoidHom) :=
  TraceCoordinates.transfer_injective _ (realized_trace_nonzero n)

#print axioms realized_zero_locus
#print axioms realized_trace_radical
#print axioms realized_trace_injective
end FamilyAlgebra
