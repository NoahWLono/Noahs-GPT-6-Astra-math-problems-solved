import FamilyAlgebra.TraceRank
import FamilyAlgebra.PfaffianKernel

namespace FamilyAlgebra
variable {E : Type*} [Field E]

/-- The field-valued bilinear form is exactly (Kx) dot y, matching the
coordinate trace-radical theorem rather than merely being isomorphic to it. -/
def fieldBilin (K : TraceCoordinates.Matrix4 E) :
    LinearMap.BilinForm E (TraceCoordinates.V4 E) :=
  LinearMap.mk₂ E (fun x y => TraceCoordinates.dot (TraceCoordinates.action K x) y)
    (by intro x x' y; simp only [TraceCoordinates.dot, TraceCoordinates.action, Pi.add_apply]; ring)
    (by intro c x y; simp only [TraceCoordinates.dot, TraceCoordinates.action, Pi.smul_apply, smul_eq_mul]; ring)
    (by intro x y y'; simp only [TraceCoordinates.dot, TraceCoordinates.action, Pi.add_apply]; ring)
    (by intro c x y; simp only [TraceCoordinates.dot, TraceCoordinates.action, Pi.smul_apply, smul_eq_mul]; ring)

theorem fieldBilin_alt (two_zero : (2:E)=0) (x : Pfaffian.Coordinates E) :
    (fieldBilin (altMatrix x)).IsAlt := by
  intro y
  change TraceCoordinates.dot (TraceCoordinates.action (altMatrix x) y) y=0
  simp only [TraceCoordinates.dot, TraceCoordinates.action, altMatrix]
  ring_nf
  simp [two_zero]

local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

/-- A genuine F2-linear coordinate identification; its existence is proved
from the realized field degree, not supplied as an assumption. -/
noncomputable def binaryCoordinates (n : Nat) (positive : 0<n) :
    (Fin 4 → GaloisField 2 n) ≃ₗ[ZMod 2] (Fin (4*n) → ZMod 2) :=
  LinearEquiv.ofFinrankEq _ _ (by
    rw [Module.finrank_pi_fintype, Module.finrank_pi]
    simp [realized_field_finrank n positive])

/-- Actual binary-coordinate form obtained by transferring the concrete
four-by-four field matrix with the actual finite-field trace. -/
noncomputable def binaryForm (n : Nat) (positive : 0<n)
    (K : TraceCoordinates.Matrix4 (GaloisField 2 n)) :
    LinearMap.BilinForm (ZMod 2) (Fin (4*n) → ZMod 2) :=
  LinearMap.BilinForm.congr (binaryCoordinates n positive)
    ((Algebra.trace (ZMod 2) (GaloisField 2 n)).compBilinForm (fieldBilin K))

theorem binaryForm_apply (n : Nat) (positive : 0<n)
    (K : TraceCoordinates.Matrix4 (GaloisField 2 n)) (x y : Fin (4*n) → ZMod 2) :
    binaryForm n positive K x y = TraceCoordinates.form
      (Algebra.trace (ZMod 2) (GaloisField 2 n)).toAddMonoidHom K
      ((binaryCoordinates n positive).symm x) ((binaryCoordinates n positive).symm y) := rfl

theorem binaryForm_alt (n : Nat) (positive : 0<n) (x : Pfaffian.Coordinates (GaloisField 2 n)) :
    (binaryForm n positive (altMatrix x)).IsAlt := by
  intro y
  change Algebra.trace (ZMod 2) (GaloisField 2 n)
    (fieldBilin (altMatrix x) ((binaryCoordinates n positive).symm y)
      ((binaryCoordinates n positive).symm y))=0
  rw [fieldBilin_alt (CharP.cast_eq_zero (GaloisField 2 n) 2) x]
  exact map_zero _

theorem binaryForm_nondegenerate (n : Nat) (positive : 0<n)
    (x : Pfaffian.Coordinates (GaloisField 2 n)) (hp : Pfaffian.pf x ≠ 0) :
    (binaryForm n positive (altMatrix x)).Nondegenerate := by
  intro y hy
  have hr : ∀ z, TraceCoordinates.form
      (Algebra.trace (ZMod 2) (GaloisField 2 n)).toAddMonoidHom (altMatrix x)
      ((binaryCoordinates n positive).symm y) z=0 := by
    intro z
    have h := hy ((binaryCoordinates n positive) z)
    simpa only [binaryForm_apply, LinearEquiv.symm_apply_apply] using h
  have hk := (realized_trace_radical n (altMatrix x) _).mp hr
  have hz := pf_nonzero_kernel (CharP.cast_eq_zero (GaloisField 2 n) 2) x hp _ hk
  apply (binaryCoordinates n positive).symm.injective
  simpa using hz

theorem binaryForm_degenerate_of_kernel (n : Nat) (positive : 0<n)
    (K : TraceCoordinates.Matrix4 (GaloisField 2 n))
    (witness : ∃ y, y ≠ 0 ∧ ∀ i, TraceCoordinates.action K y i=0) :
    ¬(binaryForm n positive K).Nondegenerate := by
  rcases witness with ⟨y,hy,hk⟩
  intro hnon
  have hz := hnon ((binaryCoordinates n positive) y) (by
    intro z
    rw [binaryForm_apply, LinearEquiv.symm_apply_apply]
    exact (realized_trace_radical n K y).mpr hk _)
  apply hy
  apply (binaryCoordinates n positive).injective
  simpa using hz

/-- Complete concrete family classification at the actual binary bilinear-form
level. The subsequent Boolean quadratic/Walsh encoding is a separate bridge. -/
theorem binary_family_nondegenerate_iff (n : Nat) (positive : 0<n)
    (a : GaloisField 2 n)
    (independent : ∀ bits, binarySum (fun k => a^k) bits n=0 ↔ ∀ k, k<n → bits k=false)
    (u v w z : Bool) (s t : Nat → Bool) :
    (binaryForm n positive (altMatrix (pencil a (family u v w z s t) n))).Nondegenerate ↔
      ¬((u,v,w,z) ∈ sixBaseTuples ∧ ∀ j, 0<j → j<n → s j=false ∧ t j=false) := by
  have hclass := concrete_zero_locus_six (CharP.cast_eq_zero (GaloisField 2 n) 2)
    a n positive independent u v w z s t
  constructor
  · intro hgood hbad
    have hp := hclass.mpr hbad
    exact binaryForm_degenerate_of_kernel n positive _
      (singular_pencil_kernel (CharP.cast_eq_zero (GaloisField 2 n) 2)
        a n positive independent u v w z s t hp) hgood
  · intro hgood
    apply binaryForm_nondegenerate
    intro hp
    exact hgood (hclass.mp hp)

/-- Every positive degree admits the fully realized binary alternating family
with the proved six-exception nondegeneracy classification. -/
theorem realized_binary_family (n : Nat) (positive : 0<n) :
    ∃ a : GaloisField 2 n, ∀ (u v w z : Bool) (s t : Nat → Bool),
      (binaryForm n positive (altMatrix (pencil a (family u v w z s t) n))).IsAlt ∧
      ((binaryForm n positive (altMatrix (pencil a (family u v w z s t) n))).Nondegenerate ↔
        ¬((u,v,w,z) ∈ sixBaseTuples ∧ ∀ j, 0<j → j<n → s j=false ∧ t j=false)) := by
  rcases galois_power_basis n positive with ⟨a,ha⟩
  refine ⟨a, ?_⟩
  intro u v w z s t
  exact ⟨binaryForm_alt n positive _,
    binary_family_nondegenerate_iff n positive a ha u v w z s t⟩

#print axioms realized_binary_family
#print axioms binary_family_nondegenerate_iff
#print axioms binaryForm_alt
end FamilyAlgebra
