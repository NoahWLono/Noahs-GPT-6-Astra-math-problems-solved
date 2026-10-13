/- Relative symbol-family interface and actual frozen-numerator properties. -/
module
public import DegreeFiveDescent
public import BridgeEndpoint
public import CompactNumerator
public import Endpoint
public import CompactExpandedBridge

@[expose] public section
noncomputable section
open Module
namespace PrimeFiveFamily

/-- Explicit relative symbol-family data. No conclusion about the fixed algebra,
its dimension, the numerator, or cyclicity is a field of this structure. -/
structure SymbolFamily (K A : Type*) [Field K] [CharZero K]
    [DivisionRing A] [Algebra K A] where
  q : K
  q_primitive : IsPrimitiveRoot q 5
  U : Aˣ
  V : Aˣ
  quantum : (U : A) * V = q • ((V : A) * U)
  x : K
  y : K
  fifth_U : (U : A) ^ 5 = algebraMap K A x
  fifth_V : (V : A) ^ 5 = algebraMap K A y
  basis : Basis (Fin 5 × Fin 5) K A
  basis_apply : ∀ ij, basis ij = (U : A) ^ ij.1.val * (V : A) ^ ij.2.val
  center : ∀ a : A, (∀ z : A, a * z = z * a) ↔
    ∃ c : K, algebraMap K A c = a
  sigma : A ≃+* A
  tau : K ≃+* K
  semilinear : ∀ (c : K) (a : A), sigma (c • a) = tau c • sigma a
  sigma_cube : ∀ a : A, sigma (sigma (sigma a)) = a
  sigma_U : sigma (U : A) = V
  sigma_V : sigma (V : A) = ((U : A) * V)⁻¹
  tau_q : tau q = q

variable {K A : Type*} [Field K] [CharZero K] [DivisionRing A] [Algebra K A]
variable (s : SymbolFamily K A)

abbrev FixedScalars := ↥(C3BasisDescent.fixedField s.tau)
abbrev FixedAlgebra := ↥(C3BasisDescent.fixedAlgebra s.sigma s.tau s.semilinear)
def z : K := (s.x * s.y)⁻¹
def W : A := ((s.U : A) * s.V)⁻¹

def frozenNumerator : A :=
  PrimeCyclicity.evalLaurent s.q s.U s.V PrimeCyclicity.numerator

def compactNumerator : A :=
  CompactC3Invariance.compactNumerator (algebraMap K A s.q)
    (s.U : A) (s.V : A) (W s)

def qFixed : FixedScalars s := ⟨s.q, s.tau_q⟩

theorem qFixed_primitive : IsPrimitiveRoot (qFixed s) 5 := by
  have h : IsPrimitiveRoot ((algebraMap (FixedScalars s) K) (qFixed s)) 5 :=
    s.q_primitive
  exact h.of_map_of_injective (algebraMap (FixedScalars s) K).injective

theorem sigma_scalar (c : K) :
    s.sigma (algebraMap K A c) = algebraMap K A (s.tau c) := by
  simpa only [Algebra.smul_def, mul_one, map_one] using s.semilinear c (1 : A)

theorem sigma_W : s.sigma (W s) = s.U := by
  simp only [W, map_inv₀, map_mul, s.sigma_U, s.sigma_V, mul_inv_rev]
  simp [s.V.ne_zero]

theorem compactNumerator_fixed : s.sigma (compactNumerator s) = compactNumerator s := by
  apply CompactC3Invariance.compactNumerator_fixed_of_two_images s.sigma
    (algebraMap K A s.q) (s.U : A) (s.V : A) s.U.ne_zero s.V.ne_zero
  · rw [sigma_scalar, s.tau_q]
  · exact s.sigma_U
  · exact s.sigma_V

/-- This non-scalarity statement concerns the actual imported 69-term numerator. -/
theorem frozenNumerator_not_scalar :
    ¬ ∃ c : K, frozenNumerator s = algebraMap K A c := by
  exact ConcreteCoordinateBridge.evaluated_numerator_not_scalar
    s.basis s.U s.V s.x s.y s.basis_apply s.fifth_U s.fifth_V s.q s.q_primitive s.quantum

/-- The checked compact/list bridge identifies the actual frozen numerator. -/
theorem frozen_eq_compact : frozenNumerator s = compactNumerator s := by
  exact CompactLaurentBridge.numerator_eq_compact_of_scalar_relation
    s.q s.q_primitive s.U s.V (by simpa only [Algebra.smul_def] using s.quantum)

/-- Fixedness is proved for the actual 69-term numerator. -/
theorem frozenNumerator_fixed : s.sigma (frozenNumerator s) = frozenNumerator s := by
  rw [frozen_eq_compact]
  exact compactNumerator_fixed s

/-- The actual frozen numerator as an element of the actual fixed algebra. -/
def fixedNumerator : FixedAlgebra s := ⟨frozenNumerator s, frozenNumerator_fixed s⟩

theorem fixedNumerator_not_scalar :
    fixedNumerator s ∉ Set.range (algebraMap (FixedScalars s) (FixedAlgebra s)) := by
  rintro ⟨c, hc⟩
  apply frozenNumerator_not_scalar s
  refine ⟨(c : K), ?_⟩
  have h := congrArg (fun d : FixedAlgebra s => (d : A)) hc
  exact h.symm

end PrimeFiveFamily
