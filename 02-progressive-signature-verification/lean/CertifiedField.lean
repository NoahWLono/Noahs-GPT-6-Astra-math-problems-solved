import PrimeCertificate
import Mathlib.Algebra.Field.ZMod

namespace ProgressivePool
/-- The parameter field is an actual prime field, using the kernel-checked
primality certificate, rather than an assumed prime-order field. -/
abbrev ParameterField := ZMod 1073741789
instance parameterPrimeFact : Fact (Nat.Prime 1073741789) := ⟨parameter_prime_checked⟩
example : Field ParameterField := inferInstance
example : Fintype ParameterField := inferInstance
 theorem parameter_field_card : Fintype.card ParameterField = 1073741789 := by
  exact ZMod.card 1073741789
#print axioms parameter_field_card
#print axioms parameterPrimeFact
end ProgressivePool
