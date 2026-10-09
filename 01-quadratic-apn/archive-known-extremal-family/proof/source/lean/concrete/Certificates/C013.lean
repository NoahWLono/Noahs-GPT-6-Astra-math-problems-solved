import Inputs.C013
open FastWalsh QuadraticWalshShift
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C013
theorem zero_value : componentZeroSum 12 coefficients (BitVec.ofNat 8 13) = (0 : Int) := by
  rw [componentZeroSum_eq_sumTree]
  change sumTree (signTree effective (BitVec.ofNat 8 13)) = (0 : Int)
  rw [input_certificate]
  rfl
theorem not_bent : ¬ IsBent effective (BitVec.ofNat 8 13) := by
  intro h
  have hb : ¬(componentZeroSum 12 coefficients (BitVec.ofNat 8 13) * componentZeroSum 12 coefficients (BitVec.ofNat 8 13) = (2^12 : Nat)) := by
    rw [zero_value]
    decide
  apply hb
  simpa only [componentZeroSum_correct] using h (0 : BitVec 12)
#print axioms not_bent
end N12.C013
