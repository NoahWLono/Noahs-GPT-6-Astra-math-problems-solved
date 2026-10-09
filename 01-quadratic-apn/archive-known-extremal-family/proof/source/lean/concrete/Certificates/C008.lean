import Inputs.C008
open FastWalsh QuadraticWalshShift
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C008
theorem zero_value : componentZeroSum 12 coefficients (BitVec.ofNat 8 8) = (512 : Int) := by
  rw [componentZeroSum_eq_sumTree]
  change sumTree (signTree effective (BitVec.ofNat 8 8)) = (512 : Int)
  rw [input_certificate]
  rfl
theorem not_bent : ¬ IsBent effective (BitVec.ofNat 8 8) := by
  intro h
  have hb : ¬(componentZeroSum 12 coefficients (BitVec.ofNat 8 8) * componentZeroSum 12 coefficients (BitVec.ofNat 8 8) = (2^12 : Nat)) := by
    rw [zero_value]
    decide
  apply hb
  simpa only [componentZeroSum_correct] using h (0 : BitVec 12)
#print axioms not_bent
end N12.C008
