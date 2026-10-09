import Inputs.C089
open FastWalsh QuadraticWalshShift
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C089
theorem zero_value : componentZeroSum 12 coefficients (BitVec.ofNat 8 89) = (64 : Int) := by
  rw [componentZeroSum_eq_sumTree]
  change sumTree (signTree effective (BitVec.ofNat 8 89)) = (64 : Int)
  rw [input_certificate]
  rfl
def inverseColumns : List (Nat × BitVec 12) := [(0, 1248), (1, 2032), (2, 2456), (3, 3972), (4, 838), (5, 3011), (6, 3635), (7, 559), (8, 2622), (9, 506), (10, 75), (11, 364)]
theorem alignment : basisAlignmentCheck coefficients (BitVec.ofNat 8 89) inverseColumns = true := by decide
theorem bent : IsBent effective (BitVec.ofNat 8 89) := by
  apply quadratic_bent_certificate coefficients (BitVec.ofNat 8 89) inverseColumns alignment
  rw [zero_value]
  decide
#print axioms bent
end N12.C089
