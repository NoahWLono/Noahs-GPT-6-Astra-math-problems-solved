import Inputs.C047
open FastWalsh QuadraticWalshShift
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C047
theorem zero_value : componentZeroSum 12 coefficients (BitVec.ofNat 8 47) = (-64 : Int) := by
  rw [componentZeroSum_eq_sumTree]
  change sumTree (signTree effective (BitVec.ofNat 8 47)) = (-64 : Int)
  rw [input_certificate]
  rfl
def inverseColumns : List (Nat × BitVec 12) := [(0, 4072), (1, 592), (2, 2888), (3, 4037), (4, 578), (5, 2881), (6, 2623), (7, 1033), (8, 557), (9, 383), (10, 137), (11, 109)]
theorem alignment : basisAlignmentCheck coefficients (BitVec.ofNat 8 47) inverseColumns = true := by decide
theorem bent : IsBent effective (BitVec.ofNat 8 47) := by
  apply quadratic_bent_certificate coefficients (BitVec.ofNat 8 47) inverseColumns alignment
  rw [zero_value]
  decide
#print axioms bent
end N12.C047
