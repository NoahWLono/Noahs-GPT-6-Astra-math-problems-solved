import Inputs.C138
open FastWalsh QuadraticWalshShift
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C138
theorem zero_value : componentZeroSum 12 coefficients (BitVec.ofNat 8 138) = (-64 : Int) := by
  rw [componentZeroSum_eq_sumTree]
  change sumTree (signTree effective (BitVec.ofNat 8 138)) = (-64 : Int)
  rw [input_certificate]
  rfl
def inverseColumns : List (Nat × BitVec 12) := [(0, 2208), (1, 3312), (2, 1816), (3, 3460), (4, 2886), (5, 4035), (6, 2098), (7, 3115), (8, 1596), (9, 308), (10, 430), (11, 251)]
theorem alignment : basisAlignmentCheck coefficients (BitVec.ofNat 8 138) inverseColumns = true := by decide
theorem bent : IsBent effective (BitVec.ofNat 8 138) := by
  apply quadratic_bent_certificate coefficients (BitVec.ofNat 8 138) inverseColumns alignment
  rw [zero_value]
  decide
#print axioms bent
end N12.C138
