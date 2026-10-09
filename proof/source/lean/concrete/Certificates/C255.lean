import Inputs.C255
open FastWalsh QuadraticWalshShift
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C255
theorem zero_value : componentZeroSum 12 coefficients (BitVec.ofNat 8 255) = (64 : Int) := by
  rw [componentZeroSum_eq_sumTree]
  change sumTree (signTree effective (BitVec.ofNat 8 255)) = (64 : Int)
  rw [input_certificate]
  rfl
def inverseColumns : List (Nat × BitVec 12) := [(0, 2224), (1, 3304), (2, 1848), (3, 1222), (4, 1989), (5, 2439), (6, 26), (7, 59), (8, 52), (9, 20), (10, 30), (11, 35)]
theorem alignment : basisAlignmentCheck coefficients (BitVec.ofNat 8 255) inverseColumns = true := by decide
theorem bent : IsBent effective (BitVec.ofNat 8 255) := by
  apply quadratic_bent_certificate coefficients (BitVec.ofNat 8 255) inverseColumns alignment
  rw [zero_value]
  decide
#print axioms bent
end N12.C255
