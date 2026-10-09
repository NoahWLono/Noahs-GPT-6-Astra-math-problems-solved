import Inputs.C098
open FastWalsh QuadraticWalshShift
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C098
theorem zero_value : componentZeroSum 12 coefficients (BitVec.ofNat 8 98) = (64 : Int) := by
  rw [componentZeroSum_eq_sumTree]
  change sumTree (signTree effective (BitVec.ofNat 8 98)) = (64 : Int)
  rw [input_certificate]
  rfl
def inverseColumns : List (Nat × BitVec 12) := [(0, 2952), (1, 1376), (2, 976), (3, 321), (4, 132), (5, 66), (6, 558), (7, 2069), (8, 1039), (9, 69), (10, 258), (11, 129)]
theorem alignment : basisAlignmentCheck coefficients (BitVec.ofNat 8 98) inverseColumns = true := by decide
theorem bent : IsBent effective (BitVec.ofNat 8 98) := by
  apply quadratic_bent_certificate coefficients (BitVec.ofNat 8 98) inverseColumns alignment
  rw [zero_value]
  decide
#print axioms bent
end N12.C098
