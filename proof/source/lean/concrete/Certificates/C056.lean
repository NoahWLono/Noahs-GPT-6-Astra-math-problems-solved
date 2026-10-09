import Inputs.C056
open FastWalsh QuadraticWalshShift
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C056
theorem zero_value : componentZeroSum 12 coefficients (BitVec.ofNat 8 56) = (64 : Int) := by
  rw [componentZeroSum_eq_sumTree]
  change sumTree (signTree effective (BitVec.ofNat 8 56)) = (64 : Int)
  rw [input_certificate]
  rfl
def inverseColumns : List (Nat × BitVec 12) := [(0, 3944), (1, 656), (2, 2632), (3, 2565), (4, 1026), (5, 513), (6, 5), (7, 2), (8, 1), (9, 47), (10, 17), (11, 13)]
theorem alignment : basisAlignmentCheck coefficients (BitVec.ofNat 8 56) inverseColumns = true := by decide
theorem bent : IsBent effective (BitVec.ofNat 8 56) := by
  apply quadratic_bent_certificate coefficients (BitVec.ofNat 8 56) inverseColumns alignment
  rw [zero_value]
  decide
#print axioms bent
end N12.C056
