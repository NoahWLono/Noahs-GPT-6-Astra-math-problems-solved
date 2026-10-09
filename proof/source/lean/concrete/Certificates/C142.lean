import Inputs.C142
open FastWalsh QuadraticWalshShift
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C142
theorem zero_value : componentZeroSum 12 coefficients (BitVec.ofNat 8 142) = (-64 : Int) := by
  rw [componentZeroSum_eq_sumTree]
  change sumTree (signTree effective (BitVec.ofNat 8 142)) = (-64 : Int)
  rw [input_certificate]
  rfl
def inverseColumns : List (Nat × BitVec 12) := [(0, 1816), (1, 4024), (2, 3312), (3, 3843), (4, 903), (5, 2758), (6, 1572), (7, 3638), (8, 3099), (9, 251), (10, 463), (11, 430)]
theorem alignment : basisAlignmentCheck coefficients (BitVec.ofNat 8 142) inverseColumns = true := by decide
theorem bent : IsBent effective (BitVec.ofNat 8 142) := by
  apply quadratic_bent_certificate coefficients (BitVec.ofNat 8 142) inverseColumns alignment
  rw [zero_value]
  decide
#print axioms bent
end N12.C142
