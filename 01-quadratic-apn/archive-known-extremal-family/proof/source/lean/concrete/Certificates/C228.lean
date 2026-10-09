import Inputs.C228
open FastWalsh QuadraticWalshShift
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C228
theorem zero_value : componentZeroSum 12 coefficients (BitVec.ofNat 8 228) = (-64 : Int) := by
  rw [componentZeroSum_eq_sumTree]
  change sumTree (signTree effective (BitVec.ofNat 8 228)) = (-64 : Int)
  rw [input_certificate]
  rfl
def inverseColumns : List (Nat × BitVec 12) := [(0, 4080), (1, 616), (2, 2936), (3, 3782), (4, 965), (5, 2951), (6, 3103), (7, 2617), (8, 3637), (9, 447), (10, 329), (11, 493)]
theorem alignment : basisAlignmentCheck coefficients (BitVec.ofNat 8 228) inverseColumns = true := by decide
theorem bent : IsBent effective (BitVec.ofNat 8 228) := by
  apply quadratic_bent_certificate coefficients (BitVec.ofNat 8 228) inverseColumns alignment
  rw [zero_value]
  decide
#print axioms bent
end N12.C228
