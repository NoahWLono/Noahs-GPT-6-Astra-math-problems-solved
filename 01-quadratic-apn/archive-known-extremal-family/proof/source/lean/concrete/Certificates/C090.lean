import Inputs.C090
open FastWalsh QuadraticWalshShift
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C090
theorem zero_value : componentZeroSum 12 coefficients (BitVec.ofNat 8 90) = (64 : Int) := by
  rw [componentZeroSum_eq_sumTree]
  change sumTree (signTree effective (BitVec.ofNat 8 90)) = (64 : Int)
  rw [input_certificate]
  rfl
def inverseColumns : List (Nat × BitVec 12) := [(0, 1504), (1, 1648), (2, 2392), (3, 1924), (4, 3910), (5, 3523), (6, 3639), (7, 553), (8, 2621), (9, 474), (10, 123), (11, 372)]
theorem alignment : basisAlignmentCheck coefficients (BitVec.ofNat 8 90) inverseColumns = true := by decide
theorem bent : IsBent effective (BitVec.ofNat 8 90) := by
  apply quadratic_bent_certificate coefficients (BitVec.ofNat 8 90) inverseColumns alignment
  rw [zero_value]
  decide
#print axioms bent
end N12.C090
