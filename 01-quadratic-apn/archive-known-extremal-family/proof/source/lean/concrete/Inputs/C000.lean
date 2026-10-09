import Data.C000
open FastWalsh
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C000
theorem input_certificate : signTree effective (BitVec.ofNat 8 0) = inputTree := by
  change signTree effective (0 : BitVec 8) = inputTree
  rw [signTree_zero]
  rfl
end N12.C000
