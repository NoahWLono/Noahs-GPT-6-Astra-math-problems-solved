import Data.C092
import Inputs.C004
import Inputs.C088
open FastWalsh
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C092
theorem input_certificate : signTree effective (BitVec.ofNat 8 92) = inputTree := by
  have hb : BitVec.ofNat 8 92 = (BitVec.ofNat 8 4 ^^^ BitVec.ofNat 8 88) := by decide
  rw [hb, signTree_xor, C004.input_certificate, C088.input_certificate]
  rfl
end N12.C092
