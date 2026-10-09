import Data.C164
import Inputs.C004
import Inputs.C160
open FastWalsh
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C164
theorem input_certificate : signTree effective (BitVec.ofNat 8 164) = inputTree := by
  have hb : BitVec.ofNat 8 164 = (BitVec.ofNat 8 4 ^^^ BitVec.ofNat 8 160) := by decide
  rw [hb, signTree_xor, C004.input_certificate, C160.input_certificate]
  rfl
end N12.C164
