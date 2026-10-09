import Data.C160
import Inputs.C032
import Inputs.C128
open FastWalsh
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C160
theorem input_certificate : signTree effective (BitVec.ofNat 8 160) = inputTree := by
  have hb : BitVec.ofNat 8 160 = (BitVec.ofNat 8 32 ^^^ BitVec.ofNat 8 128) := by decide
  rw [hb, signTree_xor, C032.input_certificate, C128.input_certificate]
  rfl
end N12.C160
