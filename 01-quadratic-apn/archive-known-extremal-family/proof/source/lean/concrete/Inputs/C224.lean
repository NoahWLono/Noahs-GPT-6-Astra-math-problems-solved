import Data.C224
import Inputs.C032
import Inputs.C192
open FastWalsh
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C224
theorem input_certificate : signTree effective (BitVec.ofNat 8 224) = inputTree := by
  have hb : BitVec.ofNat 8 224 = (BitVec.ofNat 8 32 ^^^ BitVec.ofNat 8 192) := by decide
  rw [hb, signTree_xor, C032.input_certificate, C192.input_certificate]
  rfl
end N12.C224
