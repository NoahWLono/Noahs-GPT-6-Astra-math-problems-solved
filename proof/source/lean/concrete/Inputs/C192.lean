import Data.C192
import Inputs.C064
import Inputs.C128
open FastWalsh
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C192
theorem input_certificate : signTree effective (BitVec.ofNat 8 192) = inputTree := by
  have hb : BitVec.ofNat 8 192 = (BitVec.ofNat 8 64 ^^^ BitVec.ofNat 8 128) := by decide
  rw [hb, signTree_xor, C064.input_certificate, C128.input_certificate]
  rfl
end N12.C192
