import Data.C196
import Inputs.C004
import Inputs.C192
open FastWalsh
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C196
theorem input_certificate : signTree effective (BitVec.ofNat 8 196) = inputTree := by
  have hb : BitVec.ofNat 8 196 = (BitVec.ofNat 8 4 ^^^ BitVec.ofNat 8 192) := by decide
  rw [hb, signTree_xor, C004.input_certificate, C192.input_certificate]
  rfl
end N12.C196
