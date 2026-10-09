import Data.C136
import Inputs.C008
import Inputs.C128
open FastWalsh
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C136
theorem input_certificate : signTree effective (BitVec.ofNat 8 136) = inputTree := by
  have hb : BitVec.ofNat 8 136 = (BitVec.ofNat 8 8 ^^^ BitVec.ofNat 8 128) := by decide
  rw [hb, signTree_xor, C008.input_certificate, C128.input_certificate]
  rfl
end N12.C136
