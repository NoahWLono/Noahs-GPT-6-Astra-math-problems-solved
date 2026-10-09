import Data.C220
import Inputs.C004
import Inputs.C216
open FastWalsh
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C220
theorem input_certificate : signTree effective (BitVec.ofNat 8 220) = inputTree := by
  have hb : BitVec.ofNat 8 220 = (BitVec.ofNat 8 4 ^^^ BitVec.ofNat 8 216) := by decide
  rw [hb, signTree_xor, C004.input_certificate, C216.input_certificate]
  rfl
end N12.C220
