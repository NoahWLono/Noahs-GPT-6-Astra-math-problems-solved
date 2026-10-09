import Data.C255
import Inputs.C001
import Inputs.C254
open FastWalsh
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C255
theorem input_certificate : signTree effective (BitVec.ofNat 8 255) = inputTree := by
  have hb : BitVec.ofNat 8 255 = (BitVec.ofNat 8 1 ^^^ BitVec.ofNat 8 254) := by decide
  rw [hb, signTree_xor, C001.input_certificate, C254.input_certificate]
  rfl
end N12.C255
