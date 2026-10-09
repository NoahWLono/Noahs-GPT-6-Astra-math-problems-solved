import Data.C180
import Inputs.C004
import Inputs.C176
open FastWalsh
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C180
theorem input_certificate : signTree effective (BitVec.ofNat 8 180) = inputTree := by
  have hb : BitVec.ofNat 8 180 = (BitVec.ofNat 8 4 ^^^ BitVec.ofNat 8 176) := by decide
  rw [hb, signTree_xor, C004.input_certificate, C176.input_certificate]
  rfl
end N12.C180
