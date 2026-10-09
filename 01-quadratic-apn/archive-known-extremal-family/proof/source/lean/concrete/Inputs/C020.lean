import Data.C020
import Inputs.C004
import Inputs.C016
open FastWalsh
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C020
theorem input_certificate : signTree effective (BitVec.ofNat 8 20) = inputTree := by
  have hb : BitVec.ofNat 8 20 = (BitVec.ofNat 8 4 ^^^ BitVec.ofNat 8 16) := by decide
  rw [hb, signTree_xor, C004.input_certificate, C016.input_certificate]
  rfl
end N12.C020
