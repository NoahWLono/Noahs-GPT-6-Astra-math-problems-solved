import Data.C248
import Inputs.C008
import Inputs.C240
open FastWalsh
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C248
theorem input_certificate : signTree effective (BitVec.ofNat 8 248) = inputTree := by
  have hb : BitVec.ofNat 8 248 = (BitVec.ofNat 8 8 ^^^ BitVec.ofNat 8 240) := by decide
  rw [hb, signTree_xor, C008.input_certificate, C240.input_certificate]
  rfl
end N12.C248
