import Data.C249
import Inputs.C001
import Inputs.C248
open FastWalsh
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C249
theorem input_certificate : signTree effective (BitVec.ofNat 8 249) = inputTree := by
  have hb : BitVec.ofNat 8 249 = (BitVec.ofNat 8 1 ^^^ BitVec.ofNat 8 248) := by decide
  rw [hb, signTree_xor, C001.input_certificate, C248.input_certificate]
  rfl
end N12.C249
