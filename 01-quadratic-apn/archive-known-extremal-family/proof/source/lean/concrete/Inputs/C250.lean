import Data.C250
import Inputs.C002
import Inputs.C248
open FastWalsh
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C250
theorem input_certificate : signTree effective (BitVec.ofNat 8 250) = inputTree := by
  have hb : BitVec.ofNat 8 250 = (BitVec.ofNat 8 2 ^^^ BitVec.ofNat 8 248) := by decide
  rw [hb, signTree_xor, C002.input_certificate, C248.input_certificate]
  rfl
end N12.C250
