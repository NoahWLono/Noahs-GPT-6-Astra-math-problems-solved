import Data.C142
import Inputs.C002
import Inputs.C140
open FastWalsh
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C142
theorem input_certificate : signTree effective (BitVec.ofNat 8 142) = inputTree := by
  have hb : BitVec.ofNat 8 142 = (BitVec.ofNat 8 2 ^^^ BitVec.ofNat 8 140) := by decide
  rw [hb, signTree_xor, C002.input_certificate, C140.input_certificate]
  rfl
end N12.C142
