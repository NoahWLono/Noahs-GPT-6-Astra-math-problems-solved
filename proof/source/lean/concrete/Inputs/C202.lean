import Data.C202
import Inputs.C002
import Inputs.C200
open FastWalsh
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C202
theorem input_certificate : signTree effective (BitVec.ofNat 8 202) = inputTree := by
  have hb : BitVec.ofNat 8 202 = (BitVec.ofNat 8 2 ^^^ BitVec.ofNat 8 200) := by decide
  rw [hb, signTree_xor, C002.input_certificate, C200.input_certificate]
  rfl
end N12.C202
