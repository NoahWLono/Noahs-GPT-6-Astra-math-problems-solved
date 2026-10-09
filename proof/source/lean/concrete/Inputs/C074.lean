import Data.C074
import Inputs.C002
import Inputs.C072
open FastWalsh
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C074
theorem input_certificate : signTree effective (BitVec.ofNat 8 74) = inputTree := by
  have hb : BitVec.ofNat 8 74 = (BitVec.ofNat 8 2 ^^^ BitVec.ofNat 8 72) := by decide
  rw [hb, signTree_xor, C002.input_certificate, C072.input_certificate]
  rfl
end N12.C074
