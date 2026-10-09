import Data.C073
import Inputs.C001
import Inputs.C072
open FastWalsh
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C073
theorem input_certificate : signTree effective (BitVec.ofNat 8 73) = inputTree := by
  have hb : BitVec.ofNat 8 73 = (BitVec.ofNat 8 1 ^^^ BitVec.ofNat 8 72) := by decide
  rw [hb, signTree_xor, C001.input_certificate, C072.input_certificate]
  rfl
end N12.C073
