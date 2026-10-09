import Data.C117
import Inputs.C001
import Inputs.C116
open FastWalsh
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C117
theorem input_certificate : signTree effective (BitVec.ofNat 8 117) = inputTree := by
  have hb : BitVec.ofNat 8 117 = (BitVec.ofNat 8 1 ^^^ BitVec.ofNat 8 116) := by decide
  rw [hb, signTree_xor, C001.input_certificate, C116.input_certificate]
  rfl
end N12.C117
