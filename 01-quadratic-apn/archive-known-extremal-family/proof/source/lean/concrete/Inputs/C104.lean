import Data.C104
import Inputs.C008
import Inputs.C096
open FastWalsh
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C104
theorem input_certificate : signTree effective (BitVec.ofNat 8 104) = inputTree := by
  have hb : BitVec.ofNat 8 104 = (BitVec.ofNat 8 8 ^^^ BitVec.ofNat 8 96) := by decide
  rw [hb, signTree_xor, C008.input_certificate, C096.input_certificate]
  rfl
end N12.C104
