import Data.C105
import Inputs.C001
import Inputs.C104
open FastWalsh
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C105
theorem input_certificate : signTree effective (BitVec.ofNat 8 105) = inputTree := by
  have hb : BitVec.ofNat 8 105 = (BitVec.ofNat 8 1 ^^^ BitVec.ofNat 8 104) := by decide
  rw [hb, signTree_xor, C001.input_certificate, C104.input_certificate]
  rfl
end N12.C105
