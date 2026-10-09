import Data.C040
import Inputs.C008
import Inputs.C032
open FastWalsh
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C040
theorem input_certificate : signTree effective (BitVec.ofNat 8 40) = inputTree := by
  have hb : BitVec.ofNat 8 40 = (BitVec.ofNat 8 8 ^^^ BitVec.ofNat 8 32) := by decide
  rw [hb, signTree_xor, C008.input_certificate, C032.input_certificate]
  rfl
end N12.C040
