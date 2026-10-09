import Data.C213
import Inputs.C001
import Inputs.C212
open FastWalsh
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C213
theorem input_certificate : signTree effective (BitVec.ofNat 8 213) = inputTree := by
  have hb : BitVec.ofNat 8 213 = (BitVec.ofNat 8 1 ^^^ BitVec.ofNat 8 212) := by decide
  rw [hb, signTree_xor, C001.input_certificate, C212.input_certificate]
  rfl
end N12.C213
