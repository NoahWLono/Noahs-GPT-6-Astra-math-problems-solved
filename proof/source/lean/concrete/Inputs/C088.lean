import Data.C088
import Inputs.C008
import Inputs.C080
open FastWalsh
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C088
theorem input_certificate : signTree effective (BitVec.ofNat 8 88) = inputTree := by
  have hb : BitVec.ofNat 8 88 = (BitVec.ofNat 8 8 ^^^ BitVec.ofNat 8 80) := by decide
  rw [hb, signTree_xor, C008.input_certificate, C080.input_certificate]
  rfl
end N12.C088
