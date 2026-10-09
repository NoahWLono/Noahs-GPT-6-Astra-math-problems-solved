import Data.C094
import Inputs.C002
import Inputs.C092
open FastWalsh
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C094
theorem input_certificate : signTree effective (BitVec.ofNat 8 94) = inputTree := by
  have hb : BitVec.ofNat 8 94 = (BitVec.ofNat 8 2 ^^^ BitVec.ofNat 8 92) := by decide
  rw [hb, signTree_xor, C002.input_certificate, C092.input_certificate]
  rfl
end N12.C094
