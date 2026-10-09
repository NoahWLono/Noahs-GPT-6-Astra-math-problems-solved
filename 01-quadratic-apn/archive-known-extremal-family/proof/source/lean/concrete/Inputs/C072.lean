import Data.C072
import Inputs.C008
import Inputs.C064
open FastWalsh
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C072
theorem input_certificate : signTree effective (BitVec.ofNat 8 72) = inputTree := by
  have hb : BitVec.ofNat 8 72 = (BitVec.ofNat 8 8 ^^^ BitVec.ofNat 8 64) := by decide
  rw [hb, signTree_xor, C008.input_certificate, C064.input_certificate]
  rfl
end N12.C072
