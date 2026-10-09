import Data.C080
import Inputs.C016
import Inputs.C064
open FastWalsh
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C080
theorem input_certificate : signTree effective (BitVec.ofNat 8 80) = inputTree := by
  have hb : BitVec.ofNat 8 80 = (BitVec.ofNat 8 16 ^^^ BitVec.ofNat 8 64) := by decide
  rw [hb, signTree_xor, C016.input_certificate, C064.input_certificate]
  rfl
end N12.C080
