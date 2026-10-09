import Data.C065
import Inputs.C001
import Inputs.C064
open FastWalsh
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C065
theorem input_certificate : signTree effective (BitVec.ofNat 8 65) = inputTree := by
  have hb : BitVec.ofNat 8 65 = (BitVec.ofNat 8 1 ^^^ BitVec.ofNat 8 64) := by decide
  rw [hb, signTree_xor, C001.input_certificate, C064.input_certificate]
  rfl
end N12.C065
