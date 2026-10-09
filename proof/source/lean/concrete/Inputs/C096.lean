import Data.C096
import Inputs.C032
import Inputs.C064
open FastWalsh
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C096
theorem input_certificate : signTree effective (BitVec.ofNat 8 96) = inputTree := by
  have hb : BitVec.ofNat 8 96 = (BitVec.ofNat 8 32 ^^^ BitVec.ofNat 8 64) := by decide
  rw [hb, signTree_xor, C032.input_certificate, C064.input_certificate]
  rfl
end N12.C096
