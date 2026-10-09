import Data.C037
import Inputs.C001
import Inputs.C036
open FastWalsh
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C037
theorem input_certificate : signTree effective (BitVec.ofNat 8 37) = inputTree := by
  have hb : BitVec.ofNat 8 37 = (BitVec.ofNat 8 1 ^^^ BitVec.ofNat 8 36) := by decide
  rw [hb, signTree_xor, C001.input_certificate, C036.input_certificate]
  rfl
end N12.C037
