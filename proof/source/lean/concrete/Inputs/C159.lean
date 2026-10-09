import Data.C159
import Inputs.C001
import Inputs.C158
open FastWalsh
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C159
theorem input_certificate : signTree effective (BitVec.ofNat 8 159) = inputTree := by
  have hb : BitVec.ofNat 8 159 = (BitVec.ofNat 8 1 ^^^ BitVec.ofNat 8 158) := by decide
  rw [hb, signTree_xor, C001.input_certificate, C158.input_certificate]
  rfl
end N12.C159
