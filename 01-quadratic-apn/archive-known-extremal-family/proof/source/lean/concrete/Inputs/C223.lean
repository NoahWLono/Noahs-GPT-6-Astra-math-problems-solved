import Data.C223
import Inputs.C001
import Inputs.C222
open FastWalsh
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C223
theorem input_certificate : signTree effective (BitVec.ofNat 8 223) = inputTree := by
  have hb : BitVec.ofNat 8 223 = (BitVec.ofNat 8 1 ^^^ BitVec.ofNat 8 222) := by decide
  rw [hb, signTree_xor, C001.input_certificate, C222.input_certificate]
  rfl
end N12.C223
