import Data.C019
import Inputs.C001
import Inputs.C018
open FastWalsh
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C019
theorem input_certificate : signTree effective (BitVec.ofNat 8 19) = inputTree := by
  have hb : BitVec.ofNat 8 19 = (BitVec.ofNat 8 1 ^^^ BitVec.ofNat 8 18) := by decide
  rw [hb, signTree_xor, C001.input_certificate, C018.input_certificate]
  rfl
end N12.C019
