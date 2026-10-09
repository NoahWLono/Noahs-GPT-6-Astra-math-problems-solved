import Data.C059
import Inputs.C001
import Inputs.C058
open FastWalsh
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C059
theorem input_certificate : signTree effective (BitVec.ofNat 8 59) = inputTree := by
  have hb : BitVec.ofNat 8 59 = (BitVec.ofNat 8 1 ^^^ BitVec.ofNat 8 58) := by decide
  rw [hb, signTree_xor, C001.input_certificate, C058.input_certificate]
  rfl
end N12.C059
