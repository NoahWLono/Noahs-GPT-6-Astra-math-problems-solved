import Data.C102
import Inputs.C002
import Inputs.C100
open FastWalsh
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C102
theorem input_certificate : signTree effective (BitVec.ofNat 8 102) = inputTree := by
  have hb : BitVec.ofNat 8 102 = (BitVec.ofNat 8 2 ^^^ BitVec.ofNat 8 100) := by decide
  rw [hb, signTree_xor, C002.input_certificate, C100.input_certificate]
  rfl
end N12.C102
