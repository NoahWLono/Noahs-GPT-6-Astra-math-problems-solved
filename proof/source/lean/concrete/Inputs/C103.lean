import Data.C103
import Inputs.C001
import Inputs.C102
open FastWalsh
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C103
theorem input_certificate : signTree effective (BitVec.ofNat 8 103) = inputTree := by
  have hb : BitVec.ofNat 8 103 = (BitVec.ofNat 8 1 ^^^ BitVec.ofNat 8 102) := by decide
  rw [hb, signTree_xor, C001.input_certificate, C102.input_certificate]
  rfl
end N12.C103
