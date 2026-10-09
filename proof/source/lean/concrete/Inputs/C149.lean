import Data.C149
import Inputs.C001
import Inputs.C148
open FastWalsh
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C149
theorem input_certificate : signTree effective (BitVec.ofNat 8 149) = inputTree := by
  have hb : BitVec.ofNat 8 149 = (BitVec.ofNat 8 1 ^^^ BitVec.ofNat 8 148) := by decide
  rw [hb, signTree_xor, C001.input_certificate, C148.input_certificate]
  rfl
end N12.C149
