import Data.C195
import Inputs.C001
import Inputs.C194
open FastWalsh
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C195
theorem input_certificate : signTree effective (BitVec.ofNat 8 195) = inputTree := by
  have hb : BitVec.ofNat 8 195 = (BitVec.ofNat 8 1 ^^^ BitVec.ofNat 8 194) := by decide
  rw [hb, signTree_xor, C001.input_certificate, C194.input_certificate]
  rfl
end N12.C195
