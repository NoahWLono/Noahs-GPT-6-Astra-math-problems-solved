import Data.C131
import Inputs.C001
import Inputs.C130
open FastWalsh
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C131
theorem input_certificate : signTree effective (BitVec.ofNat 8 131) = inputTree := by
  have hb : BitVec.ofNat 8 131 = (BitVec.ofNat 8 1 ^^^ BitVec.ofNat 8 130) := by decide
  rw [hb, signTree_xor, C001.input_certificate, C130.input_certificate]
  rfl
end N12.C131
