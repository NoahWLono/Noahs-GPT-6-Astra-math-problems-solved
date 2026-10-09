import Data.C045
import Inputs.C001
import Inputs.C044
open FastWalsh
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C045
theorem input_certificate : signTree effective (BitVec.ofNat 8 45) = inputTree := by
  have hb : BitVec.ofNat 8 45 = (BitVec.ofNat 8 1 ^^^ BitVec.ofNat 8 44) := by decide
  rw [hb, signTree_xor, C001.input_certificate, C044.input_certificate]
  rfl
end N12.C045
