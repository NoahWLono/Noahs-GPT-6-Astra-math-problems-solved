import Data.C083
import Inputs.C001
import Inputs.C082
open FastWalsh
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C083
theorem input_certificate : signTree effective (BitVec.ofNat 8 83) = inputTree := by
  have hb : BitVec.ofNat 8 83 = (BitVec.ofNat 8 1 ^^^ BitVec.ofNat 8 82) := by decide
  rw [hb, signTree_xor, C001.input_certificate, C082.input_certificate]
  rfl
end N12.C083
