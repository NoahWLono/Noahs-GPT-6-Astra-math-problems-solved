import Data.C109
import Inputs.C001
import Inputs.C108
open FastWalsh
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C109
theorem input_certificate : signTree effective (BitVec.ofNat 8 109) = inputTree := by
  have hb : BitVec.ofNat 8 109 = (BitVec.ofNat 8 1 ^^^ BitVec.ofNat 8 108) := by decide
  rw [hb, signTree_xor, C001.input_certificate, C108.input_certificate]
  rfl
end N12.C109
