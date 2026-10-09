import Data.C081
import Inputs.C001
import Inputs.C080
open FastWalsh
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C081
theorem input_certificate : signTree effective (BitVec.ofNat 8 81) = inputTree := by
  have hb : BitVec.ofNat 8 81 = (BitVec.ofNat 8 1 ^^^ BitVec.ofNat 8 80) := by decide
  rw [hb, signTree_xor, C001.input_certificate, C080.input_certificate]
  rfl
end N12.C081
