import Data.C115
import Inputs.C001
import Inputs.C114
open FastWalsh
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C115
theorem input_certificate : signTree effective (BitVec.ofNat 8 115) = inputTree := by
  have hb : BitVec.ofNat 8 115 = (BitVec.ofNat 8 1 ^^^ BitVec.ofNat 8 114) := by decide
  rw [hb, signTree_xor, C001.input_certificate, C114.input_certificate]
  rfl
end N12.C115
