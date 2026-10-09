import Data.C137
import Inputs.C001
import Inputs.C136
open FastWalsh
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C137
theorem input_certificate : signTree effective (BitVec.ofNat 8 137) = inputTree := by
  have hb : BitVec.ofNat 8 137 = (BitVec.ofNat 8 1 ^^^ BitVec.ofNat 8 136) := by decide
  rw [hb, signTree_xor, C001.input_certificate, C136.input_certificate]
  rfl
end N12.C137
