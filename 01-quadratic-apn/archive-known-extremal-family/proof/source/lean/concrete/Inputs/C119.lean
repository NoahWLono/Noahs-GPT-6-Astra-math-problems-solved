import Data.C119
import Inputs.C001
import Inputs.C118
open FastWalsh
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C119
theorem input_certificate : signTree effective (BitVec.ofNat 8 119) = inputTree := by
  have hb : BitVec.ofNat 8 119 = (BitVec.ofNat 8 1 ^^^ BitVec.ofNat 8 118) := by decide
  rw [hb, signTree_xor, C001.input_certificate, C118.input_certificate]
  rfl
end N12.C119
