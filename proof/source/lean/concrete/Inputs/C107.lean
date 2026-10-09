import Data.C107
import Inputs.C001
import Inputs.C106
open FastWalsh
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C107
theorem input_certificate : signTree effective (BitVec.ofNat 8 107) = inputTree := by
  have hb : BitVec.ofNat 8 107 = (BitVec.ofNat 8 1 ^^^ BitVec.ofNat 8 106) := by decide
  rw [hb, signTree_xor, C001.input_certificate, C106.input_certificate]
  rfl
end N12.C107
