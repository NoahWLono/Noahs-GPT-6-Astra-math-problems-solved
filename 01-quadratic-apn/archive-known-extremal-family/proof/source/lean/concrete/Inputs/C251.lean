import Data.C251
import Inputs.C001
import Inputs.C250
open FastWalsh
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C251
theorem input_certificate : signTree effective (BitVec.ofNat 8 251) = inputTree := by
  have hb : BitVec.ofNat 8 251 = (BitVec.ofNat 8 1 ^^^ BitVec.ofNat 8 250) := by decide
  rw [hb, signTree_xor, C001.input_certificate, C250.input_certificate]
  rfl
end N12.C251
