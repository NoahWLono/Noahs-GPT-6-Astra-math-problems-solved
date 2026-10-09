import Data.C207
import Inputs.C001
import Inputs.C206
open FastWalsh
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C207
theorem input_certificate : signTree effective (BitVec.ofNat 8 207) = inputTree := by
  have hb : BitVec.ofNat 8 207 = (BitVec.ofNat 8 1 ^^^ BitVec.ofNat 8 206) := by decide
  rw [hb, signTree_xor, C001.input_certificate, C206.input_certificate]
  rfl
end N12.C207
