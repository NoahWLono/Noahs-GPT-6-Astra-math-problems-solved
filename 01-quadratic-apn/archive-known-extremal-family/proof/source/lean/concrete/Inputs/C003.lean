import Data.C003
import Inputs.C001
import Inputs.C002
open FastWalsh
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C003
theorem input_certificate : signTree effective (BitVec.ofNat 8 3) = inputTree := by
  have hb : BitVec.ofNat 8 3 = (BitVec.ofNat 8 1 ^^^ BitVec.ofNat 8 2) := by decide
  rw [hb, signTree_xor, C001.input_certificate, C002.input_certificate]
  rfl
end N12.C003
