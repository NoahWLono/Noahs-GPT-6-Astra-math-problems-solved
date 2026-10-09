import Data.C082
import Inputs.C002
import Inputs.C080
open FastWalsh
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C082
theorem input_certificate : signTree effective (BitVec.ofNat 8 82) = inputTree := by
  have hb : BitVec.ofNat 8 82 = (BitVec.ofNat 8 2 ^^^ BitVec.ofNat 8 80) := by decide
  rw [hb, signTree_xor, C002.input_certificate, C080.input_certificate]
  rfl
end N12.C082
