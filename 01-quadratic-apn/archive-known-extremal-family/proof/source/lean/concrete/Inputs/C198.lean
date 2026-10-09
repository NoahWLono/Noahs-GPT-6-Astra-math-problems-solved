import Data.C198
import Inputs.C002
import Inputs.C196
open FastWalsh
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C198
theorem input_certificate : signTree effective (BitVec.ofNat 8 198) = inputTree := by
  have hb : BitVec.ofNat 8 198 = (BitVec.ofNat 8 2 ^^^ BitVec.ofNat 8 196) := by decide
  rw [hb, signTree_xor, C002.input_certificate, C196.input_certificate]
  rfl
end N12.C198
