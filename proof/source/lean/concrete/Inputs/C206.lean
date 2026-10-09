import Data.C206
import Inputs.C002
import Inputs.C204
open FastWalsh
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C206
theorem input_certificate : signTree effective (BitVec.ofNat 8 206) = inputTree := by
  have hb : BitVec.ofNat 8 206 = (BitVec.ofNat 8 2 ^^^ BitVec.ofNat 8 204) := by decide
  rw [hb, signTree_xor, C002.input_certificate, C204.input_certificate]
  rfl
end N12.C206
