import Data.C178
import Inputs.C002
import Inputs.C176
open FastWalsh
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C178
theorem input_certificate : signTree effective (BitVec.ofNat 8 178) = inputTree := by
  have hb : BitVec.ofNat 8 178 = (BitVec.ofNat 8 2 ^^^ BitVec.ofNat 8 176) := by decide
  rw [hb, signTree_xor, C002.input_certificate, C176.input_certificate]
  rfl
end N12.C178
