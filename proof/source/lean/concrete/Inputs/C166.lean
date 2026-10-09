import Data.C166
import Inputs.C002
import Inputs.C164
open FastWalsh
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C166
theorem input_certificate : signTree effective (BitVec.ofNat 8 166) = inputTree := by
  have hb : BitVec.ofNat 8 166 = (BitVec.ofNat 8 2 ^^^ BitVec.ofNat 8 164) := by decide
  rw [hb, signTree_xor, C002.input_certificate, C164.input_certificate]
  rfl
end N12.C166
