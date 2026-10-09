import Data.C253
import Inputs.C001
import Inputs.C252
open FastWalsh
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C253
theorem input_certificate : signTree effective (BitVec.ofNat 8 253) = inputTree := by
  have hb : BitVec.ofNat 8 253 = (BitVec.ofNat 8 1 ^^^ BitVec.ofNat 8 252) := by decide
  rw [hb, signTree_xor, C001.input_certificate, C252.input_certificate]
  rfl
end N12.C253
