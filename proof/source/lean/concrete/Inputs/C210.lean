import Data.C210
import Inputs.C002
import Inputs.C208
open FastWalsh
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C210
theorem input_certificate : signTree effective (BitVec.ofNat 8 210) = inputTree := by
  have hb : BitVec.ofNat 8 210 = (BitVec.ofNat 8 2 ^^^ BitVec.ofNat 8 208) := by decide
  rw [hb, signTree_xor, C002.input_certificate, C208.input_certificate]
  rfl
end N12.C210
