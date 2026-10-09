import Data.C211
import Inputs.C001
import Inputs.C210
open FastWalsh
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C211
theorem input_certificate : signTree effective (BitVec.ofNat 8 211) = inputTree := by
  have hb : BitVec.ofNat 8 211 = (BitVec.ofNat 8 1 ^^^ BitVec.ofNat 8 210) := by decide
  rw [hb, signTree_xor, C001.input_certificate, C210.input_certificate]
  rfl
end N12.C211
