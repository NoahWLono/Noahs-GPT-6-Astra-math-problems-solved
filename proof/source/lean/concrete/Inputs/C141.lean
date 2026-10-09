import Data.C141
import Inputs.C001
import Inputs.C140
open FastWalsh
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C141
theorem input_certificate : signTree effective (BitVec.ofNat 8 141) = inputTree := by
  have hb : BitVec.ofNat 8 141 = (BitVec.ofNat 8 1 ^^^ BitVec.ofNat 8 140) := by decide
  rw [hb, signTree_xor, C001.input_certificate, C140.input_certificate]
  rfl
end N12.C141
