import Data.C186
import Inputs.C002
import Inputs.C184
open FastWalsh
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C186
theorem input_certificate : signTree effective (BitVec.ofNat 8 186) = inputTree := by
  have hb : BitVec.ofNat 8 186 = (BitVec.ofNat 8 2 ^^^ BitVec.ofNat 8 184) := by decide
  rw [hb, signTree_xor, C002.input_certificate, C184.input_certificate]
  rfl
end N12.C186
