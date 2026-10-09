import Data.C170
import Inputs.C002
import Inputs.C168
open FastWalsh
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C170
theorem input_certificate : signTree effective (BitVec.ofNat 8 170) = inputTree := by
  have hb : BitVec.ofNat 8 170 = (BitVec.ofNat 8 2 ^^^ BitVec.ofNat 8 168) := by decide
  rw [hb, signTree_xor, C002.input_certificate, C168.input_certificate]
  rfl
end N12.C170
