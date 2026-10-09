import Data.C110
import Inputs.C002
import Inputs.C108
open FastWalsh
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C110
theorem input_certificate : signTree effective (BitVec.ofNat 8 110) = inputTree := by
  have hb : BitVec.ofNat 8 110 = (BitVec.ofNat 8 2 ^^^ BitVec.ofNat 8 108) := by decide
  rw [hb, signTree_xor, C002.input_certificate, C108.input_certificate]
  rfl
end N12.C110
