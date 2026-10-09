import Data.C062
import Inputs.C002
import Inputs.C060
open FastWalsh
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C062
theorem input_certificate : signTree effective (BitVec.ofNat 8 62) = inputTree := by
  have hb : BitVec.ofNat 8 62 = (BitVec.ofNat 8 2 ^^^ BitVec.ofNat 8 60) := by decide
  rw [hb, signTree_xor, C002.input_certificate, C060.input_certificate]
  rfl
end N12.C062
