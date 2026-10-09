import Data.C060
import Inputs.C004
import Inputs.C056
open FastWalsh
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C060
theorem input_certificate : signTree effective (BitVec.ofNat 8 60) = inputTree := by
  have hb : BitVec.ofNat 8 60 = (BitVec.ofNat 8 4 ^^^ BitVec.ofNat 8 56) := by decide
  rw [hb, signTree_xor, C004.input_certificate, C056.input_certificate]
  rfl
end N12.C060
