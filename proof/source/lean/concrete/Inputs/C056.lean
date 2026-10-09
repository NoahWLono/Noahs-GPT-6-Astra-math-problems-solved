import Data.C056
import Inputs.C008
import Inputs.C048
open FastWalsh
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C056
theorem input_certificate : signTree effective (BitVec.ofNat 8 56) = inputTree := by
  have hb : BitVec.ofNat 8 56 = (BitVec.ofNat 8 8 ^^^ BitVec.ofNat 8 48) := by decide
  rw [hb, signTree_xor, C008.input_certificate, C048.input_certificate]
  rfl
end N12.C056
