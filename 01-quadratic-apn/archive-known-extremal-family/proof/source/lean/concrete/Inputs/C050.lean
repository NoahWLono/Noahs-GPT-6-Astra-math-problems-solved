import Data.C050
import Inputs.C002
import Inputs.C048
open FastWalsh
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C050
theorem input_certificate : signTree effective (BitVec.ofNat 8 50) = inputTree := by
  have hb : BitVec.ofNat 8 50 = (BitVec.ofNat 8 2 ^^^ BitVec.ofNat 8 48) := by decide
  rw [hb, signTree_xor, C002.input_certificate, C048.input_certificate]
  rfl
end N12.C050
