import Data.C122
import Inputs.C002
import Inputs.C120
open FastWalsh
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C122
theorem input_certificate : signTree effective (BitVec.ofNat 8 122) = inputTree := by
  have hb : BitVec.ofNat 8 122 = (BitVec.ofNat 8 2 ^^^ BitVec.ofNat 8 120) := by decide
  rw [hb, signTree_xor, C002.input_certificate, C120.input_certificate]
  rfl
end N12.C122
