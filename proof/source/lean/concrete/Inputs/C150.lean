import Data.C150
import Inputs.C002
import Inputs.C148
open FastWalsh
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C150
theorem input_certificate : signTree effective (BitVec.ofNat 8 150) = inputTree := by
  have hb : BitVec.ofNat 8 150 = (BitVec.ofNat 8 2 ^^^ BitVec.ofNat 8 148) := by decide
  rw [hb, signTree_xor, C002.input_certificate, C148.input_certificate]
  rfl
end N12.C150
