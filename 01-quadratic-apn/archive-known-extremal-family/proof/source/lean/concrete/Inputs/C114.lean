import Data.C114
import Inputs.C002
import Inputs.C112
open FastWalsh
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C114
theorem input_certificate : signTree effective (BitVec.ofNat 8 114) = inputTree := by
  have hb : BitVec.ofNat 8 114 = (BitVec.ofNat 8 2 ^^^ BitVec.ofNat 8 112) := by decide
  rw [hb, signTree_xor, C002.input_certificate, C112.input_certificate]
  rfl
end N12.C114
