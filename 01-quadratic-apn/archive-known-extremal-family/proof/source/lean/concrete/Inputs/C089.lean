import Data.C089
import Inputs.C001
import Inputs.C088
open FastWalsh
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C089
theorem input_certificate : signTree effective (BitVec.ofNat 8 89) = inputTree := by
  have hb : BitVec.ofNat 8 89 = (BitVec.ofNat 8 1 ^^^ BitVec.ofNat 8 88) := by decide
  rw [hb, signTree_xor, C001.input_certificate, C088.input_certificate]
  rfl
end N12.C089
