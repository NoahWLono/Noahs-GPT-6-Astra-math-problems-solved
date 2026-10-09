import Data.C182
import Inputs.C002
import Inputs.C180
open FastWalsh
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C182
theorem input_certificate : signTree effective (BitVec.ofNat 8 182) = inputTree := by
  have hb : BitVec.ofNat 8 182 = (BitVec.ofNat 8 2 ^^^ BitVec.ofNat 8 180) := by decide
  rw [hb, signTree_xor, C002.input_certificate, C180.input_certificate]
  rfl
end N12.C182
