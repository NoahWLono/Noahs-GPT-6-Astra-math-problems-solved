import Data.C183
import Inputs.C001
import Inputs.C182
open FastWalsh
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C183
theorem input_certificate : signTree effective (BitVec.ofNat 8 183) = inputTree := by
  have hb : BitVec.ofNat 8 183 = (BitVec.ofNat 8 1 ^^^ BitVec.ofNat 8 182) := by decide
  rw [hb, signTree_xor, C001.input_certificate, C182.input_certificate]
  rfl
end N12.C183
