import Data.C165
import Inputs.C001
import Inputs.C164
open FastWalsh
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C165
theorem input_certificate : signTree effective (BitVec.ofNat 8 165) = inputTree := by
  have hb : BitVec.ofNat 8 165 = (BitVec.ofNat 8 1 ^^^ BitVec.ofNat 8 164) := by decide
  rw [hb, signTree_xor, C001.input_certificate, C164.input_certificate]
  rfl
end N12.C165
