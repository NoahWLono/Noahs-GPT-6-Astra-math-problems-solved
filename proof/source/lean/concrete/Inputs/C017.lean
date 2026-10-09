import Data.C017
import Inputs.C001
import Inputs.C016
open FastWalsh
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C017
theorem input_certificate : signTree effective (BitVec.ofNat 8 17) = inputTree := by
  have hb : BitVec.ofNat 8 17 = (BitVec.ofNat 8 1 ^^^ BitVec.ofNat 8 16) := by decide
  rw [hb, signTree_xor, C001.input_certificate, C016.input_certificate]
  rfl
end N12.C017
