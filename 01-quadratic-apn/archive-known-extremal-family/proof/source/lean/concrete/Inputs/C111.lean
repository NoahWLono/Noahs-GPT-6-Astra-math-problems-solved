import Data.C111
import Inputs.C001
import Inputs.C110
open FastWalsh
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C111
theorem input_certificate : signTree effective (BitVec.ofNat 8 111) = inputTree := by
  have hb : BitVec.ofNat 8 111 = (BitVec.ofNat 8 1 ^^^ BitVec.ofNat 8 110) := by decide
  rw [hb, signTree_xor, C001.input_certificate, C110.input_certificate]
  rfl
end N12.C111
