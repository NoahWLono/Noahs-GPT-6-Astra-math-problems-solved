import Data.C057
import Inputs.C001
import Inputs.C056
open FastWalsh
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C057
theorem input_certificate : signTree effective (BitVec.ofNat 8 57) = inputTree := by
  have hb : BitVec.ofNat 8 57 = (BitVec.ofNat 8 1 ^^^ BitVec.ofNat 8 56) := by decide
  rw [hb, signTree_xor, C001.input_certificate, C056.input_certificate]
  rfl
end N12.C057
