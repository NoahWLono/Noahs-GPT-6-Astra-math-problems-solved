import Data.C077
import Inputs.C001
import Inputs.C076
open FastWalsh
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C077
theorem input_certificate : signTree effective (BitVec.ofNat 8 77) = inputTree := by
  have hb : BitVec.ofNat 8 77 = (BitVec.ofNat 8 1 ^^^ BitVec.ofNat 8 76) := by decide
  rw [hb, signTree_xor, C001.input_certificate, C076.input_certificate]
  rfl
end N12.C077
