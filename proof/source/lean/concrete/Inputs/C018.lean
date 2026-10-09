import Data.C018
import Inputs.C002
import Inputs.C016
open FastWalsh
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C018
theorem input_certificate : signTree effective (BitVec.ofNat 8 18) = inputTree := by
  have hb : BitVec.ofNat 8 18 = (BitVec.ofNat 8 2 ^^^ BitVec.ofNat 8 16) := by decide
  rw [hb, signTree_xor, C002.input_certificate, C016.input_certificate]
  rfl
end N12.C018
