import Data.C024
import Inputs.C008
import Inputs.C016
open FastWalsh
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C024
theorem input_certificate : signTree effective (BitVec.ofNat 8 24) = inputTree := by
  have hb : BitVec.ofNat 8 24 = (BitVec.ofNat 8 8 ^^^ BitVec.ofNat 8 16) := by decide
  rw [hb, signTree_xor, C008.input_certificate, C016.input_certificate]
  rfl
end N12.C024
