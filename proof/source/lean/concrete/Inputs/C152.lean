import Data.C152
import Inputs.C008
import Inputs.C144
open FastWalsh
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C152
theorem input_certificate : signTree effective (BitVec.ofNat 8 152) = inputTree := by
  have hb : BitVec.ofNat 8 152 = (BitVec.ofNat 8 8 ^^^ BitVec.ofNat 8 144) := by decide
  rw [hb, signTree_xor, C008.input_certificate, C144.input_certificate]
  rfl
end N12.C152
