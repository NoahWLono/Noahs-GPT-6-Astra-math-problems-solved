import Data.C144
import Inputs.C016
import Inputs.C128
open FastWalsh
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C144
theorem input_certificate : signTree effective (BitVec.ofNat 8 144) = inputTree := by
  have hb : BitVec.ofNat 8 144 = (BitVec.ofNat 8 16 ^^^ BitVec.ofNat 8 128) := by decide
  rw [hb, signTree_xor, C016.input_certificate, C128.input_certificate]
  rfl
end N12.C144
