import Data.C146
import Inputs.C002
import Inputs.C144
open FastWalsh
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C146
theorem input_certificate : signTree effective (BitVec.ofNat 8 146) = inputTree := by
  have hb : BitVec.ofNat 8 146 = (BitVec.ofNat 8 2 ^^^ BitVec.ofNat 8 144) := by decide
  rw [hb, signTree_xor, C002.input_certificate, C144.input_certificate]
  rfl
end N12.C146
