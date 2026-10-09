import Data.C026
import Inputs.C002
import Inputs.C024
open FastWalsh
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C026
theorem input_certificate : signTree effective (BitVec.ofNat 8 26) = inputTree := by
  have hb : BitVec.ofNat 8 26 = (BitVec.ofNat 8 2 ^^^ BitVec.ofNat 8 24) := by decide
  rw [hb, signTree_xor, C002.input_certificate, C024.input_certificate]
  rfl
end N12.C026
