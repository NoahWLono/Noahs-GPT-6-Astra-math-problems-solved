import Data.C130
import Inputs.C002
import Inputs.C128
open FastWalsh
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C130
theorem input_certificate : signTree effective (BitVec.ofNat 8 130) = inputTree := by
  have hb : BitVec.ofNat 8 130 = (BitVec.ofNat 8 2 ^^^ BitVec.ofNat 8 128) := by decide
  rw [hb, signTree_xor, C002.input_certificate, C128.input_certificate]
  rfl
end N12.C130
