import Data.C129
import Inputs.C001
import Inputs.C128
open FastWalsh
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C129
theorem input_certificate : signTree effective (BitVec.ofNat 8 129) = inputTree := by
  have hb : BitVec.ofNat 8 129 = (BitVec.ofNat 8 1 ^^^ BitVec.ofNat 8 128) := by decide
  rw [hb, signTree_xor, C001.input_certificate, C128.input_certificate]
  rfl
end N12.C129
