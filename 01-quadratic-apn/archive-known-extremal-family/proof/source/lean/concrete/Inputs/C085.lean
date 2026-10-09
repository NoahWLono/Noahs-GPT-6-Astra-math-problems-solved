import Data.C085
import Inputs.C001
import Inputs.C084
open FastWalsh
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C085
theorem input_certificate : signTree effective (BitVec.ofNat 8 85) = inputTree := by
  have hb : BitVec.ofNat 8 85 = (BitVec.ofNat 8 1 ^^^ BitVec.ofNat 8 84) := by decide
  rw [hb, signTree_xor, C001.input_certificate, C084.input_certificate]
  rfl
end N12.C085
