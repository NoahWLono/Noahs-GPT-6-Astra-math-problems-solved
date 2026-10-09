import Data.C101
import Inputs.C001
import Inputs.C100
open FastWalsh
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C101
theorem input_certificate : signTree effective (BitVec.ofNat 8 101) = inputTree := by
  have hb : BitVec.ofNat 8 101 = (BitVec.ofNat 8 1 ^^^ BitVec.ofNat 8 100) := by decide
  rw [hb, signTree_xor, C001.input_certificate, C100.input_certificate]
  rfl
end N12.C101
