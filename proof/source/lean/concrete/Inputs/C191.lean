import Data.C191
import Inputs.C001
import Inputs.C190
open FastWalsh
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C191
theorem input_certificate : signTree effective (BitVec.ofNat 8 191) = inputTree := by
  have hb : BitVec.ofNat 8 191 = (BitVec.ofNat 8 1 ^^^ BitVec.ofNat 8 190) := by decide
  rw [hb, signTree_xor, C001.input_certificate, C190.input_certificate]
  rfl
end N12.C191
