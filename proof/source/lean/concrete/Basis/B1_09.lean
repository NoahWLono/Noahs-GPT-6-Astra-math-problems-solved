import Basis.B1
import Data.C002
open FastWalsh
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C002
theorem inputBlock9 : tabulate (fun x => signed (B1.scalar (embed 9 x)) 1) = data8_6 := by rfl
end N12.C002
