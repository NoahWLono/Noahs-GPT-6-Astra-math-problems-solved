import Basis.B4
import Data.C016
open FastWalsh
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C016
theorem inputBlock13 : tabulate (fun x => signed (B4.scalar (embed 13 x)) 1) = data8_13 := by rfl
end N12.C016
