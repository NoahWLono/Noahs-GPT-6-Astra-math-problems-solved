import Basis.B0
import Data.C001
open FastWalsh
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C001
theorem inputBlock5 : tabulate (fun x => signed (B0.scalar (embed 5 x)) 1) = data8_4 := by rfl
end N12.C001
