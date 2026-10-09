import Basis.B3
import Data.C008
open FastWalsh
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C008
theorem inputBlock7 : tabulate (fun x => signed (B3.scalar (embed 7 x)) 1) = data8_1 := by rfl
end N12.C008
