import RUPPath.Inputs
import GraphClauseData
import CardinalityEncoding
open Std.Sat
namespace LocalIdentifyingQ6
open CardinalityEncoding
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem semanticChunk29 (C : Code) (X : Nat → Bool) (hX : ∀ v : Vertex, X (v.val+1) = C v)
    (hC : Constraints C) (hz0 : C 0 = true) (hz1 : C 1 = true) (hz2 : C 2 = true)
    (hs : prefixCount X 64 ≤ 13) :
    Q6RUPPath.InputChunk29 (fun n => assignment X n = true) := by
  have hA : ∀ v : Vertex, assignment X (v.val+1) = C v := by
    intro v
    rw [assignment_input X _ (by have := v.isLt; omega)]
    exact hX v
  refine { c1451 := ?_, c1452 := ?_, c1453 := ?_, c1454 := ?_, c1455 := ?_, c1456 := ?_, c1457 := ?_, c1458 := ?_, c1459 := ?_, c1460 := ?_, c1461 := ?_, c1462 := ?_, c1463 := ?_, c1464 := ?_, c1465 := ?_, c1466 := ?_, c1467 := ?_, c1468 := ?_, c1469 := ?_, c1470 := ?_, c1471 := ?_, c1472 := ?_, c1473 := ?_, c1474 := ?_, c1475 := ?_, c1476 := ?_, c1477 := ?_, c1478 := ?_, c1479 := ?_, c1480 := ?_, c1481 := ?_, c1482 := ?_, c1483 := ?_, c1484 := ?_, c1485 := ?_, c1486 := ?_, c1487 := ?_, c1488 := ?_, c1489 := ?_, c1490 := ?_, c1491 := ?_, c1492 := ?_, c1493 := ?_, c1494 := ?_, c1495 := ?_, c1496 := ?_, c1497 := ?_, c1498 := ?_, c1499 := ?_, c1500 := ?_ }
  · have hh := step_sound X hs (.carry 638 651) (by decide +kernel)
    simpa [Step.clause, CNF.Clause.eval] using hh
  · have hh := step_sound X hs (.increment 47 638 639) (by decide +kernel)
    simpa [Step.clause, CNF.Clause.eval] using hh
  · have hh := step_sound X hs (.carry 639 652) (by decide +kernel)
    simpa [Step.clause, CNF.Clause.eval] using hh
  · have hh := step_sound X hs (.increment 48 639 640) (by decide +kernel)
    simpa [Step.clause, CNF.Clause.eval] using hh
  · have hh := step_sound X hs (.carry 640 653) (by decide +kernel)
    simpa [Step.clause, CNF.Clause.eval] using hh
  · have hh := step_sound X hs (.increment 49 640 641) (by decide +kernel)
    simpa [Step.clause, CNF.Clause.eval] using hh
  · have hh := step_sound X hs (.carry 641 654) (by decide +kernel)
    simpa [Step.clause, CNF.Clause.eval] using hh
  · have hh := step_sound X hs (.increment 50 641 642) (by decide +kernel)
    simpa [Step.clause, CNF.Clause.eval] using hh
  · have hh := step_sound X hs (.carry 642 655) (by decide +kernel)
    simpa [Step.clause, CNF.Clause.eval] using hh
  · have hh := step_sound X hs (.increment 51 642 643) (by decide +kernel)
    simpa [Step.clause, CNF.Clause.eval] using hh
  · have hh := step_sound X hs (.carry 643 656) (by decide +kernel)
    simpa [Step.clause, CNF.Clause.eval] using hh
  · have hh := step_sound X hs (.increment 52 643 644) (by decide +kernel)
    simpa [Step.clause, CNF.Clause.eval] using hh
  · have hh := step_sound X hs (.carry 644 657) (by decide +kernel)
    simpa [Step.clause, CNF.Clause.eval] using hh
  · have hh := step_sound X hs (.increment 53 644 645) (by decide +kernel)
    simpa [Step.clause, CNF.Clause.eval] using hh
  · have hh := step_sound X hs (.carry 645 658) (by decide +kernel)
    simpa [Step.clause, CNF.Clause.eval] using hh
  · have hh := step_sound X hs (.increment 54 645 646) (by decide +kernel)
    simpa [Step.clause, CNF.Clause.eval] using hh
  · have hh := step_sound X hs (.carry 646 659) (by decide +kernel)
    simpa [Step.clause, CNF.Clause.eval] using hh
  · have hh := step_sound X hs (.increment 55 646 647) (by decide +kernel)
    simpa [Step.clause, CNF.Clause.eval] using hh
  · have hh := step_sound X hs (.carry 647 660) (by decide +kernel)
    simpa [Step.clause, CNF.Clause.eval] using hh
  · have hh := step_sound X hs (.increment 56 647 648) (by decide +kernel)
    simpa [Step.clause, CNF.Clause.eval] using hh
  · have hh := step_sound X hs (.carry 648 661) (by decide +kernel)
    simpa [Step.clause, CNF.Clause.eval] using hh
  · have hh := step_sound X hs (.increment 57 648 649) (by decide +kernel)
    simpa [Step.clause, CNF.Clause.eval] using hh
  · have hh := step_sound X hs (.carry 649 662) (by decide +kernel)
    simpa [Step.clause, CNF.Clause.eval] using hh
  · have hh := step_sound X hs (.overflow 58 649) (by decide +kernel)
    simpa [Step.clause, CNF.Clause.eval] using hh
  · have hh := step_sound X hs (.input 46 650) (by decide +kernel)
    simpa [Step.clause, CNF.Clause.eval] using hh
  · have hh := step_sound X hs (.carry 650 663) (by decide +kernel)
    simpa [Step.clause, CNF.Clause.eval] using hh
  · have hh := step_sound X hs (.increment 47 650 651) (by decide +kernel)
    simpa [Step.clause, CNF.Clause.eval] using hh
  · have hh := step_sound X hs (.carry 651 664) (by decide +kernel)
    simpa [Step.clause, CNF.Clause.eval] using hh
  · have hh := step_sound X hs (.increment 48 651 652) (by decide +kernel)
    simpa [Step.clause, CNF.Clause.eval] using hh
  · have hh := step_sound X hs (.carry 652 665) (by decide +kernel)
    simpa [Step.clause, CNF.Clause.eval] using hh
  · have hh := step_sound X hs (.increment 49 652 653) (by decide +kernel)
    simpa [Step.clause, CNF.Clause.eval] using hh
  · have hh := step_sound X hs (.carry 653 666) (by decide +kernel)
    simpa [Step.clause, CNF.Clause.eval] using hh
  · have hh := step_sound X hs (.increment 50 653 654) (by decide +kernel)
    simpa [Step.clause, CNF.Clause.eval] using hh
  · have hh := step_sound X hs (.carry 654 667) (by decide +kernel)
    simpa [Step.clause, CNF.Clause.eval] using hh
  · have hh := step_sound X hs (.increment 51 654 655) (by decide +kernel)
    simpa [Step.clause, CNF.Clause.eval] using hh
  · have hh := step_sound X hs (.carry 655 668) (by decide +kernel)
    simpa [Step.clause, CNF.Clause.eval] using hh
  · have hh := step_sound X hs (.increment 52 655 656) (by decide +kernel)
    simpa [Step.clause, CNF.Clause.eval] using hh
  · have hh := step_sound X hs (.carry 656 669) (by decide +kernel)
    simpa [Step.clause, CNF.Clause.eval] using hh
  · have hh := step_sound X hs (.increment 53 656 657) (by decide +kernel)
    simpa [Step.clause, CNF.Clause.eval] using hh
  · have hh := step_sound X hs (.carry 657 670) (by decide +kernel)
    simpa [Step.clause, CNF.Clause.eval] using hh
  · have hh := step_sound X hs (.increment 54 657 658) (by decide +kernel)
    simpa [Step.clause, CNF.Clause.eval] using hh
  · have hh := step_sound X hs (.carry 658 671) (by decide +kernel)
    simpa [Step.clause, CNF.Clause.eval] using hh
  · have hh := step_sound X hs (.increment 55 658 659) (by decide +kernel)
    simpa [Step.clause, CNF.Clause.eval] using hh
  · have hh := step_sound X hs (.carry 659 672) (by decide +kernel)
    simpa [Step.clause, CNF.Clause.eval] using hh
  · have hh := step_sound X hs (.increment 56 659 660) (by decide +kernel)
    simpa [Step.clause, CNF.Clause.eval] using hh
  · have hh := step_sound X hs (.carry 660 673) (by decide +kernel)
    simpa [Step.clause, CNF.Clause.eval] using hh
  · have hh := step_sound X hs (.increment 57 660 661) (by decide +kernel)
    simpa [Step.clause, CNF.Clause.eval] using hh
  · have hh := step_sound X hs (.carry 661 674) (by decide +kernel)
    simpa [Step.clause, CNF.Clause.eval] using hh
  · have hh := step_sound X hs (.increment 58 661 662) (by decide +kernel)
    simpa [Step.clause, CNF.Clause.eval] using hh
  · have hh := step_sound X hs (.carry 662 675) (by decide +kernel)
    simpa [Step.clause, CNF.Clause.eval] using hh
end LocalIdentifyingQ6
