import RUPPath.Inputs
import GraphClauseData
import CardinalityEncoding
open Std.Sat
namespace LocalIdentifyingQ6
open CardinalityEncoding
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem semanticChunk27 (C : Code) (X : Nat → Bool) (hX : ∀ v : Vertex, X (v.val+1) = C v)
    (hC : Constraints C) (hz0 : C 0 = true) (hz1 : C 1 = true) (hz2 : C 2 = true)
    (hs : prefixCount X 64 ≤ 13) :
    Q6RUPPath.InputChunk27 (fun n => assignment X n = true) := by
  have hA : ∀ v : Vertex, assignment X (v.val+1) = C v := by
    intro v
    rw [assignment_input X _ (by have := v.isLt; omega)]
    exact hX v
  refine { c1351 := ?_, c1352 := ?_, c1353 := ?_, c1354 := ?_, c1355 := ?_, c1356 := ?_, c1357 := ?_, c1358 := ?_, c1359 := ?_, c1360 := ?_, c1361 := ?_, c1362 := ?_, c1363 := ?_, c1364 := ?_, c1365 := ?_, c1366 := ?_, c1367 := ?_, c1368 := ?_, c1369 := ?_, c1370 := ?_, c1371 := ?_, c1372 := ?_, c1373 := ?_, c1374 := ?_, c1375 := ?_, c1376 := ?_, c1377 := ?_, c1378 := ?_, c1379 := ?_, c1380 := ?_, c1381 := ?_, c1382 := ?_, c1383 := ?_, c1384 := ?_, c1385 := ?_, c1386 := ?_, c1387 := ?_, c1388 := ?_, c1389 := ?_, c1390 := ?_, c1391 := ?_, c1392 := ?_, c1393 := ?_, c1394 := ?_, c1395 := ?_, c1396 := ?_, c1397 := ?_, c1398 := ?_, c1399 := ?_, c1400 := ?_ }
  · have hh := step_sound X hs (.carry 590 603) (by decide +kernel)
    simpa [Step.clause, CNF.Clause.eval] using hh
  · have hh := step_sound X hs (.increment 47 590 591) (by decide +kernel)
    simpa [Step.clause, CNF.Clause.eval] using hh
  · have hh := step_sound X hs (.carry 591 604) (by decide +kernel)
    simpa [Step.clause, CNF.Clause.eval] using hh
  · have hh := step_sound X hs (.increment 48 591 592) (by decide +kernel)
    simpa [Step.clause, CNF.Clause.eval] using hh
  · have hh := step_sound X hs (.carry 592 605) (by decide +kernel)
    simpa [Step.clause, CNF.Clause.eval] using hh
  · have hh := step_sound X hs (.increment 49 592 593) (by decide +kernel)
    simpa [Step.clause, CNF.Clause.eval] using hh
  · have hh := step_sound X hs (.carry 593 606) (by decide +kernel)
    simpa [Step.clause, CNF.Clause.eval] using hh
  · have hh := step_sound X hs (.increment 50 593 594) (by decide +kernel)
    simpa [Step.clause, CNF.Clause.eval] using hh
  · have hh := step_sound X hs (.carry 594 607) (by decide +kernel)
    simpa [Step.clause, CNF.Clause.eval] using hh
  · have hh := step_sound X hs (.increment 51 594 595) (by decide +kernel)
    simpa [Step.clause, CNF.Clause.eval] using hh
  · have hh := step_sound X hs (.carry 595 608) (by decide +kernel)
    simpa [Step.clause, CNF.Clause.eval] using hh
  · have hh := step_sound X hs (.increment 52 595 596) (by decide +kernel)
    simpa [Step.clause, CNF.Clause.eval] using hh
  · have hh := step_sound X hs (.carry 596 609) (by decide +kernel)
    simpa [Step.clause, CNF.Clause.eval] using hh
  · have hh := step_sound X hs (.increment 53 596 597) (by decide +kernel)
    simpa [Step.clause, CNF.Clause.eval] using hh
  · have hh := step_sound X hs (.carry 597 610) (by decide +kernel)
    simpa [Step.clause, CNF.Clause.eval] using hh
  · have hh := step_sound X hs (.overflow 54 597) (by decide +kernel)
    simpa [Step.clause, CNF.Clause.eval] using hh
  · have hh := step_sound X hs (.input 42 598) (by decide +kernel)
    simpa [Step.clause, CNF.Clause.eval] using hh
  · have hh := step_sound X hs (.carry 598 611) (by decide +kernel)
    simpa [Step.clause, CNF.Clause.eval] using hh
  · have hh := step_sound X hs (.increment 43 598 599) (by decide +kernel)
    simpa [Step.clause, CNF.Clause.eval] using hh
  · have hh := step_sound X hs (.carry 599 612) (by decide +kernel)
    simpa [Step.clause, CNF.Clause.eval] using hh
  · have hh := step_sound X hs (.increment 44 599 600) (by decide +kernel)
    simpa [Step.clause, CNF.Clause.eval] using hh
  · have hh := step_sound X hs (.carry 600 613) (by decide +kernel)
    simpa [Step.clause, CNF.Clause.eval] using hh
  · have hh := step_sound X hs (.increment 45 600 601) (by decide +kernel)
    simpa [Step.clause, CNF.Clause.eval] using hh
  · have hh := step_sound X hs (.carry 601 614) (by decide +kernel)
    simpa [Step.clause, CNF.Clause.eval] using hh
  · have hh := step_sound X hs (.increment 46 601 602) (by decide +kernel)
    simpa [Step.clause, CNF.Clause.eval] using hh
  · have hh := step_sound X hs (.carry 602 615) (by decide +kernel)
    simpa [Step.clause, CNF.Clause.eval] using hh
  · have hh := step_sound X hs (.increment 47 602 603) (by decide +kernel)
    simpa [Step.clause, CNF.Clause.eval] using hh
  · have hh := step_sound X hs (.carry 603 616) (by decide +kernel)
    simpa [Step.clause, CNF.Clause.eval] using hh
  · have hh := step_sound X hs (.increment 48 603 604) (by decide +kernel)
    simpa [Step.clause, CNF.Clause.eval] using hh
  · have hh := step_sound X hs (.carry 604 617) (by decide +kernel)
    simpa [Step.clause, CNF.Clause.eval] using hh
  · have hh := step_sound X hs (.increment 49 604 605) (by decide +kernel)
    simpa [Step.clause, CNF.Clause.eval] using hh
  · have hh := step_sound X hs (.carry 605 618) (by decide +kernel)
    simpa [Step.clause, CNF.Clause.eval] using hh
  · have hh := step_sound X hs (.increment 50 605 606) (by decide +kernel)
    simpa [Step.clause, CNF.Clause.eval] using hh
  · have hh := step_sound X hs (.carry 606 619) (by decide +kernel)
    simpa [Step.clause, CNF.Clause.eval] using hh
  · have hh := step_sound X hs (.increment 51 606 607) (by decide +kernel)
    simpa [Step.clause, CNF.Clause.eval] using hh
  · have hh := step_sound X hs (.carry 607 620) (by decide +kernel)
    simpa [Step.clause, CNF.Clause.eval] using hh
  · have hh := step_sound X hs (.increment 52 607 608) (by decide +kernel)
    simpa [Step.clause, CNF.Clause.eval] using hh
  · have hh := step_sound X hs (.carry 608 621) (by decide +kernel)
    simpa [Step.clause, CNF.Clause.eval] using hh
  · have hh := step_sound X hs (.increment 53 608 609) (by decide +kernel)
    simpa [Step.clause, CNF.Clause.eval] using hh
  · have hh := step_sound X hs (.carry 609 622) (by decide +kernel)
    simpa [Step.clause, CNF.Clause.eval] using hh
  · have hh := step_sound X hs (.increment 54 609 610) (by decide +kernel)
    simpa [Step.clause, CNF.Clause.eval] using hh
  · have hh := step_sound X hs (.carry 610 623) (by decide +kernel)
    simpa [Step.clause, CNF.Clause.eval] using hh
  · have hh := step_sound X hs (.overflow 55 610) (by decide +kernel)
    simpa [Step.clause, CNF.Clause.eval] using hh
  · have hh := step_sound X hs (.input 43 611) (by decide +kernel)
    simpa [Step.clause, CNF.Clause.eval] using hh
  · have hh := step_sound X hs (.carry 611 624) (by decide +kernel)
    simpa [Step.clause, CNF.Clause.eval] using hh
  · have hh := step_sound X hs (.increment 44 611 612) (by decide +kernel)
    simpa [Step.clause, CNF.Clause.eval] using hh
  · have hh := step_sound X hs (.carry 612 625) (by decide +kernel)
    simpa [Step.clause, CNF.Clause.eval] using hh
  · have hh := step_sound X hs (.increment 45 612 613) (by decide +kernel)
    simpa [Step.clause, CNF.Clause.eval] using hh
  · have hh := step_sound X hs (.carry 613 626) (by decide +kernel)
    simpa [Step.clause, CNF.Clause.eval] using hh
  · have hh := step_sound X hs (.increment 46 613 614) (by decide +kernel)
    simpa [Step.clause, CNF.Clause.eval] using hh
end LocalIdentifyingQ6
