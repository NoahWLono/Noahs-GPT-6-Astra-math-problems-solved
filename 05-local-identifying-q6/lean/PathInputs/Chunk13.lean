import RUPPath.Inputs
import GraphClauseData
import CardinalityEncoding
open Std.Sat
namespace LocalIdentifyingQ6
open CardinalityEncoding
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem semanticChunk13 (C : Code) (X : Nat → Bool) (hX : ∀ v : Vertex, X (v.val+1) = C v)
    (hC : Constraints C) (hz0 : C 0 = true) (hz1 : C 1 = true) (hz2 : C 2 = true)
    (hs : prefixCount X 64 ≤ 13) :
    Q6RUPPath.InputChunk13 (fun n => assignment X n = true) := by
  have hA : ∀ v : Vertex, assignment X (v.val+1) = C v := by
    intro v
    rw [assignment_input X _ (by have := v.isLt; omega)]
    exact hX v
  refine { c651 := ?_, c652 := ?_, c653 := ?_, c654 := ?_, c655 := ?_, c656 := ?_, c657 := ?_, c658 := ?_, c659 := ?_, c660 := ?_, c661 := ?_, c662 := ?_, c663 := ?_, c664 := ?_, c665 := ?_, c666 := ?_, c667 := ?_, c668 := ?_, c669 := ?_, c670 := ?_, c671 := ?_, c672 := ?_, c673 := ?_, c674 := ?_, c675 := ?_, c676 := ?_, c677 := ?_, c678 := ?_, c679 := ?_, c680 := ?_, c681 := ?_, c682 := ?_, c683 := ?_, c684 := ?_, c685 := ?_, c686 := ?_, c687 := ?_, c688 := ?_, c689 := ?_, c690 := ?_, c691 := ?_, c692 := ?_, c693 := ?_, c694 := ?_, c695 := ?_, c696 := ?_, c697 := ?_, c698 := ?_, c699 := ?_, c700 := ?_ }
  · have hh := step_sound X hs (.carry 253 266) (by decide +kernel)
    simpa [Step.clause, CNF.Clause.eval] using hh
  · have hh := step_sound X hs (.increment 22 253 254) (by decide +kernel)
    simpa [Step.clause, CNF.Clause.eval] using hh
  · have hh := step_sound X hs (.carry 254 267) (by decide +kernel)
    simpa [Step.clause, CNF.Clause.eval] using hh
  · have hh := step_sound X hs (.increment 23 254 255) (by decide +kernel)
    simpa [Step.clause, CNF.Clause.eval] using hh
  · have hh := step_sound X hs (.carry 255 268) (by decide +kernel)
    simpa [Step.clause, CNF.Clause.eval] using hh
  · have hh := step_sound X hs (.increment 24 255 256) (by decide +kernel)
    simpa [Step.clause, CNF.Clause.eval] using hh
  · have hh := step_sound X hs (.carry 256 269) (by decide +kernel)
    simpa [Step.clause, CNF.Clause.eval] using hh
  · have hh := step_sound X hs (.increment 25 256 257) (by decide +kernel)
    simpa [Step.clause, CNF.Clause.eval] using hh
  · have hh := step_sound X hs (.carry 257 270) (by decide +kernel)
    simpa [Step.clause, CNF.Clause.eval] using hh
  · have hh := step_sound X hs (.increment 26 257 258) (by decide +kernel)
    simpa [Step.clause, CNF.Clause.eval] using hh
  · have hh := step_sound X hs (.carry 258 271) (by decide +kernel)
    simpa [Step.clause, CNF.Clause.eval] using hh
  · have hh := step_sound X hs (.increment 27 258 259) (by decide +kernel)
    simpa [Step.clause, CNF.Clause.eval] using hh
  · have hh := step_sound X hs (.carry 259 272) (by decide +kernel)
    simpa [Step.clause, CNF.Clause.eval] using hh
  · have hh := step_sound X hs (.overflow 28 259) (by decide +kernel)
    simpa [Step.clause, CNF.Clause.eval] using hh
  · have hh := step_sound X hs (.input 16 260) (by decide +kernel)
    simpa [Step.clause, CNF.Clause.eval] using hh
  · have hh := step_sound X hs (.carry 260 273) (by decide +kernel)
    simpa [Step.clause, CNF.Clause.eval] using hh
  · have hh := step_sound X hs (.increment 17 260 261) (by decide +kernel)
    simpa [Step.clause, CNF.Clause.eval] using hh
  · have hh := step_sound X hs (.carry 261 274) (by decide +kernel)
    simpa [Step.clause, CNF.Clause.eval] using hh
  · have hh := step_sound X hs (.increment 18 261 262) (by decide +kernel)
    simpa [Step.clause, CNF.Clause.eval] using hh
  · have hh := step_sound X hs (.carry 262 275) (by decide +kernel)
    simpa [Step.clause, CNF.Clause.eval] using hh
  · have hh := step_sound X hs (.increment 19 262 263) (by decide +kernel)
    simpa [Step.clause, CNF.Clause.eval] using hh
  · have hh := step_sound X hs (.carry 263 276) (by decide +kernel)
    simpa [Step.clause, CNF.Clause.eval] using hh
  · have hh := step_sound X hs (.increment 20 263 264) (by decide +kernel)
    simpa [Step.clause, CNF.Clause.eval] using hh
  · have hh := step_sound X hs (.carry 264 277) (by decide +kernel)
    simpa [Step.clause, CNF.Clause.eval] using hh
  · have hh := step_sound X hs (.increment 21 264 265) (by decide +kernel)
    simpa [Step.clause, CNF.Clause.eval] using hh
  · have hh := step_sound X hs (.carry 265 278) (by decide +kernel)
    simpa [Step.clause, CNF.Clause.eval] using hh
  · have hh := step_sound X hs (.increment 22 265 266) (by decide +kernel)
    simpa [Step.clause, CNF.Clause.eval] using hh
  · have hh := step_sound X hs (.carry 266 279) (by decide +kernel)
    simpa [Step.clause, CNF.Clause.eval] using hh
  · have hh := step_sound X hs (.increment 23 266 267) (by decide +kernel)
    simpa [Step.clause, CNF.Clause.eval] using hh
  · have hh := step_sound X hs (.carry 267 280) (by decide +kernel)
    simpa [Step.clause, CNF.Clause.eval] using hh
  · have hh := step_sound X hs (.increment 24 267 268) (by decide +kernel)
    simpa [Step.clause, CNF.Clause.eval] using hh
  · have hh := step_sound X hs (.carry 268 281) (by decide +kernel)
    simpa [Step.clause, CNF.Clause.eval] using hh
  · have hh := step_sound X hs (.increment 25 268 269) (by decide +kernel)
    simpa [Step.clause, CNF.Clause.eval] using hh
  · have hh := step_sound X hs (.carry 269 282) (by decide +kernel)
    simpa [Step.clause, CNF.Clause.eval] using hh
  · have hh := step_sound X hs (.increment 26 269 270) (by decide +kernel)
    simpa [Step.clause, CNF.Clause.eval] using hh
  · have hh := step_sound X hs (.carry 270 283) (by decide +kernel)
    simpa [Step.clause, CNF.Clause.eval] using hh
  · have hh := step_sound X hs (.increment 27 270 271) (by decide +kernel)
    simpa [Step.clause, CNF.Clause.eval] using hh
  · have hh := step_sound X hs (.carry 271 284) (by decide +kernel)
    simpa [Step.clause, CNF.Clause.eval] using hh
  · have hh := step_sound X hs (.increment 28 271 272) (by decide +kernel)
    simpa [Step.clause, CNF.Clause.eval] using hh
  · have hh := step_sound X hs (.carry 272 285) (by decide +kernel)
    simpa [Step.clause, CNF.Clause.eval] using hh
  · have hh := step_sound X hs (.overflow 29 272) (by decide +kernel)
    simpa [Step.clause, CNF.Clause.eval] using hh
  · have hh := step_sound X hs (.input 17 273) (by decide +kernel)
    simpa [Step.clause, CNF.Clause.eval] using hh
  · have hh := step_sound X hs (.carry 273 286) (by decide +kernel)
    simpa [Step.clause, CNF.Clause.eval] using hh
  · have hh := step_sound X hs (.increment 18 273 274) (by decide +kernel)
    simpa [Step.clause, CNF.Clause.eval] using hh
  · have hh := step_sound X hs (.carry 274 287) (by decide +kernel)
    simpa [Step.clause, CNF.Clause.eval] using hh
  · have hh := step_sound X hs (.increment 19 274 275) (by decide +kernel)
    simpa [Step.clause, CNF.Clause.eval] using hh
  · have hh := step_sound X hs (.carry 275 288) (by decide +kernel)
    simpa [Step.clause, CNF.Clause.eval] using hh
  · have hh := step_sound X hs (.increment 20 275 276) (by decide +kernel)
    simpa [Step.clause, CNF.Clause.eval] using hh
  · have hh := step_sound X hs (.carry 276 289) (by decide +kernel)
    simpa [Step.clause, CNF.Clause.eval] using hh
  · have hh := step_sound X hs (.increment 21 276 277) (by decide +kernel)
    simpa [Step.clause, CNF.Clause.eval] using hh
end LocalIdentifyingQ6
