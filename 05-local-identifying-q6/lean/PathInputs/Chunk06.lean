import RUPPath.Inputs
import GraphClauseData
import CardinalityEncoding
open Std.Sat
namespace LocalIdentifyingQ6
open CardinalityEncoding
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem semanticChunk6 (C : Code) (X : Nat → Bool) (hX : ∀ v : Vertex, X (v.val+1) = C v)
    (hC : Constraints C) (hz0 : C 0 = true) (hz1 : C 1 = true) (hz2 : C 2 = true)
    (hs : prefixCount X 64 ≤ 13) :
    Q6RUPPath.InputChunk6 (fun n => assignment X n = true) := by
  have hA : ∀ v : Vertex, assignment X (v.val+1) = C v := by
    intro v
    rw [assignment_input X _ (by have := v.isLt; omega)]
    exact hX v
  refine { c301 := ?_, c302 := ?_, c303 := ?_, c304 := ?_, c305 := ?_, c306 := ?_, c307 := ?_, c308 := ?_, c309 := ?_, c310 := ?_, c311 := ?_, c312 := ?_, c313 := ?_, c314 := ?_, c315 := ?_, c316 := ?_, c317 := ?_, c318 := ?_, c319 := ?_, c320 := ?_, c321 := ?_, c322 := ?_, c323 := ?_, c324 := ?_, c325 := ?_, c326 := ?_, c327 := ?_, c328 := ?_, c329 := ?_, c330 := ?_, c331 := ?_, c332 := ?_, c333 := ?_, c334 := ?_, c335 := ?_, c336 := ?_, c337 := ?_, c338 := ?_, c339 := ?_, c340 := ?_, c341 := ?_, c342 := ?_, c343 := ?_, c344 := ?_, c345 := ?_, c346 := ?_, c347 := ?_, c348 := ?_, c349 := ?_, c350 := ?_ }
  · have hh := step_sound X hs (.increment 9 78 80) (by decide +kernel)
    simpa [Step.clause, CNF.Clause.eval] using hh
  · have hh := step_sound X hs (.carry 80 98) (by decide +kernel)
    simpa [Step.clause, CNF.Clause.eval] using hh
  · have hh := step_sound X hs (.increment 10 80 82) (by decide +kernel)
    simpa [Step.clause, CNF.Clause.eval] using hh
  · have hh := step_sound X hs (.carry 82 99) (by decide +kernel)
    simpa [Step.clause, CNF.Clause.eval] using hh
  · have hh := step_sound X hs (.increment 11 82 84) (by decide +kernel)
    simpa [Step.clause, CNF.Clause.eval] using hh
  · have hh := step_sound X hs (.carry 84 100) (by decide +kernel)
    simpa [Step.clause, CNF.Clause.eval] using hh
  · have hh := step_sound X hs (.increment 12 84 86) (by decide +kernel)
    simpa [Step.clause, CNF.Clause.eval] using hh
  · have hh := step_sound X hs (.carry 86 101) (by decide +kernel)
    simpa [Step.clause, CNF.Clause.eval] using hh
  · have hh := step_sound X hs (.increment 13 86 88) (by decide +kernel)
    simpa [Step.clause, CNF.Clause.eval] using hh
  · have hh := step_sound X hs (.carry 88 102) (by decide +kernel)
    simpa [Step.clause, CNF.Clause.eval] using hh
  · have hh := step_sound X hs (.increment 14 88 90) (by decide +kernel)
    simpa [Step.clause, CNF.Clause.eval] using hh
  · have hh := step_sound X hs (.carry 90 103) (by decide +kernel)
    simpa [Step.clause, CNF.Clause.eval] using hh
  · have hh := step_sound X hs (.overflow 15 90) (by decide +kernel)
    simpa [Step.clause, CNF.Clause.eval] using hh
  · have hh := step_sound X hs (.input 3 91) (by decide +kernel)
    simpa [Step.clause, CNF.Clause.eval] using hh
  · have hh := step_sound X hs (.carry 91 104) (by decide +kernel)
    simpa [Step.clause, CNF.Clause.eval] using hh
  · have hh := step_sound X hs (.increment 4 91 92) (by decide +kernel)
    simpa [Step.clause, CNF.Clause.eval] using hh
  · have hh := step_sound X hs (.carry 92 105) (by decide +kernel)
    simpa [Step.clause, CNF.Clause.eval] using hh
  · have hh := step_sound X hs (.increment 5 92 93) (by decide +kernel)
    simpa [Step.clause, CNF.Clause.eval] using hh
  · have hh := step_sound X hs (.carry 93 106) (by decide +kernel)
    simpa [Step.clause, CNF.Clause.eval] using hh
  · have hh := step_sound X hs (.increment 6 93 94) (by decide +kernel)
    simpa [Step.clause, CNF.Clause.eval] using hh
  · have hh := step_sound X hs (.carry 94 107) (by decide +kernel)
    simpa [Step.clause, CNF.Clause.eval] using hh
  · have hh := step_sound X hs (.increment 7 94 95) (by decide +kernel)
    simpa [Step.clause, CNF.Clause.eval] using hh
  · have hh := step_sound X hs (.carry 95 108) (by decide +kernel)
    simpa [Step.clause, CNF.Clause.eval] using hh
  · have hh := step_sound X hs (.increment 8 95 96) (by decide +kernel)
    simpa [Step.clause, CNF.Clause.eval] using hh
  · have hh := step_sound X hs (.carry 96 109) (by decide +kernel)
    simpa [Step.clause, CNF.Clause.eval] using hh
  · have hh := step_sound X hs (.increment 9 96 97) (by decide +kernel)
    simpa [Step.clause, CNF.Clause.eval] using hh
  · have hh := step_sound X hs (.carry 97 110) (by decide +kernel)
    simpa [Step.clause, CNF.Clause.eval] using hh
  · have hh := step_sound X hs (.increment 10 97 98) (by decide +kernel)
    simpa [Step.clause, CNF.Clause.eval] using hh
  · have hh := step_sound X hs (.carry 98 111) (by decide +kernel)
    simpa [Step.clause, CNF.Clause.eval] using hh
  · have hh := step_sound X hs (.increment 11 98 99) (by decide +kernel)
    simpa [Step.clause, CNF.Clause.eval] using hh
  · have hh := step_sound X hs (.carry 99 112) (by decide +kernel)
    simpa [Step.clause, CNF.Clause.eval] using hh
  · have hh := step_sound X hs (.increment 12 99 100) (by decide +kernel)
    simpa [Step.clause, CNF.Clause.eval] using hh
  · have hh := step_sound X hs (.carry 100 113) (by decide +kernel)
    simpa [Step.clause, CNF.Clause.eval] using hh
  · have hh := step_sound X hs (.increment 13 100 101) (by decide +kernel)
    simpa [Step.clause, CNF.Clause.eval] using hh
  · have hh := step_sound X hs (.carry 101 114) (by decide +kernel)
    simpa [Step.clause, CNF.Clause.eval] using hh
  · have hh := step_sound X hs (.increment 14 101 102) (by decide +kernel)
    simpa [Step.clause, CNF.Clause.eval] using hh
  · have hh := step_sound X hs (.carry 102 115) (by decide +kernel)
    simpa [Step.clause, CNF.Clause.eval] using hh
  · have hh := step_sound X hs (.increment 15 102 103) (by decide +kernel)
    simpa [Step.clause, CNF.Clause.eval] using hh
  · have hh := step_sound X hs (.carry 103 116) (by decide +kernel)
    simpa [Step.clause, CNF.Clause.eval] using hh
  · have hh := step_sound X hs (.overflow 16 103) (by decide +kernel)
    simpa [Step.clause, CNF.Clause.eval] using hh
  · have hh := step_sound X hs (.input 4 104) (by decide +kernel)
    simpa [Step.clause, CNF.Clause.eval] using hh
  · have hh := step_sound X hs (.carry 104 117) (by decide +kernel)
    simpa [Step.clause, CNF.Clause.eval] using hh
  · have hh := step_sound X hs (.increment 5 104 105) (by decide +kernel)
    simpa [Step.clause, CNF.Clause.eval] using hh
  · have hh := step_sound X hs (.carry 105 118) (by decide +kernel)
    simpa [Step.clause, CNF.Clause.eval] using hh
  · have hh := step_sound X hs (.increment 6 105 106) (by decide +kernel)
    simpa [Step.clause, CNF.Clause.eval] using hh
  · have hh := step_sound X hs (.carry 106 119) (by decide +kernel)
    simpa [Step.clause, CNF.Clause.eval] using hh
  · have hh := step_sound X hs (.increment 7 106 107) (by decide +kernel)
    simpa [Step.clause, CNF.Clause.eval] using hh
  · have hh := step_sound X hs (.carry 107 120) (by decide +kernel)
    simpa [Step.clause, CNF.Clause.eval] using hh
  · have hh := step_sound X hs (.increment 8 107 108) (by decide +kernel)
    simpa [Step.clause, CNF.Clause.eval] using hh
  · have hh := step_sound X hs (.carry 108 121) (by decide +kernel)
    simpa [Step.clause, CNF.Clause.eval] using hh
end LocalIdentifyingQ6
