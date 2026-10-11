import RUPPath.Inputs
import GraphClauseData
import CardinalityEncoding
open Std.Sat
namespace LocalIdentifyingQ6
open CardinalityEncoding
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem semanticChunk5 (C : Code) (X : Nat → Bool) (hX : ∀ v : Vertex, X (v.val+1) = C v)
    (hC : Constraints C) (hz0 : C 0 = true) (hz1 : C 1 = true) (hz2 : C 2 = true)
    (hs : prefixCount X 64 ≤ 13) :
    Q6RUPPath.InputChunk5 (fun n => assignment X n = true) := by
  have hA : ∀ v : Vertex, assignment X (v.val+1) = C v := by
    intro v
    rw [assignment_input X _ (by have := v.isLt; omega)]
    exact hX v
  refine { c251 := ?_, c252 := ?_, c253 := ?_, c254 := ?_, c255 := ?_, c256 := ?_, c257 := ?_, c258 := ?_, c259 := ?_, c260 := ?_, c261 := ?_, c262 := ?_, c263 := ?_, c264 := ?_, c265 := ?_, c266 := ?_, c267 := ?_, c268 := ?_, c269 := ?_, c270 := ?_, c271 := ?_, c272 := ?_, c273 := ?_, c274 := ?_, c275 := ?_, c276 := ?_, c277 := ?_, c278 := ?_, c279 := ?_, c280 := ?_, c281 := ?_, c282 := ?_, c283 := ?_, c284 := ?_, c285 := ?_, c286 := ?_, c287 := ?_, c288 := ?_, c289 := ?_, c290 := ?_, c291 := ?_, c292 := ?_, c293 := ?_, c294 := ?_, c295 := ?_, c296 := ?_, c297 := ?_, c298 := ?_, c299 := ?_, c300 := ?_ }
  · have hh := (separationClause_sat (assignment X) C hA 58 62).mpr (hC.2 58 62 (by decide))
    rw [sep_data_186] at hh
    simpa [CNF.Clause.eval] using hh
  · have hh := (separationClause_sat (assignment X) C hA 59 63).mpr (hC.2 59 63 (by decide))
    rw [sep_data_187] at hh
    simpa [CNF.Clause.eval] using hh
  · have hh := (separationClause_sat (assignment X) C hA 60 61).mpr (hC.2 60 61 (by decide))
    rw [sep_data_188] at hh
    simpa [CNF.Clause.eval] using hh
  · have hh := (separationClause_sat (assignment X) C hA 60 62).mpr (hC.2 60 62 (by decide))
    rw [sep_data_189] at hh
    simpa [CNF.Clause.eval] using hh
  · have hh := (separationClause_sat (assignment X) C hA 61 63).mpr (hC.2 61 63 (by decide))
    rw [sep_data_190] at hh
    simpa [CNF.Clause.eval] using hh
  · have hh := (separationClause_sat (assignment X) C hA 62 63).mpr (hC.2 62 63 (by decide))
    rw [sep_data_191] at hh
    simpa [CNF.Clause.eval] using hh
  · simpa using (hA (0 : Vertex)).trans hz0
  · simpa using (hA (1 : Vertex)).trans hz1
  · simpa using (hA (2 : Vertex)).trans hz2
  · have hh := step_sound X hs (.input 1 65) (by decide +kernel)
    simpa [Step.clause, CNF.Clause.eval] using hh
  · have hh := step_sound X hs (.carry 65 66) (by decide +kernel)
    simpa [Step.clause, CNF.Clause.eval] using hh
  · have hh := step_sound X hs (.increment 2 65 67) (by decide +kernel)
    simpa [Step.clause, CNF.Clause.eval] using hh
  · have hh := step_sound X hs (.carry 67 68) (by decide +kernel)
    simpa [Step.clause, CNF.Clause.eval] using hh
  · have hh := step_sound X hs (.increment 3 67 69) (by decide +kernel)
    simpa [Step.clause, CNF.Clause.eval] using hh
  · have hh := step_sound X hs (.carry 69 70) (by decide +kernel)
    simpa [Step.clause, CNF.Clause.eval] using hh
  · have hh := step_sound X hs (.increment 4 69 71) (by decide +kernel)
    simpa [Step.clause, CNF.Clause.eval] using hh
  · have hh := step_sound X hs (.carry 71 72) (by decide +kernel)
    simpa [Step.clause, CNF.Clause.eval] using hh
  · have hh := step_sound X hs (.increment 5 71 73) (by decide +kernel)
    simpa [Step.clause, CNF.Clause.eval] using hh
  · have hh := step_sound X hs (.carry 73 74) (by decide +kernel)
    simpa [Step.clause, CNF.Clause.eval] using hh
  · have hh := step_sound X hs (.increment 6 73 75) (by decide +kernel)
    simpa [Step.clause, CNF.Clause.eval] using hh
  · have hh := step_sound X hs (.carry 75 76) (by decide +kernel)
    simpa [Step.clause, CNF.Clause.eval] using hh
  · have hh := step_sound X hs (.increment 7 75 77) (by decide +kernel)
    simpa [Step.clause, CNF.Clause.eval] using hh
  · have hh := step_sound X hs (.carry 77 78) (by decide +kernel)
    simpa [Step.clause, CNF.Clause.eval] using hh
  · have hh := step_sound X hs (.increment 8 77 79) (by decide +kernel)
    simpa [Step.clause, CNF.Clause.eval] using hh
  · have hh := step_sound X hs (.carry 79 80) (by decide +kernel)
    simpa [Step.clause, CNF.Clause.eval] using hh
  · have hh := step_sound X hs (.increment 9 79 81) (by decide +kernel)
    simpa [Step.clause, CNF.Clause.eval] using hh
  · have hh := step_sound X hs (.carry 81 82) (by decide +kernel)
    simpa [Step.clause, CNF.Clause.eval] using hh
  · have hh := step_sound X hs (.increment 10 81 83) (by decide +kernel)
    simpa [Step.clause, CNF.Clause.eval] using hh
  · have hh := step_sound X hs (.carry 83 84) (by decide +kernel)
    simpa [Step.clause, CNF.Clause.eval] using hh
  · have hh := step_sound X hs (.increment 11 83 85) (by decide +kernel)
    simpa [Step.clause, CNF.Clause.eval] using hh
  · have hh := step_sound X hs (.carry 85 86) (by decide +kernel)
    simpa [Step.clause, CNF.Clause.eval] using hh
  · have hh := step_sound X hs (.increment 12 85 87) (by decide +kernel)
    simpa [Step.clause, CNF.Clause.eval] using hh
  · have hh := step_sound X hs (.carry 87 88) (by decide +kernel)
    simpa [Step.clause, CNF.Clause.eval] using hh
  · have hh := step_sound X hs (.increment 13 87 89) (by decide +kernel)
    simpa [Step.clause, CNF.Clause.eval] using hh
  · have hh := step_sound X hs (.carry 89 90) (by decide +kernel)
    simpa [Step.clause, CNF.Clause.eval] using hh
  · have hh := step_sound X hs (.overflow 14 89) (by decide +kernel)
    simpa [Step.clause, CNF.Clause.eval] using hh
  · have hh := step_sound X hs (.input 2 66) (by decide +kernel)
    simpa [Step.clause, CNF.Clause.eval] using hh
  · have hh := step_sound X hs (.carry 66 91) (by decide +kernel)
    simpa [Step.clause, CNF.Clause.eval] using hh
  · have hh := step_sound X hs (.increment 3 66 68) (by decide +kernel)
    simpa [Step.clause, CNF.Clause.eval] using hh
  · have hh := step_sound X hs (.carry 68 92) (by decide +kernel)
    simpa [Step.clause, CNF.Clause.eval] using hh
  · have hh := step_sound X hs (.increment 4 68 70) (by decide +kernel)
    simpa [Step.clause, CNF.Clause.eval] using hh
  · have hh := step_sound X hs (.carry 70 93) (by decide +kernel)
    simpa [Step.clause, CNF.Clause.eval] using hh
  · have hh := step_sound X hs (.increment 5 70 72) (by decide +kernel)
    simpa [Step.clause, CNF.Clause.eval] using hh
  · have hh := step_sound X hs (.carry 72 94) (by decide +kernel)
    simpa [Step.clause, CNF.Clause.eval] using hh
  · have hh := step_sound X hs (.increment 6 72 74) (by decide +kernel)
    simpa [Step.clause, CNF.Clause.eval] using hh
  · have hh := step_sound X hs (.carry 74 95) (by decide +kernel)
    simpa [Step.clause, CNF.Clause.eval] using hh
  · have hh := step_sound X hs (.increment 7 74 76) (by decide +kernel)
    simpa [Step.clause, CNF.Clause.eval] using hh
  · have hh := step_sound X hs (.carry 76 96) (by decide +kernel)
    simpa [Step.clause, CNF.Clause.eval] using hh
  · have hh := step_sound X hs (.increment 8 76 78) (by decide +kernel)
    simpa [Step.clause, CNF.Clause.eval] using hh
  · have hh := step_sound X hs (.carry 78 97) (by decide +kernel)
    simpa [Step.clause, CNF.Clause.eval] using hh
end LocalIdentifyingQ6
