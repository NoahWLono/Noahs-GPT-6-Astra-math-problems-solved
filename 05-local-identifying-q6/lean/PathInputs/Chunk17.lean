import RUPPath.Inputs
import GraphClauseData
import CardinalityEncoding
open Std.Sat
namespace LocalIdentifyingQ6
open CardinalityEncoding
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem semanticChunk17 (C : Code) (X : Nat → Bool) (hX : ∀ v : Vertex, X (v.val+1) = C v)
    (hC : Constraints C) (hz0 : C 0 = true) (hz1 : C 1 = true) (hz2 : C 2 = true)
    (hs : prefixCount X 64 ≤ 13) :
    Q6RUPPath.InputChunk17 (fun n => assignment X n = true) := by
  have hA : ∀ v : Vertex, assignment X (v.val+1) = C v := by
    intro v
    rw [assignment_input X _ (by have := v.isLt; omega)]
    exact hX v
  refine { c851 := ?_, c852 := ?_, c853 := ?_, c854 := ?_, c855 := ?_, c856 := ?_, c857 := ?_, c858 := ?_, c859 := ?_, c860 := ?_, c861 := ?_, c862 := ?_, c863 := ?_, c864 := ?_, c865 := ?_, c866 := ?_, c867 := ?_, c868 := ?_, c869 := ?_, c870 := ?_, c871 := ?_, c872 := ?_, c873 := ?_, c874 := ?_, c875 := ?_, c876 := ?_, c877 := ?_, c878 := ?_, c879 := ?_, c880 := ?_, c881 := ?_, c882 := ?_, c883 := ?_, c884 := ?_, c885 := ?_, c886 := ?_, c887 := ?_, c888 := ?_, c889 := ?_, c890 := ?_, c891 := ?_, c892 := ?_, c893 := ?_, c894 := ?_, c895 := ?_, c896 := ?_, c897 := ?_, c898 := ?_, c899 := ?_, c900 := ?_ }
  · have hh := step_sound X hs (.increment 34 349 350) (by decide +kernel)
    simpa [Step.clause, CNF.Clause.eval] using hh
  · have hh := step_sound X hs (.carry 350 363) (by decide +kernel)
    simpa [Step.clause, CNF.Clause.eval] using hh
  · have hh := step_sound X hs (.overflow 35 350) (by decide +kernel)
    simpa [Step.clause, CNF.Clause.eval] using hh
  · have hh := step_sound X hs (.input 23 351) (by decide +kernel)
    simpa [Step.clause, CNF.Clause.eval] using hh
  · have hh := step_sound X hs (.carry 351 364) (by decide +kernel)
    simpa [Step.clause, CNF.Clause.eval] using hh
  · have hh := step_sound X hs (.increment 24 351 352) (by decide +kernel)
    simpa [Step.clause, CNF.Clause.eval] using hh
  · have hh := step_sound X hs (.carry 352 365) (by decide +kernel)
    simpa [Step.clause, CNF.Clause.eval] using hh
  · have hh := step_sound X hs (.increment 25 352 353) (by decide +kernel)
    simpa [Step.clause, CNF.Clause.eval] using hh
  · have hh := step_sound X hs (.carry 353 366) (by decide +kernel)
    simpa [Step.clause, CNF.Clause.eval] using hh
  · have hh := step_sound X hs (.increment 26 353 354) (by decide +kernel)
    simpa [Step.clause, CNF.Clause.eval] using hh
  · have hh := step_sound X hs (.carry 354 367) (by decide +kernel)
    simpa [Step.clause, CNF.Clause.eval] using hh
  · have hh := step_sound X hs (.increment 27 354 355) (by decide +kernel)
    simpa [Step.clause, CNF.Clause.eval] using hh
  · have hh := step_sound X hs (.carry 355 368) (by decide +kernel)
    simpa [Step.clause, CNF.Clause.eval] using hh
  · have hh := step_sound X hs (.increment 28 355 356) (by decide +kernel)
    simpa [Step.clause, CNF.Clause.eval] using hh
  · have hh := step_sound X hs (.carry 356 369) (by decide +kernel)
    simpa [Step.clause, CNF.Clause.eval] using hh
  · have hh := step_sound X hs (.increment 29 356 357) (by decide +kernel)
    simpa [Step.clause, CNF.Clause.eval] using hh
  · have hh := step_sound X hs (.carry 357 370) (by decide +kernel)
    simpa [Step.clause, CNF.Clause.eval] using hh
  · have hh := step_sound X hs (.increment 30 357 358) (by decide +kernel)
    simpa [Step.clause, CNF.Clause.eval] using hh
  · have hh := step_sound X hs (.carry 358 371) (by decide +kernel)
    simpa [Step.clause, CNF.Clause.eval] using hh
  · have hh := step_sound X hs (.increment 31 358 359) (by decide +kernel)
    simpa [Step.clause, CNF.Clause.eval] using hh
  · have hh := step_sound X hs (.carry 359 372) (by decide +kernel)
    simpa [Step.clause, CNF.Clause.eval] using hh
  · have hh := step_sound X hs (.increment 32 359 360) (by decide +kernel)
    simpa [Step.clause, CNF.Clause.eval] using hh
  · have hh := step_sound X hs (.carry 360 373) (by decide +kernel)
    simpa [Step.clause, CNF.Clause.eval] using hh
  · have hh := step_sound X hs (.increment 33 360 361) (by decide +kernel)
    simpa [Step.clause, CNF.Clause.eval] using hh
  · have hh := step_sound X hs (.carry 361 374) (by decide +kernel)
    simpa [Step.clause, CNF.Clause.eval] using hh
  · have hh := step_sound X hs (.increment 34 361 362) (by decide +kernel)
    simpa [Step.clause, CNF.Clause.eval] using hh
  · have hh := step_sound X hs (.carry 362 375) (by decide +kernel)
    simpa [Step.clause, CNF.Clause.eval] using hh
  · have hh := step_sound X hs (.increment 35 362 363) (by decide +kernel)
    simpa [Step.clause, CNF.Clause.eval] using hh
  · have hh := step_sound X hs (.carry 363 376) (by decide +kernel)
    simpa [Step.clause, CNF.Clause.eval] using hh
  · have hh := step_sound X hs (.overflow 36 363) (by decide +kernel)
    simpa [Step.clause, CNF.Clause.eval] using hh
  · have hh := step_sound X hs (.input 24 364) (by decide +kernel)
    simpa [Step.clause, CNF.Clause.eval] using hh
  · have hh := step_sound X hs (.carry 364 377) (by decide +kernel)
    simpa [Step.clause, CNF.Clause.eval] using hh
  · have hh := step_sound X hs (.increment 25 364 365) (by decide +kernel)
    simpa [Step.clause, CNF.Clause.eval] using hh
  · have hh := step_sound X hs (.carry 365 378) (by decide +kernel)
    simpa [Step.clause, CNF.Clause.eval] using hh
  · have hh := step_sound X hs (.increment 26 365 366) (by decide +kernel)
    simpa [Step.clause, CNF.Clause.eval] using hh
  · have hh := step_sound X hs (.carry 366 379) (by decide +kernel)
    simpa [Step.clause, CNF.Clause.eval] using hh
  · have hh := step_sound X hs (.increment 27 366 367) (by decide +kernel)
    simpa [Step.clause, CNF.Clause.eval] using hh
  · have hh := step_sound X hs (.carry 367 380) (by decide +kernel)
    simpa [Step.clause, CNF.Clause.eval] using hh
  · have hh := step_sound X hs (.increment 28 367 368) (by decide +kernel)
    simpa [Step.clause, CNF.Clause.eval] using hh
  · have hh := step_sound X hs (.carry 368 381) (by decide +kernel)
    simpa [Step.clause, CNF.Clause.eval] using hh
  · have hh := step_sound X hs (.increment 29 368 369) (by decide +kernel)
    simpa [Step.clause, CNF.Clause.eval] using hh
  · have hh := step_sound X hs (.carry 369 382) (by decide +kernel)
    simpa [Step.clause, CNF.Clause.eval] using hh
  · have hh := step_sound X hs (.increment 30 369 370) (by decide +kernel)
    simpa [Step.clause, CNF.Clause.eval] using hh
  · have hh := step_sound X hs (.carry 370 383) (by decide +kernel)
    simpa [Step.clause, CNF.Clause.eval] using hh
  · have hh := step_sound X hs (.increment 31 370 371) (by decide +kernel)
    simpa [Step.clause, CNF.Clause.eval] using hh
  · have hh := step_sound X hs (.carry 371 384) (by decide +kernel)
    simpa [Step.clause, CNF.Clause.eval] using hh
  · have hh := step_sound X hs (.increment 32 371 372) (by decide +kernel)
    simpa [Step.clause, CNF.Clause.eval] using hh
  · have hh := step_sound X hs (.carry 372 385) (by decide +kernel)
    simpa [Step.clause, CNF.Clause.eval] using hh
  · have hh := step_sound X hs (.increment 33 372 373) (by decide +kernel)
    simpa [Step.clause, CNF.Clause.eval] using hh
  · have hh := step_sound X hs (.carry 373 386) (by decide +kernel)
    simpa [Step.clause, CNF.Clause.eval] using hh
end LocalIdentifyingQ6
