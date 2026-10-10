import ActualConditionalBound
import FirstSpoilCounting

namespace ProgressivePool
open Finset Classical
variable {J X K : Type*}

def historyTree : List (Observation J X) → QueryTree J X Unit
  | [] => .leaf ()
  | o :: os => .query o.row o.input
      (fun b => if b = o.answer then historyTree os else .leaf ())

theorem historyTree_valid (obs : List (Observation J X)) :
    pathValid (historyTree obs) (obs.map Observation.answer) := by
  induction obs with
  | nil => rfl
  | cons o os ih => simpa [historyTree, pathValid] using ih

theorem historyTree_observations (obs : List (Observation J X)) :
    pathObservations (historyTree obs) (obs.map Observation.answer) = obs := by
  induction obs with
  | nil => rfl
  | cons o os ih => simpa [historyTree, pathObservations, ih] using congrArg (fun x => x :: os) (show ⟨o.row,o.input,o.answer⟩ = o from rfl)

def historyCompatible (test : K → X → Bool) (bank : J → K)
    (obs : List (Observation J X)) : Prop :=
  ∀ o ∈ obs, test (bank o.row) o.input = o.answer

theorem historyTree_run_iff (test : K → X → Bool) (bank : J → K)
    (obs : List (Observation J X)) :
    runBits test bank (historyTree obs) = obs.map Observation.answer ↔
      historyCompatible test bank obs := by
  rw [actual_transcript_factorization, historyTree_observations,
    and_iff_right (historyTree_valid obs)]
  constructor
  · intro h o ho
    exact h o.row o ho rfl
  · intro h j o ho hj
    simpa [← hj] using h o ho

variable {F I : Type*} [Field F] [Fintype F] [DecidableEq F]
  [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

noncomputable def historyCell (obs : List (Observation J (I → F))) :
    Finset (J → I → F) := univ.filter fun bank => historyCompatible rowTest bank obs

theorem historyCell_query_bound (obs : List (Observation J (I → F))) (L : ℕ)
    (hlen : obs.length ≤ L) (j : J) (w : I → F) (hw : w ≠ 0)
    (unspoiled : ∀ o ∈ obs, o.row = j → o.input ≠ 0 → o.answer = false) :
    (Fintype.card F-L) *
      ((historyCell obs).filter fun bank => rowTest (bank j) w = true).card ≤
        (historyCell obs).card := by
  have hb := actual_query_count_bound (historyTree obs) (obs.map Observation.answer) L
    (by simpa [historyTree_observations] using hlen) j w hw
    (by simpa [historyTree_observations] using unspoiled)
  have he : (univ.filter fun bank : J → I → F =>
      runBits rowTest bank (historyTree obs) = obs.map Observation.answer) = historyCell obs := by
    ext bank
    simp only [historyCell, mem_filter, mem_univ, true_and, historyTree_run_iff]
  dsimp only at hb
  rw [he] at hb
  simpa only [rowTest, decide_eq_true_eq] using hb

#print axioms historyCell_query_bound
end ProgressivePool
