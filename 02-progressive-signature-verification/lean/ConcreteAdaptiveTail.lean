import HistoryCells
import AdaptiveTail

namespace ProgressivePool
open Finset Classical
variable {F I J Y : Type*} [Field F] [Fintype F] [DecidableEq F]
  [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

def queryHeight : QueryTree J (I → F) Y → ℕ
  | .leaf _ => 0
  | .query _ _ next => 1 + max (queryHeight (next false)) (queryHeight (next true))

def freshMark (obs : List (Observation J (I → F))) (j : J) (w : I → F) : Bool :=
  decide (w ≠ 0 ∧ ∀ o ∈ obs, o.row = j → o.input ≠ 0 → o.answer = false)

noncomputable def markedExperiment (obs : List (Observation J (I → F))) :
    QueryTree J (I → F) Y → AdaptiveTail.Tree (J → I → F)
  | .leaf _ => .leaf
  | .query j w next => .node (fun bank => rowTest (bank j) w) (freshMark obs j w)
      (fun b => markedExperiment (obs ++ [⟨j,w,b⟩]) (next b))

theorem historyCell_append (obs : List (Observation J (I → F)))
    (j : J) (w : I → F) (b : Bool) :
    historyCell (obs ++ [⟨j,w,b⟩]) =
      AdaptiveTail.childCell (historyCell obs) (fun bank => rowTest (bank j) w) b := by
  ext bank
  simp only [historyCell, AdaptiveTail.childCell, mem_filter, mem_univ, true_and,
    historyCompatible, List.mem_append, List.mem_singleton]
  constructor
  · intro h
    exact ⟨fun o ho => h o (Or.inl ho), h _ (Or.inr rfl)⟩
  · rintro ⟨h,hb⟩ o (ho | rfl)
    · exact h o ho
    · exact hb

theorem markedExperiment_depth (obs : List (Observation J (I → F)))
    (tree : QueryTree J (I → F) Y) (N : ℕ) (h : queryHeight tree ≤ N) :
    AdaptiveTail.depthLE N (markedExperiment obs tree) := by
  induction tree generalizing obs N with
  | leaf _ => cases N <;> simp [markedExperiment, AdaptiveTail.depthLE]
  | query j w next ih =>
    cases N with
    | zero => simp [queryHeight] at h
    | succ n =>
      intro b
      apply ih b
      have hn : max (queryHeight (next false)) (queryHeight (next true)) ≤ n := by
        simp only [queryHeight] at h
        omega
      cases b
      · exact (le_max_left _ _).trans hn
      · exact (le_max_right _ _).trans hn

/-- Local first-spoil bounds for every node of the actual adaptive experiment,
derived from the finite-field counting theorem, including adaptive choices. -/
theorem markedExperiment_local (obs : List (Observation J (I → F)))
    (tree : QueryTree J (I → F) Y) (N : ℕ)
    (h : obs.length + queryHeight tree ≤ N) :
    AdaptiveTail.localBound (Fintype.card F-N) (historyCell obs)
      (markedExperiment obs tree) := by
  induction tree generalizing obs with
  | leaf _ => trivial
  | query j w next ih =>
    constructor
    · intro hm
      have hm' : w ≠ 0 ∧ ∀ o ∈ obs, o.row = j → o.input ≠ 0 → o.answer = false :=
        of_decide_eq_true hm
      exact historyCell_query_bound obs N (by omega) j w hm'.1 hm'.2
    · intro b
      rw [← historyCell_append]
      apply ih b
      simp only [List.length_append, List.length_singleton]
      have hm : queryHeight (next b) ≤
          max (queryHeight (next false)) (queryHeight (next true)) := by
        cases b
        · exact le_max_left _ _
        · exact le_max_right _ _
      simp only [queryHeight] at h
      omega

/-- Actual finite-field adaptive experiment: no conditional probability premise.
It bounds the number of first-spoil events, before the final virtual-pass lift. -/
theorem actual_first_spoil_tail (tree : QueryTree J (I → F) Y) (N u : ℕ)
    (h : queryHeight tree ≤ N) :
    (Fintype.card F-N)^u *
      AdaptiveTail.tailCount univ (markedExperiment [] tree) u ≤
        N.choose u * Fintype.card (J → I → F) := by
  have ht := AdaptiveTail.marked_tail_bound (Fintype.card F-N) N u
    (historyCell []) (markedExperiment [] tree)
    (markedExperiment_depth [] tree N h)
    (markedExperiment_local [] tree N (by simpa using h))
  simpa [historyCell, historyCompatible] using ht

#print axioms actual_first_spoil_tail
end ProgressivePool
