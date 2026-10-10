import SpoiledRows

namespace ProgressivePool
open Finset Classical
variable {F I J Y : Type*} [Field F] [Fintype F] [DecidableEq F]
  [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

def runOutput (bank : J → I → F) : QueryTree J (I → F) Y → Y
  | .leaf y => y
  | .query j w next => runOutput bank (next (rowTest (bank j) w))

def runObservations (bank : J → I → F) :
    QueryTree J (I → F) Y → List (Observation J (I → F))
  | .leaf _ => []
  | .query j w next =>
    let b := rowTest (bank j) w
    ⟨j,w,b⟩ :: runObservations bank (next b)

theorem spoiledRows_execution (bank : J → I → F)
    (tree : QueryTree J (I → F) Y) (obs : List (Observation J (I → F))) :
    (spoiledRows (obs ++ runObservations bank tree)).card =
      (spoiledRows obs).card + AdaptiveTail.successes (markedExperiment obs tree) bank := by
  induction tree generalizing obs with
  | leaf _ => simp [runObservations, markedExperiment, AdaptiveTail.successes]
  | query j w next ih =>
    let b := rowTest (bank j) w
    change (spoiledRows (obs ++ ⟨j,w,b⟩ :: runObservations bank (next b))).card = _
    have he : obs ++ ⟨j,w,b⟩ :: runObservations bank (next b) =
        (obs ++ [⟨j,w,b⟩]) ++ runObservations bank (next b) := by simp
    rw [he, ih, spoiledRows_card_step]
    simp [markedExperiment, AdaptiveTail.successes, b, Nat.add_assoc]

def virtualPass (rows : List J) (w : I → F) : QueryTree J (I → F) (I → F) :=
  match rows with
  | [] => .leaf w
  | j :: js => .query j w (fun _ => virtualPass js w)

def finalExperiment (rows : List J) : QueryTree J (I → F) (I → F) →
    QueryTree J (I → F) (I → F)
  | .leaf w => virtualPass rows w
  | .query j w next => .query j w (fun b => finalExperiment rows (next b))

theorem virtualPass_observations (bank : J → I → F) (rows : List J) (w : I → F) :
    runObservations bank (virtualPass rows w) =
      rows.map (fun j => ⟨j,w,rowTest (bank j) w⟩) := by
  induction rows with
  | nil => rfl
  | cons j js ih => simp [virtualPass, runObservations, ih]

theorem finalExperiment_observations (bank : J → I → F) (rows : List J)
    (tree : QueryTree J (I → F) (I → F)) :
    runObservations bank (finalExperiment rows tree) = runObservations bank tree ++
      rows.map (fun j => ⟨j,runOutput bank tree,rowTest (bank j) (runOutput bank tree)⟩) := by
  induction tree with
  | leaf w => simp [finalExperiment, runOutput, runObservations, virtualPass_observations]
  | query j w next ih => simp [finalExperiment, runObservations, runOutput, ih]

theorem virtualPass_height (rows : List J) (w : I → F) :
    queryHeight (virtualPass rows w) = rows.length := by
  induction rows with
  | nil => rfl
  | cons j js ih => simp [virtualPass, queryHeight, ih, Nat.add_comm]

theorem finalExperiment_height (rows : List J) (tree : QueryTree J (I → F) (I → F)) :
    queryHeight (finalExperiment rows tree) = queryHeight tree + rows.length := by
  induction tree with
  | leaf w => simp [finalExperiment, queryHeight, virtualPass_height]
  | query j w next ih =>
    simp only [finalExperiment, queryHeight, ih]
    omega

/-- Virtual checking does not allow changing the selected residual. Every zero
row is recorded on that single fixed nonzero residual. -/
theorem final_zero_le_spoils (bank : J → I → F)
    (tree : QueryTree J (I → F) (I → F)) (hw : runOutput bank tree ≠ 0) :
    (univ.filter fun j => rowDot (runOutput bank tree) (bank j) = 0).card ≤
      AdaptiveTail.successes (markedExperiment []
        (finalExperiment univ.toList tree)) bank := by
  have hs : (univ.filter fun j => rowDot (runOutput bank tree) (bank j) = 0) ⊆
      spoiledRows (runObservations bank (finalExperiment univ.toList tree)) := by
    intro j hj
    have hz : rowTest (bank j) (runOutput bank tree) = true := by
      simp [rowTest, (mem_filter.mp hj).2]
    simp only [spoiledRows, mem_filter, mem_univ, true_and]
    refine ⟨⟨j,runOutput bank tree,true⟩, ?_, rfl, hw, rfl⟩
    rw [finalExperiment_observations]
    apply List.mem_append.mpr
    right
    apply List.mem_map.mpr
    exact ⟨j, by simp, by simp [hz]⟩
  have hc := card_le_card hs
  have he := spoiledRows_execution bank (finalExperiment univ.toList tree) []
  simpa [spoiledRows] using hc.trans_eq (by simpa [spoiledRows] using he)

#print axioms final_zero_le_spoils
end ProgressivePool
