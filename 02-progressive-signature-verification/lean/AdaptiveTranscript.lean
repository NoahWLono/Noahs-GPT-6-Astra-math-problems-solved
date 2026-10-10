import RowExclusions
import Mathlib.Data.Fintype.BigOperators

/-! An actual deterministic adaptive row/bit-query experiment. Fixing independent
external randomness selects one such tree; no independence of adaptive queries
is assumed. -/
namespace ProgressivePool

inductive QueryTree (J X Y : Type*) where
  | leaf : Y → QueryTree J X Y
  | query : J → X → (Bool → QueryTree J X Y) → QueryTree J X Y

structure Observation (J X : Type*) where
  row : J
  input : X
  answer : Bool

variable {J X Y K : Type*}

def runBits (test : K → X → Bool) (bank : J → K) :
    QueryTree J X Y → List Bool
  | .leaf _ => []
  | .query j x next =>
    let b := test (bank j) x
    b :: runBits test bank (next b)

def pathValid : QueryTree J X Y → List Bool → Prop
  | .leaf _, bs => bs = []
  | .query _ _ _, [] => False
  | .query _ _ next, b :: bs => pathValid (next b) bs

def pathObservations : QueryTree J X Y → List Bool → List (Observation J X)
  | .leaf _, _ => []
  | .query _ _ _, [] => []
  | .query j x next, b :: bs => ⟨j,x,b⟩ :: pathObservations (next b) bs

def rowCompatible (test : K → X → Bool) (obs : List (Observation J X))
    (j : J) (key : K) : Prop :=
  ∀ o ∈ obs, o.row = j → test key o.input = o.answer

theorem actual_transcript_factorization (test : K → X → Bool) (bank : J → K)
    (tree : QueryTree J X Y) (bs : List Bool) :
    runBits test bank tree = bs ↔
      pathValid tree bs ∧ ∀ j, rowCompatible test (pathObservations tree bs) j (bank j) := by
  induction tree generalizing bs with
  | leaf y => simp [runBits, pathValid, pathObservations, rowCompatible]
  | query j x next ih =>
    cases bs with
    | nil => simp [runBits, pathValid]
    | cons b bs =>
      simp only [runBits, List.cons.injEq]
      constructor
      · rintro ⟨hb, hr⟩
        rw [hb] at hr
        obtain ⟨hv, hc⟩ := (ih b bs).mp hr
        refine ⟨hv, ?_⟩
        intro j' o ho he
        simp only [pathObservations, List.mem_cons] at ho
        rcases ho with rfl | ho
        · change j = j' at he
          subst j'
          exact hb
        · exact hc j' o ho he
      · rintro ⟨hv, hc⟩
        have hb : test (bank j) x = b :=
          hc j ⟨j,x,b⟩ (by simp [pathObservations]) rfl
        refine ⟨hb, ?_⟩
        rw [hb]
        apply (ih b bs).mpr
        refine ⟨hv, ?_⟩
        intro j' o ho he
        exact hc j' o (by simp [pathObservations, ho]) he

open Finset
open Classical

/-- The actual transcript cell is exactly a rectangular product, not an assumed
independence property of the adversary. -/
theorem actual_transcript_cell [Fintype J] [Fintype K]
    (test : K → X → Bool) (tree : QueryTree J X Y) (bs : List Bool)
    (hv : pathValid tree bs) :
    (univ.filter fun bank : J → K => runBits test bank tree = bs) =
      Fintype.piFinset (fun j => univ.filter
        (rowCompatible test (pathObservations tree bs) j)) := by
  classical
  ext bank
  simp only [mem_filter, mem_univ, true_and, Fintype.mem_piFinset]
  exact (actual_transcript_factorization test bank tree bs).trans
    (and_iff_right hv)

/-- Exact size of an adaptive transcript cell. -/
theorem actual_transcript_card [Fintype J] [Fintype K]
    (test : K → X → Bool) (tree : QueryTree J X Y) (bs : List Bool)
    (hv : pathValid tree bs) :
    (univ.filter fun bank : J → K => runBits test bank tree = bs).card =
      ∏ j, (univ.filter (rowCompatible test (pathObservations tree bs) j)).card := by
  classical
  rw [actual_transcript_cell test tree bs hv, Fintype.card_piFinset]

#print axioms actual_transcript_card
#print axioms actual_transcript_factorization
end ProgressivePool
