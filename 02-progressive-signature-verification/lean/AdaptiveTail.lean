import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Choose.Basic

/-!
# A finite adaptive marked-success tail bound

A deterministic binary decision tree may choose both the next observation and
whether its true branch counts as a success after seeing the entire history.
The root sample space is an arbitrary finite set.  Every child receives exactly
the samples consistent with its observed bit.  No independence of queries is
assumed.  A local conditional counting bound at marked nodes implies the usual
binomial union bound, including for trees with early stopping.
-/
namespace ProgressivePool.AdaptiveTail
open Finset Classical

variable {Ω : Type*}

/-- The observation and mark may vary from node to node, hence with history. -/
inductive Tree (Ω : Type*) where
  | leaf : Tree Ω
  | node (observe : Ω → Bool) (mark : Bool) (next : Bool → Tree Ω) : Tree Ω

/-- Number of marked true observations on the actual path of a sample. -/
def successes : Tree Ω → Ω → ℕ
  | .leaf, _ => 0
  | .node observe mark next, ω =>
      (if mark && observe ω then 1 else 0) + successes (next (observe ω)) ω

/-- A structural depth bound allows different branches to stop early. -/
def depthLE : ℕ → Tree Ω → Prop
  | _, .leaf => True
  | 0, .node _ _ _ => False
  | n + 1, .node _ _ next => ∀ b, depthLE n (next b)

/-- The exact sample cell after one observation. -/
noncomputable def childCell (S : Finset Ω) (observe : Ω → Bool) (b : Bool) : Finset Ω :=
  S.filter fun ω => observe ω = b

/-- Conditional success probability at most `1 / D`, in division-free form.
The condition on an empty cell is automatically satisfied. -/
def localBound (D : ℕ) (S : Finset Ω) : Tree Ω → Prop
  | .leaf => True
  | .node observe mark next =>
      (mark = true → D * (childCell S observe true).card ≤ S.card) ∧
      ∀ b, localBound D (childCell S observe b) (next b)

noncomputable def tailCount (S : Finset Ω) (tree : Tree Ω) (u : ℕ) : ℕ :=
  (S.filter fun ω => u ≤ successes tree ω).card

lemma child_cards (S : Finset Ω) (observe : Ω → Bool) :
    (childCell S observe false).card + (childCell S observe true).card = S.card := by
  simpa [childCell] using
    (filter_card_add_filter_neg_card_eq_card (s := S) (fun ω => observe ω = false))

lemma partition_count (S : Finset Ω) (observe : Ω → Bool) (P : Ω → Prop) [DecidablePred P] :
    (S.filter P).card =
      ((childCell S observe false).filter P).card +
      ((childCell S observe true).filter P).card := by
  classical
  simpa [childCell, filter_filter, and_comm] using
    (filter_card_add_filter_neg_card_eq_card (s := S.filter P) (fun ω => observe ω = false)).symm

lemma tail_node_unmarked (S : Finset Ω) (observe : Ω → Bool)
    (next : Bool → Tree Ω) (u : ℕ) :
    tailCount S (.node observe false next) u =
      tailCount (childCell S observe false) (next false) u +
      tailCount (childCell S observe true) (next true) u := by
  classical
  unfold tailCount
  rw [partition_count S observe (fun ω => u ≤ successes (.node observe false next) ω)]
  congr 1 <;> congr 1 <;> ext ω <;>
    simp only [mem_filter, childCell, tailCount, mem_filter] <;>
    constructor <;> rintro ⟨⟨hS, hb⟩, hs⟩ <;>
    exact ⟨⟨hS, hb⟩, by simpa [successes, hb] using hs⟩

lemma tail_node_marked (S : Finset Ω) (observe : Ω → Bool)
    (next : Bool → Tree Ω) (u : ℕ) :
    tailCount S (.node observe true next) (u + 1) =
      tailCount (childCell S observe false) (next false) (u + 1) +
      tailCount (childCell S observe true) (next true) u := by
  classical
  unfold tailCount
  rw [partition_count S observe (fun ω => u + 1 ≤ successes (.node observe true next) ω)]
  congr 1 <;> congr 1 <;> ext ω <;>
    simp only [mem_filter, childCell, tailCount, mem_filter] <;>
    constructor <;> rintro ⟨⟨hS, hb⟩, hs⟩ <;>
    exact ⟨⟨hS, hb⟩, by simpa [successes, hb, Nat.add_comm 1] using hs⟩

/-- Adaptive binomial tail bound on any finite uniform sample cell.
This is an exact natural-number inequality and requires no positivity hypotheses
or probability-space infrastructure. -/
theorem marked_tail_bound (D N u : ℕ) (S : Finset Ω) (tree : Tree Ω)
    (hdepth : depthLE N tree) (hlocal : localBound D S tree) :
    D ^ u * tailCount S tree u ≤ N.choose u * S.card := by
  induction N generalizing S tree u with
  | zero =>
      cases tree with
      | leaf => cases u <;> simp [tailCount, successes]
      | node observe mark next => exact False.elim hdepth
  | succ n ih =>
      cases tree with
      | leaf => cases u <;> simp [tailCount, successes]
      | node observe mark next =>
          cases u with
          | zero => simp [tailCount]
          | succ u =>
              have h0 := ih (u + 1) (childCell S observe false) (next false)
                (hdepth false) (hlocal.2 false)
              cases mark with
              | false =>
                  have h1 := ih (u + 1) (childCell S observe true) (next true)
                    (hdepth true) (hlocal.2 true)
                  rw [tail_node_unmarked, Nat.mul_add]
                  calc
                    _ ≤ n.choose (u + 1) * (childCell S observe false).card +
                        n.choose (u + 1) * (childCell S observe true).card :=
                      Nat.add_le_add h0 h1
                    _ = n.choose (u + 1) * S.card := by rw [← Nat.mul_add, child_cards]
                    _ ≤ (n + 1).choose (u + 1) * S.card :=
                      Nat.mul_le_mul_right _ (Nat.choose_le_succ n (u + 1))
              | true =>
                  have h1 := ih u (childCell S observe true) (next true)
                    (hdepth true) (hlocal.2 true)
                  have hbranch := hlocal.1 rfl
                  have hc0 : (childCell S observe false).card ≤ S.card := by
                    exact card_le_card (filter_subset _ _)
                  rw [tail_node_marked, Nat.mul_add]
                  calc
                    _ ≤ n.choose (u + 1) * (childCell S observe false).card +
                        D * (n.choose u * (childCell S observe true).card) := by
                      exact Nat.add_le_add h0 (by
                        simpa [Nat.pow_succ, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
                          using Nat.mul_le_mul_left D h1)
                    _ ≤ n.choose (u + 1) * S.card + n.choose u * S.card := by
                      apply Nat.add_le_add (Nat.mul_le_mul_left _ hc0)
                      simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
                        using Nat.mul_le_mul_left (n.choose u) hbranch
                    _ = (n + 1).choose (u + 1) * S.card := by
                      rw [Nat.choose_succ_succ, Nat.add_mul, Nat.add_comm]

/-- Any event forcing at least `u` marked successes inherits the same bound.
This form lets a concrete experiment use a separate deterministic implication
from its terminal bad event to the marked-success count. -/
theorem marked_event_bound (D N u : ℕ) (S E : Finset Ω) (tree : Tree Ω)
    (hdepth : depthLE N tree) (hlocal : localBound D S tree)
    (hsub : E ⊆ S) (hcount : ∀ ω ∈ E, u ≤ successes tree ω) :
    D ^ u * E.card ≤ N.choose u * S.card := by
  have hc : E.card ≤ tailCount S tree u := by
    apply card_le_card
    intro ω hω
    exact mem_filter.mpr ⟨hsub hω, hcount ω hω⟩
  exact (Nat.mul_le_mul_left (D ^ u) hc).trans
    (marked_tail_bound D N u S tree hdepth hlocal)

#print axioms marked_tail_bound
#print axioms marked_event_bound
end ProgressivePool.AdaptiveTail
