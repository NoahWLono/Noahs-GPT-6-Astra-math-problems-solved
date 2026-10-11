import CanonicalMatrix
import Std.Tactic.BVDecide
import Mathlib.Tactic.FinCases

set_option autoImplicit false

namespace GPT6Astra

def prefixB (x y : Fin 10 → Bool) (c : Fin 10) : Bool :=
  (decide (c ≤ 0) || (x 0 == y 0)) &&
  (decide (c ≤ 1) || (x 1 == y 1)) &&
  (decide (c ≤ 2) || (x 2 == y 2)) &&
  (decide (c ≤ 3) || (x 3 == y 3)) &&
  (decide (c ≤ 4) || (x 4 == y 4)) &&
  (decide (c ≤ 5) || (x 5 == y 5)) &&
  (decide (c ≤ 6) || (x 6 == y 6)) &&
  (decide (c ≤ 7) || (x 7 == y 7)) &&
  (decide (c ≤ 8) || (x 8 == y 8)) &&
  (decide (c ≤ 9) || (x 9 == y 9))

private theorem forall_fin10_iff (P : Fin 10 → Prop) :
    (∀ d, P d) ↔ P 0 ∧ P 1 ∧ P 2 ∧ P 3 ∧ P 4 ∧ P 5 ∧ P 6 ∧ P 7 ∧ P 8 ∧ P 9 := by
  constructor
  · intro h
    exact ⟨h 0, h 1, h 2, h 3, h 4, h 5, h 6, h 7, h 8, h 9⟩
  · rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ d
    fin_cases d <;> assumption

private theorem prefix_entry_iff (x y : Fin 10 → Bool) (c d : Fin 10) :
    (decide (c ≤ d) || (x d == y d)) = true ↔ (d < c → x d = y d) := by
  simp only [Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq]
  constructor
  · rintro (hcd | heq) hdc
    · exact False.elim (not_le_of_gt hdc hcd)
    · exact heq
  · intro h
    by_cases hcd : c ≤ d
    · exact Or.inl hcd
    · exact Or.inr (h (lt_of_not_ge hcd))

theorem prefixB_eq_true_iff (x y : Fin 10 → Bool) (c : Fin 10) :
    prefixB x y c = true ↔ ∀ d, d < c → x d = y d := by
  rw [forall_fin10_iff]
  simp only [prefixB, Bool.and_eq_true, prefix_entry_iff, and_assoc]

def rowLexClause (A : BinaryMatrix 10) (i j c : Fin 10) : Bool :=
  (!(prefixB (A i) (A j) c)) || (!(A i c)) || A j c

private theorem bool_lex_clause (p x y : Bool) (h : p = true → x ≤ y) :
    ((!p) || (!x) || y) = true := by
  cases p <;> cases x <;> cases y <;> simp_all [Bool.le_iff_imp]

theorem rowLexClause_of_doubleLexRows (A : BinaryMatrix 10)
    (hrows : DoubleLexRows A) (i j c : Fin 10) (hi : 0 < i) (hij : i < j) :
    rowLexClause A i j c = true := by
  apply bool_lex_clause
  intro hp
  exact hrows i j hi hij c ((prefixB_eq_true_iff (A i) (A j) c).1 hp)

def columnPrefixB (A : BinaryMatrix 10) (c d r : Fin 10) : Bool :=
  (decide (r ≤ 1) || (A 1 c == A 1 d)) &&
  (decide (r ≤ 2) || (A 2 c == A 2 d)) &&
  (decide (r ≤ 3) || (A 3 c == A 3 d)) &&
  (decide (r ≤ 4) || (A 4 c == A 4 d)) &&
  (decide (r ≤ 5) || (A 5 c == A 5 d)) &&
  (decide (r ≤ 6) || (A 6 c == A 6 d)) &&
  (decide (r ≤ 7) || (A 7 c == A 7 d)) &&
  (decide (r ≤ 8) || (A 8 c == A 8 d)) &&
  (decide (r ≤ 9) || (A 9 c == A 9 d))

theorem columnPrefixB_eq_true_iff (A : BinaryMatrix 10) (c d r : Fin 10) :
    columnPrefixB A c d r = true ↔ ∀ s, 0 < s → s < r → A s c = A s d := by
  rw [forall_fin10_iff]
  simp only [columnPrefixB, Bool.and_eq_true]
  have h (s : Fin 10) := prefix_entry_iff (fun t => A t c) (fun t => A t d) r s
  simp only [h]
  simp [and_assoc]

def columnLexClause (A : BinaryMatrix 10) (c d r : Fin 10) : Bool :=
  (!(columnPrefixB A c d r)) || (!(A r c)) || A r d

theorem columnLexClause_of_doubleLexAnchoredColumns (A : BinaryMatrix 10) (k : Nat)
    (hcols : DoubleLexAnchoredColumns A k) (c d r : Fin 10)
    (hc : 0 < c) (hcd : c < d) (hpart : c.val < k ↔ d.val < k) (hr : 0 < r) :
    columnLexClause A c d r = true := by
  apply bool_lex_clause
  intro hp
  exact hcols c d hc hcd hpart r hr ((columnPrefixB_eq_true_iff A c d r).1 hp)

end GPT6Astra

#print axioms GPT6Astra.rowLexClause_of_doubleLexRows
#print axioms GPT6Astra.columnLexClause_of_doubleLexAnchoredColumns
