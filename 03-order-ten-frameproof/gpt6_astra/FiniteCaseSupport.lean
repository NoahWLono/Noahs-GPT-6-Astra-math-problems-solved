import MatrixStructure
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases
import Std.Tactic.BVDecide

set_option autoImplicit false

namespace GPT6Astra

theorem xor_true_iff_ne (a b : Bool) : (a ^^ b) = true ↔ a ≠ b := by
  cases a <;> cases b <;> decide

/-- The Boolean form of a single separation witness. -/
def separatesB (A : BinaryMatrix 10) (r a b c d : Fin 10) : Bool :=
  (A r a ^^ A r b) && (A r a ^^ A r c) && (A r a ^^ A r d)

theorem separatesB_eq_true (A : BinaryMatrix 10) (r a b c d : Fin 10) :
    separatesB A r a b c d = true ↔ Separates A r a b c d := by
  simp [separatesB, Separates, and_assoc]

/-- Ten potential witnesses for a fixed designated column and coalition. -/
def separationClause (A : BinaryMatrix 10) (a b c d : Fin 10) : Bool :=
  separatesB A 0 a b c d || separatesB A 1 a b c d ||
  separatesB A 2 a b c d || separatesB A 3 a b c d ||
  separatesB A 4 a b c d || separatesB A 5 a b c d ||
  separatesB A 6 a b c d || separatesB A 7 a b c d ||
  separatesB A 8 a b c d || separatesB A 9 a b c d

theorem separationClause_of_isSHF (A : BinaryMatrix 10) (h : IsSHF A)
    (a b c d : Fin 10) (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    separationClause A a b c d = true := by
  obtain ⟨r, hr⟩ := h a b c d hab hac had hbc hbd hcd
  have hb := (separatesB_eq_true A r a b c d).2 hr
  fin_cases r <;> dsimp at hb <;> simp_all [separationClause]

/-- A Boolean pair witness. -/
def separatesPairB (A : BinaryMatrix 10) (r a b c : Fin 10) : Bool :=
  (A r a ^^ A r b) && (A r a ^^ A r c)

theorem separatesPairB_eq_true (A : BinaryMatrix 10) (r a b c : Fin 10) :
    separatesPairB A r a b c = true ↔ SeparatesPair A r a b c := by
  simp [separatesPairB, SeparatesPair]

/-- A Boolean private bit, expressed without a finite quantifier. -/
def privateB (A : BinaryMatrix 10) (r a : Fin 10) : Bool :=
  ((a == 0) || (A r a ^^ A r 0)) &&
  ((a == 1) || (A r a ^^ A r 1)) &&
  ((a == 2) || (A r a ^^ A r 2)) &&
  ((a == 3) || (A r a ^^ A r 3)) &&
  ((a == 4) || (A r a ^^ A r 4)) &&
  ((a == 5) || (A r a ^^ A r 5)) &&
  ((a == 6) || (A r a ^^ A r 6)) &&
  ((a == 7) || (A r a ^^ A r 7)) &&
  ((a == 8) || (A r a ^^ A r 8)) &&
  ((a == 9) || (A r a ^^ A r 9))

theorem privateB_of_privateAt (A : BinaryMatrix 10) (r a : Fin 10)
    (h : PrivateAt A r a) : privateB A r a = true := by
  have h' (b : Fin 10) : a = b ∨ A r a ≠ A r b := by
    by_cases hab : a = b
    · exact Or.inl hab
    · exact Or.inr (Ne.symm (h b (Ne.symm hab)))
  simp only [privateB, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq,
    xor_true_iff_ne]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨h' 0, h' 1⟩, h' 2⟩, h' 3⟩, h' 4⟩, h' 5⟩,
    h' 6⟩, h' 7⟩, h' 8⟩, h' 9⟩

def hasPrivateB (A : BinaryMatrix 10) (a : Fin 10) : Bool :=
  privateB A 0 a || privateB A 1 a || privateB A 2 a || privateB A 3 a ||
  privateB A 4 a || privateB A 5 a || privateB A 6 a || privateB A 7 a ||
  privateB A 8 a || privateB A 9 a

theorem hasPrivateB_of_exists (A : BinaryMatrix 10) (a : Fin 10)
    (h : ∃ r, PrivateAt A r a) : hasPrivateB A a = true := by
  obtain ⟨r, hr⟩ := h
  have hb := privateB_of_privateAt A r a hr
  fin_cases r <;> dsimp at hb <;> simp_all [hasPrivateB]

def pairWithoutB (A : BinaryMatrix 10) (a b c omitted : Fin 10) : Bool :=
  ((omitted != 0) && separatesPairB A 0 a b c) ||
  ((omitted != 1) && separatesPairB A 1 a b c) ||
  ((omitted != 2) && separatesPairB A 2 a b c) ||
  ((omitted != 3) && separatesPairB A 3 a b c) ||
  ((omitted != 4) && separatesPairB A 4 a b c) ||
  ((omitted != 5) && separatesPairB A 5 a b c) ||
  ((omitted != 6) && separatesPairB A 6 a b c) ||
  ((omitted != 7) && separatesPairB A 7 a b c) ||
  ((omitted != 8) && separatesPairB A 8 a b c) ||
  ((omitted != 9) && separatesPairB A 9 a b c)

theorem pairWithoutB_of_exists (A : BinaryMatrix 10) (a b c omitted : Fin 10)
    (h : ∃ r, r ≠ omitted ∧ SeparatesPair A r a b c) :
    pairWithoutB A a b c omitted = true := by
  obtain ⟨r, hr, hsep⟩ := h
  have hb := (separatesPairB_eq_true A r a b c).2 hsep
  have hne := Ne.symm hr
  fin_cases r <;> dsimp at hb hne <;> simp_all [pairWithoutB]

/-- The auxiliary pair clauses are consequences of the original SHF property. -/
theorem conditionalPair_of_isSHF (A : BinaryMatrix 10) (h : IsSHF A)
    (a b c omitted : Fin 10) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    (hasPrivateB A a || pairWithoutB A a b c omitted) = true := by
  classical
  by_cases hp : ∃ r, PrivateAt A r a
  · simp [hasPrivateB_of_exists A a hp]
  · have hn : NoPrivateAt A a := by simpa [NoPrivateAt] using hp
    obtain ⟨r, s, hrs, hr, hs⟩ :=
      two_rows_separate_pair_of_noPrivateAt A h a b c hn hab hac hbc
    have he : ∃ t, t ≠ omitted ∧ SeparatesPair A t a b c := by
      by_cases hro : r = omitted
      · exact ⟨s, fun hso => hrs (hro.trans hso.symm), hs⟩
      · exact ⟨r, hro, hr⟩
    simp [pairWithoutB_of_exists A a b c omitted he]

end GPT6Astra

#print axioms GPT6Astra.conditionalPair_of_isSHF
