import FamilyAlgebra.ConcretePlanes

namespace FamilyAlgebra
variable {E : Type*} [Field E]

theorem binarySum_congr (weight : Nat → E) (b c : Nat → Bool) (n : Nat)
    (h : ∀ k, k < n → b k = c k) : binarySum weight b n = binarySum weight c n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [binarySum, h n (by omega), ih (by intro k hk; exact h k (by omega))]

theorem binarySum_false (weight : Nat → E) (n : Nat) :
    binarySum weight (fun _ => false) n = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [binarySum, ih]

theorem binarySum_xor (two_zero : (2:E)=0) (weight : Nat → E)
    (b c : Nat → Bool) (n : Nat) :
    binarySum weight (fun k => b k ^^ c k) n = binarySum weight b n + binarySum weight c n := by
  induction n with
  | zero => simp [binarySum]
  | succ n ih =>
    have ht : (if b n ^^ c n then weight n else 0) =
        (if b n then weight n else 0) + (if c n then weight n else 0) := by
      cases b n <;> cases c n <;> simp [double_zero two_zero]
    simp only [binarySum, ih, ht]
    ac_rfl

def singletonBit (i : Nat) (b : Bool) : Nat → Bool := fun k => if k=i then b else false

theorem binarySum_single_out (weight : Nat → E) (i n : Nat) (b : Bool) (hn : n ≤ i) :
    binarySum weight (singletonBit i b) n = 0 := by
  rw [binarySum_congr weight _ (fun _ => false) n (by
    intro k hk
    simp [singletonBit, show ¬k=i by omega])]
  exact binarySum_false weight n

theorem binarySum_single (weight : Nat → E) (i n : Nat) (b : Bool) (hn : i < n) :
    binarySum weight (singletonBit i b) n = if b then weight i else 0 := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases hi : i=n
    · subst i
      simp [binarySum, binarySum_single_out weight n n b (by omega), singletonBit]
    · have hlt : i<n := by omega
      simp [binarySum, ih hlt, singletonBit, show ¬n=i by omega]

def termCoeff : List (Nat × Bool) → Nat → Bool
  | [], _ => false
  | p::ps, k => singletonBit p.1 p.2 k ^^ termCoeff ps k

def termValue (weight : Nat → E) (p : Nat × Bool) : E := if p.2 then weight p.1 else 0

theorem evaluate_terms (two_zero : (2:E)=0) (weight : Nat → E)
    (ts : List (Nat × Bool)) (n : Nat) (bounded : ∀ p ∈ ts, p.1 < n) :
    binarySum weight (termCoeff ts) n = Pfaffian.scalarSum (ts.map (termValue weight)) := by
  induction ts with
  | nil => simp [termCoeff, Pfaffian.scalarSum, binarySum_false]
  | cons p ps ih =>
    have hp := bounded p (by simp)
    have hs : ∀ p ∈ ps, p.1<n := by intro q hq; exact bounded q (by simp [hq])
    simp only [termCoeff, binarySum_xor two_zero, binarySum_single weight p.1 n p.2 hp,
      ih hs, List.map_cons, Pfaffian.scalarSum, termValue]

theorem termCoeff_false (ts : List (Nat × Bool)) (k : Nat)
    (h : ∀ p ∈ ts, p.1=k → p.2=false) : termCoeff ts k = false := by
  induction ts with
  | nil => rfl
  | cons p ps ih =>
    have ht : termCoeff ps k = false := ih (by intro q hq; exact h q (by simp [hq]))
    simp only [termCoeff, ht, Bool.xor_false, singletonBit]
    split
    · exact h p (by simp) (by omega)
    · rfl

#print axioms evaluate_terms
end FamilyAlgebra
