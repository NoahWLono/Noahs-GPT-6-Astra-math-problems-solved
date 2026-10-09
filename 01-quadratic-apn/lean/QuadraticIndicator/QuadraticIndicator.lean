import Std

/-! A self-contained, axiom-free first stage of the quadratic-component indicator bridge.
This file proves a degree-four polynomial representation of the perfect-matching
candidate. It does NOT identify the candidate with non-bentness. -/
namespace QuadraticIndicator

inductive Polynomial (n : Nat) where
  | const : Bool → Polynomial n
  | variable : Fin n → Polynomial n
  | add : Polynomial n → Polynomial n → Polynomial n
  | mul : Polynomial n → Polynomial n → Polynomial n

def Polynomial.eval (b : Fin n → Bool) : Polynomial n → Bool
  | .const c => c
  | .variable i => b i
  | .add p q => p.eval b ^^ q.eval b
  | .mul p q => p.eval b && q.eval b

def Polynomial.degreeBound : Polynomial n → Nat
  | .const _ => 0
  | .variable _ => 1
  | .add p q => max p.degreeBound q.degreeBound
  | .mul p q => p.degreeBound + q.degreeBound

/-- Degree is expressed by an actual representing polynomial, not an assumed
property of an unrelated numerical indicator. This upper bound is sufficient
for the usual squarefree Boolean algebraic degree. -/
def HasPolynomialDegreeLE (f : (Fin n → Bool) → Bool) (d : Nat) : Prop :=
  ∃ p : Polynomial n, p.degreeBound ≤ d ∧ ∀ b, p.eval b = f b

def polynomialSum : List (Polynomial n) → Polynomial n
  | [] => .const false
  | p :: ps => .add p (polynomialSum ps)

def xorSum : List Bool → Bool
  | [] => false
  | b :: bs => b ^^ xorSum bs

theorem eval_polynomialSum (ps : List (Polynomial n)) (b : Fin n → Bool) :
    (polynomialSum ps).eval b = xorSum (ps.map (Polynomial.eval b)) := by
  induction ps with
  | nil => rfl
  | cons p ps ih => simp only [polynomialSum, Polynomial.eval, List.map_cons, xorSum, ih]

theorem degree_polynomialSum (ps : List (Polynomial n)) (d : Nat)
    (h : ∀ p ∈ ps, p.degreeBound ≤ d) :
    (polynomialSum ps).degreeBound ≤ d := by
  induction ps with
  | nil => simp [polynomialSum, Polynomial.degreeBound]
  | cons p ps ih =>
    simp only [polynomialSum, Polynomial.degreeBound]
    exact Nat.max_le.mpr ⟨h p (by simp), ih (by intro q hq; exact h q (by simp [hq]))⟩

def linearPolynomial (c : Fin n → Bool) : Polynomial n :=
  polynomialSum ((List.finRange n).map fun i => .mul (.const (c i)) (.variable i))

def dot (b c : Fin n → Bool) : Bool :=
  xorSum ((List.finRange n).map fun i => c i && b i)

theorem eval_linearPolynomial (c b : Fin n → Bool) :
    (linearPolynomial c).eval b = dot b c := by
  simp only [linearPolynomial, eval_polynomialSum, List.map_map, Function.comp_def, Polynomial.eval, dot]

theorem degree_linearPolynomial (c : Fin n → Bool) :
    (linearPolynomial c).degreeBound ≤ 1 := by
  apply degree_polynomialSum
  intro p hp
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp hp
  simp [Polynomial.degreeBound]

abbrev Edge := Fin 8 × Fin 8
abbrev Matching := Edge × Edge × Edge × Edge

def matchingPolynomial (c : Fin 8 → Fin 8 → Fin 8 → Bool)
    (m : Matching) : Polynomial 8 :=
  .mul (.mul (linearPolynomial (c m.1.1 m.1.2))
             (linearPolynomial (c m.2.1.1 m.2.1.2)))
       (.mul (linearPolynomial (c m.2.2.1.1 m.2.2.1.2))
             (linearPolynomial (c m.2.2.2.1 m.2.2.2.2)))

theorem degree_matchingPolynomial (c : Fin 8 → Fin 8 → Fin 8 → Bool) (m : Matching) :
    (matchingPolynomial c m).degreeBound ≤ 4 := by
  have h1 := degree_linearPolynomial (c m.1.1 m.1.2)
  have h2 := degree_linearPolynomial (c m.2.1.1 m.2.1.2)
  have h3 := degree_linearPolynomial (c m.2.2.1.1 m.2.2.1.2)
  have h4 := degree_linearPolynomial (c m.2.2.2.1 m.2.2.2.2)
  simp only [matchingPolynomial, Polynomial.degreeBound]
  omega

/-- All 105 canonical perfect matchings of eight coordinates. -/
def matchings : List Matching := [
  ((0, 1), (2, 3), (4, 5), (6, 7)),
  ((0, 1), (2, 3), (4, 6), (5, 7)),
  ((0, 1), (2, 3), (4, 7), (5, 6)),
  ((0, 1), (2, 4), (3, 5), (6, 7)),
  ((0, 1), (2, 4), (3, 6), (5, 7)),
  ((0, 1), (2, 4), (3, 7), (5, 6)),
  ((0, 1), (2, 5), (3, 4), (6, 7)),
  ((0, 1), (2, 5), (3, 6), (4, 7)),
  ((0, 1), (2, 5), (3, 7), (4, 6)),
  ((0, 1), (2, 6), (3, 4), (5, 7)),
  ((0, 1), (2, 6), (3, 5), (4, 7)),
  ((0, 1), (2, 6), (3, 7), (4, 5)),
  ((0, 1), (2, 7), (3, 4), (5, 6)),
  ((0, 1), (2, 7), (3, 5), (4, 6)),
  ((0, 1), (2, 7), (3, 6), (4, 5)),
  ((0, 2), (1, 3), (4, 5), (6, 7)),
  ((0, 2), (1, 3), (4, 6), (5, 7)),
  ((0, 2), (1, 3), (4, 7), (5, 6)),
  ((0, 2), (1, 4), (3, 5), (6, 7)),
  ((0, 2), (1, 4), (3, 6), (5, 7)),
  ((0, 2), (1, 4), (3, 7), (5, 6)),
  ((0, 2), (1, 5), (3, 4), (6, 7)),
  ((0, 2), (1, 5), (3, 6), (4, 7)),
  ((0, 2), (1, 5), (3, 7), (4, 6)),
  ((0, 2), (1, 6), (3, 4), (5, 7)),
  ((0, 2), (1, 6), (3, 5), (4, 7)),
  ((0, 2), (1, 6), (3, 7), (4, 5)),
  ((0, 2), (1, 7), (3, 4), (5, 6)),
  ((0, 2), (1, 7), (3, 5), (4, 6)),
  ((0, 2), (1, 7), (3, 6), (4, 5)),
  ((0, 3), (1, 2), (4, 5), (6, 7)),
  ((0, 3), (1, 2), (4, 6), (5, 7)),
  ((0, 3), (1, 2), (4, 7), (5, 6)),
  ((0, 3), (1, 4), (2, 5), (6, 7)),
  ((0, 3), (1, 4), (2, 6), (5, 7)),
  ((0, 3), (1, 4), (2, 7), (5, 6)),
  ((0, 3), (1, 5), (2, 4), (6, 7)),
  ((0, 3), (1, 5), (2, 6), (4, 7)),
  ((0, 3), (1, 5), (2, 7), (4, 6)),
  ((0, 3), (1, 6), (2, 4), (5, 7)),
  ((0, 3), (1, 6), (2, 5), (4, 7)),
  ((0, 3), (1, 6), (2, 7), (4, 5)),
  ((0, 3), (1, 7), (2, 4), (5, 6)),
  ((0, 3), (1, 7), (2, 5), (4, 6)),
  ((0, 3), (1, 7), (2, 6), (4, 5)),
  ((0, 4), (1, 2), (3, 5), (6, 7)),
  ((0, 4), (1, 2), (3, 6), (5, 7)),
  ((0, 4), (1, 2), (3, 7), (5, 6)),
  ((0, 4), (1, 3), (2, 5), (6, 7)),
  ((0, 4), (1, 3), (2, 6), (5, 7)),
  ((0, 4), (1, 3), (2, 7), (5, 6)),
  ((0, 4), (1, 5), (2, 3), (6, 7)),
  ((0, 4), (1, 5), (2, 6), (3, 7)),
  ((0, 4), (1, 5), (2, 7), (3, 6)),
  ((0, 4), (1, 6), (2, 3), (5, 7)),
  ((0, 4), (1, 6), (2, 5), (3, 7)),
  ((0, 4), (1, 6), (2, 7), (3, 5)),
  ((0, 4), (1, 7), (2, 3), (5, 6)),
  ((0, 4), (1, 7), (2, 5), (3, 6)),
  ((0, 4), (1, 7), (2, 6), (3, 5)),
  ((0, 5), (1, 2), (3, 4), (6, 7)),
  ((0, 5), (1, 2), (3, 6), (4, 7)),
  ((0, 5), (1, 2), (3, 7), (4, 6)),
  ((0, 5), (1, 3), (2, 4), (6, 7)),
  ((0, 5), (1, 3), (2, 6), (4, 7)),
  ((0, 5), (1, 3), (2, 7), (4, 6)),
  ((0, 5), (1, 4), (2, 3), (6, 7)),
  ((0, 5), (1, 4), (2, 6), (3, 7)),
  ((0, 5), (1, 4), (2, 7), (3, 6)),
  ((0, 5), (1, 6), (2, 3), (4, 7)),
  ((0, 5), (1, 6), (2, 4), (3, 7)),
  ((0, 5), (1, 6), (2, 7), (3, 4)),
  ((0, 5), (1, 7), (2, 3), (4, 6)),
  ((0, 5), (1, 7), (2, 4), (3, 6)),
  ((0, 5), (1, 7), (2, 6), (3, 4)),
  ((0, 6), (1, 2), (3, 4), (5, 7)),
  ((0, 6), (1, 2), (3, 5), (4, 7)),
  ((0, 6), (1, 2), (3, 7), (4, 5)),
  ((0, 6), (1, 3), (2, 4), (5, 7)),
  ((0, 6), (1, 3), (2, 5), (4, 7)),
  ((0, 6), (1, 3), (2, 7), (4, 5)),
  ((0, 6), (1, 4), (2, 3), (5, 7)),
  ((0, 6), (1, 4), (2, 5), (3, 7)),
  ((0, 6), (1, 4), (2, 7), (3, 5)),
  ((0, 6), (1, 5), (2, 3), (4, 7)),
  ((0, 6), (1, 5), (2, 4), (3, 7)),
  ((0, 6), (1, 5), (2, 7), (3, 4)),
  ((0, 6), (1, 7), (2, 3), (4, 5)),
  ((0, 6), (1, 7), (2, 4), (3, 5)),
  ((0, 6), (1, 7), (2, 5), (3, 4)),
  ((0, 7), (1, 2), (3, 4), (5, 6)),
  ((0, 7), (1, 2), (3, 5), (4, 6)),
  ((0, 7), (1, 2), (3, 6), (4, 5)),
  ((0, 7), (1, 3), (2, 4), (5, 6)),
  ((0, 7), (1, 3), (2, 5), (4, 6)),
  ((0, 7), (1, 3), (2, 6), (4, 5)),
  ((0, 7), (1, 4), (2, 3), (5, 6)),
  ((0, 7), (1, 4), (2, 5), (3, 6)),
  ((0, 7), (1, 4), (2, 6), (3, 5)),
  ((0, 7), (1, 5), (2, 3), (4, 6)),
  ((0, 7), (1, 5), (2, 4), (3, 6)),
  ((0, 7), (1, 5), (2, 6), (3, 4)),
  ((0, 7), (1, 6), (2, 3), (4, 5)),
  ((0, 7), (1, 6), (2, 4), (3, 5)),
  ((0, 7), (1, 6), (2, 5), (3, 4))
]

theorem matchings_length : matchings.length = 105 := by decide

def matchingVertices (m : Matching) : List (Fin 8) :=
  [m.1.1, m.1.2, m.2.1.1, m.2.1.2, m.2.2.1.1, m.2.2.1.2, m.2.2.2.1, m.2.2.2.2]

theorem matchings_valid_check :
    matchings.all (fun m => decide (matchingVertices m).Nodup) = true := by decide

theorem every_matching_valid :
    ∀ m ∈ matchings, (matchingVertices m).Nodup := by
  intro m hm
  have h := List.all_eq_true.mp matchings_valid_check m hm
  exact of_decide_eq_true h


def pfaffianPolynomial (c : Fin 8 → Fin 8 → Fin 8 → Bool) : Polynomial 8 :=
  polynomialSum (matchings.map (matchingPolynomial c))

def matchingValue (A : Fin 8 → Fin 8 → Bool) (m : Matching) : Bool :=
  (A m.1.1 m.1.2 && A m.2.1.1 m.2.1.2) &&
  (A m.2.2.1.1 m.2.2.1.2 && A m.2.2.2.1 m.2.2.2.2)

def pfaffianValue (A : Fin 8 → Fin 8 → Bool) : Bool :=
  xorSum (matchings.map (matchingValue A))

theorem eval_pfaffianPolynomial (c : Fin 8 → Fin 8 → Fin 8 → Bool) (b : Fin 8 → Bool) :
    (pfaffianPolynomial c).eval b = pfaffianValue (fun i j => dot b (c i j)) := by
  simp only [pfaffianPolynomial, eval_polynomialSum, List.map_map, Function.comp_def,
    matchingPolynomial, Polynomial.eval, eval_linearPolynomial, pfaffianValue, matchingValue]
  rfl

theorem degree_pfaffianPolynomial (c : Fin 8 → Fin 8 → Fin 8 → Bool) :
    (pfaffianPolynomial c).degreeBound ≤ 4 := by
  apply degree_polynomialSum
  intro p hp
  obtain ⟨m, _, rfl⟩ := List.mem_map.mp hp
  exact degree_matchingPolynomial c m

def indicatorCandidatePolynomial (c : Fin 8 → Fin 8 → Fin 8 → Bool) : Polynomial 8 :=
  .add (.const true) (pfaffianPolynomial c)

theorem candidate_has_degree_le_four (c : Fin 8 → Fin 8 → Fin 8 → Bool) :
    HasPolynomialDegreeLE (fun b => true ^^ pfaffianValue (fun i j => dot b (c i j))) 4 := by
  refine ⟨indicatorCandidatePolynomial c, ?_, ?_⟩
  · simp only [indicatorCandidatePolynomial, Polynomial.degreeBound]
    exact Nat.max_le.mpr ⟨by decide, degree_pfaffianPolynomial c⟩
  · intro b
    simp only [indicatorCandidatePolynomial, Polynomial.eval, eval_pfaffianPolynomial]


theorem xor_interchange (a b c d : Bool) :
    ((a ^^ b) ^^ (c ^^ d)) = ((a ^^ c) ^^ (b ^^ d)) := by
  cases a <;> cases b <;> cases c <;> cases d <;> rfl

theorem xorSum_map_xor {α : Type} (xs : List α) (f g : α → Bool) :
    xorSum (xs.map fun x => f x ^^ g x) = (xorSum (xs.map f) ^^ xorSum (xs.map g)) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map_cons, xorSum, ih]
    exact xor_interchange _ _ _ _

theorem dot_xor (b c d : Fin n → Bool) :
    dot b (fun i => c i ^^ d i) = (dot b c ^^ dot b d) := by
  simp only [dot, Bool.and_xor_distrib_right]
  exact xorSum_map_xor _ _ _

abbrev Vector := Fin 8 → Bool

def vectorXor (x y : Vector) : Vector := fun i => x i ^^ y i

def unitVector (i : Fin 8) : Vector := fun j => decide (j = i)

def component (F : Vector → Vector) (b : Vector) (x : Vector) : Bool := dot b (F x)

def polarEntry (q : Vector → Bool) (i j : Fin 8) : Bool :=
  ((q (vectorXor (unitVector i) (unitVector j)) ^^ q (unitVector i)) ^^
    q (unitVector j)) ^^ q (fun _ => false)

/-- These are entries of the actual component polar matrix, computed from F. -/
def polarCoefficients (F : Vector → Vector) (i j : Fin 8) : Vector := fun l =>
  ((F (vectorXor (unitVector i) (unitVector j)) l ^^ F (unitVector i) l) ^^
    F (unitVector j) l) ^^ F (fun _ => false) l

theorem component_polar_entry_is_linear (F : Vector → Vector) (b : Vector) (i j : Fin 8) :
    polarEntry (component F b) i j = dot b (polarCoefficients F i j) := by
  unfold polarCoefficients polarEntry component
  rw [dot_xor, dot_xor, dot_xor]

theorem component_matching_candidate_degree (F : Vector → Vector) :
    HasPolynomialDegreeLE (fun b => true ^^ pfaffianValue (polarEntry (component F b))) 4 := by
  have h := candidate_has_degree_le_four (polarCoefficients F)
  have heq : (fun b => true ^^ pfaffianValue (polarEntry (component F b))) =
      (fun b => true ^^ pfaffianValue (fun i j => dot b (polarCoefficients F i j))) := by
    funext b
    congr 1
    apply congrArg pfaffianValue
    funext i j
    exact component_polar_entry_is_linear F b i j
  rw [heq]
  exact h


theorem polarEntry_symmetric (q : Vector → Bool) (i j : Fin 8) :
    polarEntry q i j = polarEntry q j i := by
  have h : vectorXor (unitVector i) (unitVector j) = vectorXor (unitVector j) (unitVector i) := by
    funext k
    exact Bool.xor_comm _ _
  unfold polarEntry
  rw [h]
  cases q (vectorXor (unitVector j) (unitVector i)) <;>
    cases q (unitVector i) <;> cases q (unitVector j) <;> cases q (fun _ => false) <;> rfl

theorem polarEntry_diagonal (q : Vector → Bool) (i : Fin 8) :
    polarEntry q i i = false := by
  have h : vectorXor (unitVector i) (unitVector i) = (fun _ => false) := by
    funext k
    simp [vectorXor]
  unfold polarEntry
  rw [h]
  cases q (fun _ => false) <;> cases q (unitVector i) <;> rfl

theorem xorSum_map_false {α : Type} (xs : List α) :
    xorSum (xs.map fun _ => false) = false := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.map_cons, xorSum, ih]; rfl

theorem dot_zero (c : Fin n → Bool) : dot (fun _ => false) c = false := by
  simp only [dot, Bool.and_false]
  exact xorSum_map_false _

theorem component_zero (F : Vector → Vector) :
    component F (fun _ => false) = (fun _ => false) := by
  funext x
  exact dot_zero _

theorem pfaffian_zero : pfaffianValue (fun _ _ => false) = false := by
  unfold pfaffianValue matchingValue
  exact xorSum_map_false _

theorem candidate_at_zero (F : Vector → Vector) :
    (true ^^ pfaffianValue (polarEntry (component F (fun _ => false)))) = true := by
  rw [component_zero]
  have h : polarEntry (fun _ => false) = (fun _ _ => false) := rfl
  rw [h, pfaffian_zero]
  rfl

#print axioms component_matching_candidate_degree
#print axioms every_matching_valid
#print axioms candidate_at_zero

end QuadraticIndicator
