import FamilyAlgebra.CoefficientEvaluation

namespace FamilyAlgebra
variable {E : Type*} [Field E]

def indexPairs : List Nat → List (Nat × Nat)
  | [] => []
  | i::is => is.map (fun j => (i,j)) ++ indexPairs is

theorem indexPairs_members (xs : List Nat) (ordered : xs.Pairwise (· < ·))
    (p : Nat × Nat) (hp : p ∈ indexPairs xs) :
    p.1 ∈ xs ∧ p.2 ∈ xs ∧ p.1 < p.2 := by
  induction xs with
  | nil => simp [indexPairs] at hp
  | cons i is ih =>
    rcases List.pairwise_cons.mp ordered with ⟨hi, his⟩
    rcases List.mem_append.mp hp with h | h
    · rcases List.mem_map.mp h with ⟨j, hj, rfl⟩
      exact ⟨by simp, by simp [hj], hi j hj⟩
    · rcases ih his h with ⟨h1,h2,h3⟩
      exact ⟨by simp [h1], by simp [h2], h3⟩

def crossTerms (X : Nat → Six) (xs : List Nat) : List (Nat × Bool) :=
  (indexPairs xs).map (fun p => ((p.1+p.2)/2, beta (X p.1) (X p.2)))

theorem crossTerms_bounded (X : Nat → Six) (n : Nat)
    (p : Nat × Bool) (hp : p ∈ crossTerms X (List.range n)) : p.1<n := by
  rcases List.mem_map.mp hp with ⟨r,hr,rfl⟩
  rcases indexPairs_members (List.range n) List.pairwise_lt_range r hr with ⟨_,hj,hij⟩
  have hjn := List.mem_range.mp hj
  simp only
  omega

theorem scalarSum_append (xs ys : List E) :
    Pfaffian.scalarSum (xs++ys) = Pfaffian.scalarSum xs + Pfaffian.scalarSum ys := by
  induction xs with
  | nil => simp [Pfaffian.scalarSum]
  | cons x xs ih => simp [Pfaffian.scalarSum, ih, add_assoc]

theorem scalarSum_range (weight : Nat → E) (bits : Nat → Bool) (n : Nat) :
    Pfaffian.scalarSum ((List.range n).map (fun i => if bits i then weight i else 0)) =
      binarySum weight bits n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [List.range_succ, List.map_append, scalarSum_append,
      List.map_cons, List.map_nil, Pfaffian.scalarSum, add_zero, ih, binarySum]

theorem weighted_pair_term (two_zero : (2:E)=0) (a : E) (X : Nat → Six)
    (odd_vanish : ∀ i j, i<j → (i+j)%2=1 → beta (X i) (X j)=false)
    (i j : Nat) (hij : i<j) :
    a^i*a^j*Pfaffian.polar (liftSix (X i)) (liftSix (X j)) =
      termValue (fun k => (a^k)^2) ((i+j)/2, beta (X i) (X j)) := by
  rw [lift_polar two_zero]
  by_cases ho : (i+j)%2=1
  · rw [odd_vanish i j hij ho]
    simp [bit, termValue]
  · have he : i+j=2*((i+j)/2) := by omega
    rw [Pfaffian.power_midpoint a i j ((i+j)/2) he]
    cases beta (X i) (X j) <;> simp [bit, termValue]

theorem weighted_pairs_concrete (two_zero : (2:E)=0) (a : E) (X : Nat → Six)
    (odd_vanish : ∀ i j, i<j → (i+j)%2=1 → beta (X i) (X j)=false)
    (xs : List Nat) (ordered : xs.Pairwise (· < ·)) :
    Pfaffian.weightedPairSum (xs.map (fun i => (a^i, liftSix (X i)))) =
      Pfaffian.scalarSum ((crossTerms X xs).map (termValue (fun k => (a^k)^2))) := by
  induction xs with
  | nil => rfl
  | cons i is ih =>
    rcases List.pairwise_cons.mp ordered with ⟨hi, his⟩
    simp only [List.map_cons, Pfaffian.weightedPairSum, List.map_map, Function.comp_def]
    rw [ih his]
    simp only [crossTerms, indexPairs, List.map_append, List.map_map,
      Function.comp_def, scalarSum_append]
    congr 1
    congr 1
    apply List.map_congr_left
    intro j hj
    exact weighted_pair_term two_zero a X odd_vanish i j (hi j hj)

/-- The actual extension pencil, using the concrete binary six-coordinate data. -/
def pencil (a : E) (X : Nat → Six) (n : Nat) : Pfaffian.Coordinates E :=
  Pfaffian.vectorSum ((List.range n).map (fun i => Pfaffian.scale (a^i) (liftSix (X i))))

/-- No abstract Pfaffian-expansion hypothesis: the midpoint coefficients are
computed from the actual indexed cross terms of the concrete pencil. -/
theorem pencil_expansion (two_zero : (2:E)=0) (a : E) (X : Nat → Six)
    (odd_vanish : ∀ i j, i<j → (i+j)%2=1 → beta (X i) (X j)=false)
    (n : Nat) :
    Pfaffian.pf (pencil a X n) = binarySum (fun k => (a^k)^2)
      (fun k => q (X k) ^^ termCoeff (crossTerms X (List.range n)) k) n := by
  have h := Pfaffian.weighted_finite_expansion
    ((List.range n).map (fun i => (a^i, (liftSix (X i) : Pfaffian.Coordinates E))))
  simp only [List.map_map, Function.comp_def] at h
  change Pfaffian.pf (pencil a X n) = _ at h
  rw [weighted_pairs_concrete two_zero a X odd_vanish (List.range n) List.pairwise_lt_range] at h
  have hd : Pfaffian.scalarSum ((List.range n).map (fun i => (a^i)^2 * Pfaffian.pf (liftSix (X i)))) =
      binarySum (fun k => (a^k)^2) (fun k => q (X k)) n := by
    have hm : (fun i => (a^i)^2 * Pfaffian.pf (liftSix (X i))) =
        (fun i => if q (X i) then (a^i)^2 else 0) := by
      funext i
      rw [lift_pf two_zero]
      cases q (X i) <;> simp [bit]
    rw [hm, scalarSum_range]
  rw [hd, ← evaluate_terms two_zero _ _ n (crossTerms_bounded X n)] at h
  rw [h, binarySum_xor two_zero]

#print axioms pencil_expansion
end FamilyAlgebra
