import FamilyAlgebra.ConcreteExpansion

namespace FamilyAlgebra
variable {E : Type*} [Field E]

theorem concrete_cross_triangular (u v w z : Bool) (s t : Nat → Bool)
    (n k : Nat)
    (tail : ∀ j, k<j → j<n → (s j || t j)=false) :
    termCoeff (crossTerms (family u v w z s t) (List.range n)) k = false := by
  apply termCoeff_false
  intro p hp hpk
  rcases List.mem_map.mp hp with ⟨r,hr,rfl⟩
  rcases indexPairs_members (List.range n) List.pairwise_lt_range r hr with ⟨_,hj,hij⟩
  have hjn := List.mem_range.mp hj
  have hkj : k<r.2 := by dsimp at hpk; omega
  exact family_pair_vanish u v w z s t r.1 r.2 (by omega) (tail r.2 hkj hjn)

/-- The concrete parity-specific extension pencil has zero Pfaffian precisely
when every extension parameter is zero and the base Pfaffian is zero.

The ONLY algebraic assumptions are a field of characteristic two, positive n,
and binary independence of 1,a,...,a^(n-1). The concrete plane identities,
Pfaffian expansion, midpoint regrouping, and triangular support are proved. -/
theorem concrete_zero_locus (two_zero : (2:E)=0) (a : E)
    (n : Nat) (positive : 0<n)
    (independent : ∀ bits, binarySum (fun k => a^k) bits n = 0 ↔
      ∀ k, k<n → bits k=false)
    (u v w z : Bool) (s t : Nat → Bool) :
    Pfaffian.pf (pencil a (family u v w z s t) n) = 0 ↔
      q (base u v w z)=false ∧ ∀ j, 0<j → j<n → s j=false ∧ t j=false := by
  let active : Nat → Bool := fun j => if j<n then s j || t j else false
  let diag : Nat → Bool := fun j => if j<n then q (family u v w z s t j) else false
  let perturb : Nat → Bool := termCoeff (crossTerms (family u v w z s t) (List.range n))
  have hb : ∀ j, n≤j → active j=false := by
    intro j hj
    simp [active, show ¬j<n by omega]
  have ha : ∀ j, 0<j → diag j=active j := by
    intro j hj
    simp only [diag, active]
    by_cases hn : j<n
    · simp [hn, family_diag u v w z s t j hj]
    · simp [hn]
  have ht : ∀ k, (∀ j, k<j → active j=false) → perturb k=false := by
    intro k htail
    apply concrete_cross_triangular
    intro j hkj hjn
    have hx := htail j hkj
    simpa [active, hjn] using hx
  have he : Pfaffian.pf (pencil a (family u v w z s t) n) =
      binarySum (fun k => (a^k)^2) (fun k => diag k ^^ perturb k) n := by
    rw [pencil_expansion two_zero a _ (family_odd_pair u v w z s t)]
    apply binarySum_congr
    intro k hk
    simp [diag, perturb, hk]
  rw [field_zero_locus two_zero (fun k => a^k) n positive independent
    active diag perturb _ he hb ha ht]
  constructor
  · rintro ⟨h0, hall⟩
    refine ⟨?_, ?_⟩
    · simpa [diag, positive, family] using h0
    · intro j hj hjn
      have hx := hall j hj
      have hor : (s j || t j)=false := by simpa [active, hjn] using hx
      cases hs : s j <;> cases ht : t j <;> simp_all
  · rintro ⟨h0, hall⟩
    refine ⟨?_, ?_⟩
    · simpa [diag, positive, family] using h0
    · intro j hj
      by_cases hjn : j<n
      · rcases hall j hj hjn with ⟨hs,ht⟩
        simp [active, hjn, hs, ht]
      · simp [active, hjn]

def sixBaseTuples : List (Bool × Bool × Bool × Bool) :=
  [(false,false,false,false), (false,false,true,false),
   (false,false,false,true), (true,false,true,true),
   (false,true,true,true), (true,true,true,true)]

theorem base_zero_six_tuples : ∀ u v w z,
    q (base u v w z)=false ↔ (u,v,w,z) ∈ sixBaseTuples := by decide

/-- Explicit six-tuple classification, with every extension parameter zero. -/
theorem concrete_zero_locus_six (two_zero : (2:E)=0) (a : E)
    (n : Nat) (positive : 0<n)
    (independent : ∀ bits, binarySum (fun k => a^k) bits n = 0 ↔
      ∀ k, k<n → bits k=false)
    (u v w z : Bool) (s t : Nat → Bool) :
    Pfaffian.pf (pencil a (family u v w z s t) n) = 0 ↔
      (u,v,w,z) ∈ sixBaseTuples ∧ ∀ j, 0<j → j<n → s j=false ∧ t j=false := by
  rw [concrete_zero_locus two_zero a n positive independent, base_zero_six_tuples]

#print axioms concrete_zero_locus_six
#print axioms concrete_zero_locus
end FamilyAlgebra
