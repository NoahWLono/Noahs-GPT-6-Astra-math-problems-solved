import Std

/-! Algebraic skeleton of the characteristic-two extension construction.
No assertion about Boolean bentness, trace, or cryptographic optimality occurs here. -/
namespace FamilyAlgebra

structure Six where
  a : Bool
  b : Bool
  c : Bool
  d : Bool
  f : Bool
  g : Bool
  deriving DecidableEq

def add (x y : Six) : Six :=
  ⟨x.a ^^ y.a, x.b ^^ y.b, x.c ^^ y.c,
   x.d ^^ y.d, x.f ^^ y.f, x.g ^^ y.g⟩
def q (x : Six) : Bool := (x.a && x.g) ^^ (x.b && x.f) ^^ (x.c && x.d)
def beta (x y : Six) : Bool := q (add x y) ^^ q x ^^ q y

def base (u v w z : Bool) : Six := ⟨u ^^ v, u, w, z, v, u ^^ v⟩
def oddPlane (s t : Bool) : Six := ⟨s ^^ t, s, false, false, s, t⟩
def evenPlane (s t : Bool) : Six := ⟨false, t, s ^^ t, s, t, false⟩

theorem base_pfaffian : ∀ u v w z,
    q (base u v w z) = (u ^^ v ^^ (u && v) ^^ (w && z)) := by decide

theorem odd_anisotropic : ∀ s t,
    q (oddPlane s t) = (s || t) := by decide

theorem even_anisotropic : ∀ s t,
    q (evenPlane s t) = (s || t) := by decide

theorem base_odd_orthogonal : ∀ u v w z s t,
    beta (base u v w z) (oddPlane s t) = false := by decide

theorem odd_even_orthogonal : ∀ s t u v,
    beta (oddPlane s t) (evenPlane u v) = false := by decide

theorem base_injective : ∀ u v w z u' v' w' z',
    base u v w z = base u' v' w' z' →
      u = u' ∧ v = v' ∧ w = w' ∧ z = z' := by decide

theorem odd_plane_zero_iff : ∀ s t,
    oddPlane s t = ⟨false,false,false,false,false,false⟩ ↔ s = false ∧ t = false := by decide

theorem even_plane_zero_iff : ∀ s t,
    evenPlane s t = ⟨false,false,false,false,false,false⟩ ↔ s = false ∧ t = false := by decide

theorem beta_symmetric : ∀ x y : Six, beta x y = beta y x := by
  intro x y
  have h : add x y = add y x := by
    cases x
    cases y
    simp [add, Bool.xor_comm]
  simp only [beta, h, Bool.xor_assoc, Bool.xor_left_comm, Bool.xor_comm]

def baseLabel (i : Nat) : Six := base (i.testBit 0) (i.testBit 1)
  (i.testBit 2) (i.testBit 3)

theorem exactly_six_base_zeros :
    ((List.range 16).filter (fun i => !(q (baseLabel i)))) = [0,4,8,13,14,15] := by decide

def xorList : List Bool → Bool
  | [] => false
  | b :: bs => b ^^ xorList bs

theorem xorList_false (xs : List Bool) (h : ∀ x ∈ xs, x = false) :
    xorList xs = false := by
  induction xs with
  | nil => rfl
  | cons b bs ih =>
    have hb := h b (by simp)
    have ht : ∀ x ∈ bs, x = false := by
      intro x hx
      exact h x (by simp [hx])
    simp [xorList, hb, ih ht]

/-- A concrete cross-term coefficient. The list contains the ordered pairs
whose even index sum has half-index k. -/
def cross (pairs : List (Nat × Nat)) (B : Nat → Nat → Bool) : Bool :=
  xorList (pairs.map (fun p => B p.1 p.2))

theorem cross_false_above (pairs : List (Nat × Nat)) (B : Nat → Nat → Bool)
    (active : Nat → Bool) (k : Nat)
    (higher : ∀ p ∈ pairs, k < p.2)
    (vanish : ∀ i j, active j = false → B i j = false)
    (tail : ∀ j, k < j → active j = false) : cross pairs B = false := by
  apply xorList_false
  intro b hb
  rcases List.mem_map.mp hb with ⟨p, hp, rfl⟩
  exact vanish p.1 p.2 (tail p.2 (higher p hp))

/-- Arithmetic reason a surviving cross term lies below its upper index. -/
theorem half_index_lt (i j k : Nat) (hij : i < j) (hsum : i + j = 2*k) :
    k < j := by omega

/-- Descending triangular elimination. The diagonal at each positive index
records whether its parameter is nonzero. A cross coefficient at k vanishes
when every parameter strictly above k vanishes. -/
theorem triangular_elimination (n : Nat) (active diag perturb : Nat → Bool)
    (bounded : ∀ j, n ≤ j → active j = false)
    (anisotropic : ∀ j, 0 < j → diag j = active j)
    (triangular : ∀ k, (∀ j, k < j → active j = false) → perturb k = false)
    (coeff_zero : ∀ k, k < n → (diag k ^^ perturb k) = false) :
    ∀ j, 0 < j → active j = false := by
  have descend : ∀ d k, n - k = d → (∀ j, k ≤ j → 0 < j → active j = false) := by
    intro d
    induction d using Nat.strongRecOn with
    | ind d ih =>
      intro k hk j hkj hj
      by_cases hn : n ≤ j
      · exact bounded j hn
      · have htail : ∀ l, j < l → active l = false := by
          intro l hjl
          by_cases hnl : n ≤ l
          · exact bounded l hnl
          · exact ih (n-l) (by omega) l rfl l (by omega) (by omega)
        have hp := triangular j htail
        have hc := coeff_zero j (by omega)
        rw [hp, Bool.xor_false, anisotropic j hj] at hc
        exact hc
  intro j hj
  exact descend n 0 (by omega) j (by omega) hj

/-- Zero-locus theorem under an explicit independent-coordinate evaluation.
`independent` is the binary linear-independence condition for the squared
basis powers. `expansion` is the Pfaffian coefficient expansion; it is an
explicit hypothesis rather than an unproved field-extension bridge. -/
theorem zero_locus {E : Type} (zero : E) (n : Nat) (positive : 0 < n)
    (active diag perturb : Nat → Bool) (evaluate : (Fin n → Bool) → E) (value : E)
    (independent : ∀ c, evaluate c = zero ↔ ∀ k, c k = false)
    (expansion : value = evaluate (fun k => diag k ^^ perturb k))
    (bounded : ∀ j, n ≤ j → active j = false)
    (anisotropic : ∀ j, 0 < j → diag j = active j)
    (triangular : ∀ k, (∀ j, k < j → active j = false) → perturb k = false) :
    value = zero ↔ diag 0 = false ∧ ∀ j, 0 < j → active j = false := by
  rw [expansion, independent]
  constructor
  · intro h
    have hc : ∀ k, k < n → (diag k ^^ perturb k) = false := by
      intro k hk
      exact h ⟨k, hk⟩
    have ha := triangular_elimination n active diag perturb bounded anisotropic triangular hc
    refine ⟨?_, ha⟩
    have hp := triangular 0 ha
    have h0 := hc 0 positive
    simpa [hp] using h0
  · rintro ⟨h0, ha⟩ k
    have hp : perturb k = false := triangular k (by
      intro j hj
      exact ha j (by omega))
    by_cases hk : k.val = 0
    · rw [hp, Bool.xor_false, hk, h0]
    · simp [hp, anisotropic k (by omega), ha k (by omega)]

#print axioms zero_locus
#print axioms exactly_six_base_zeros
end FamilyAlgebra
