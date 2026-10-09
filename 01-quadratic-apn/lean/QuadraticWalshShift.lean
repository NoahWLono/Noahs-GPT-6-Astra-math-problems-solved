import Quadratic
namespace QuadraticWalshShift
open FastWalsh

/-- Reindexing the complete binary domain by XOR translation. -/
theorem sumDomain_xor (f : BitVec n → Int) (a : BitVec n) :
    sumDomain (fun x => f (x ^^^ a)) = sumDomain f := by
  induction n with
  | zero => have ha : a = 0 := Subsingleton.elim _ _; subst a; simp [sumDomain]
  | succ n ih =>
    rw [← BitVec.cons_msb_setWidth a]
    generalize a.msb = b
    generalize a.setWidth n = c
    cases b <;> simp only [sumDomain, BitVec.cons_xor_cons, Bool.xor_false,
      Bool.false_xor, Bool.true_xor, Bool.xor_true]
    · rw [ih (fun x => f (BitVec.cons false x)) c, ih (fun x => f (BitVec.cons true x)) c]
    · simp only [Bool.not_false, Bool.not_true]
      rw [ih (fun x => f (BitVec.cons false x)) c, ih (fun x => f (BitVec.cons true x)) c]; omega

theorem sumDomain_signed (f : BitVec n → Int) (b : Bool) :
    sumDomain (fun x => signed b (f x)) = signed b (sumDomain f) := by
  cases b <;> simp [signed, sumDomain_neg]

def booleanWalsh (q : BitVec n → Bool) (u : BitVec n) : Int :=
  sumDomain (fun x => signed (q x ^^ binaryDot u x) 1)

theorem binaryDot_comm (x y : BitVec n) : binaryDot x y = binaryDot y x := by
  unfold binaryDot
  apply foldl_congr
  intro k hk acc
  rw [Bool.and_comm]

theorem binaryDot_zero_left (x : BitVec n) : binaryDot (0 : BitVec n) x = false := by
  rw [binaryDot_comm]
  exact binaryDot_zero x

theorem booleanWalsh_zero (q : BitVec n → Bool) :
    booleanWalsh q 0 = sumDomain (fun x => signed (q x) 1) := by
  simp only [booleanWalsh, binaryDot_zero_left, Bool.xor_false]

/-- Alignment is an explicit obligation, not an assumed rank criterion. -/
theorem booleanWalsh_shift (q : BitVec n → Bool) (u a : BitVec n)
    (align : ∀ x, q (x ^^^ a) = (q x ^^ q a ^^ binaryDot u x)) :
    booleanWalsh q u = signed (q a) (booleanWalsh q 0) := by
  rw [booleanWalsh_zero, ← sumDomain_xor (fun x => signed (q x) 1) a, ← sumDomain_signed]
  unfold booleanWalsh
  congr 1
  funext x
  rw [align]
  cases q x <;> cases q a <;> cases binaryDot u x <;> decide

theorem walsh_eq_booleanWalsh (f : BitVec n → BitVec m) (b : BitVec m) (u : BitVec n) :
    walsh f b u = booleanWalsh (fun x => binaryDot b (f x)) u := by
  rw [booleanWalsh, sumDomain_eq_range]
  rfl

/-- Shift theorem for the original concrete finite integer Walsh sum. -/
theorem walsh_shift (f : BitVec n → BitVec m) (b : BitVec m) (u a : BitVec n)
    (align : ∀ x, binaryDot b (f (x ^^^ a)) =
      (binaryDot b (f x) ^^ binaryDot b (f a) ^^ binaryDot u x)) :
    walsh f b u = signed (binaryDot b (f a)) (walsh f b 0) := by
  simp only [walsh_eq_booleanWalsh]
  exact booleanWalsh_shift _ u a align


/-- The explicitly evaluated polar polynomial of the coefficient list. -/
def coefficientPolar (cs : List (Nat × Nat × BitVec m)) (b : BitVec m)
    (a x : BitVec n) : Bool :=
  match cs with
  | [] => false
  | c :: cs =>
    (binaryDot b c.2.2 &&
      ((x.getLsbD c.1 && a.getLsbD c.2.1) ^^
       (a.getLsbD c.1 && x.getLsbD c.2.1))) ^^ coefficientPolar cs b a x

theorem quadraticComponent_translate (cs : List (Nat × Nat × BitVec m))
    (b : BitVec m) (a x : BitVec n) :
    quadraticComponent cs b (x ^^^ a) =
      (quadraticComponent cs b x ^^ quadraticComponent cs b a ^^ coefficientPolar cs b a x) := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    simp only [quadraticComponent, coefficientPolar, BitVec.getLsbD_xor, ih]
    generalize binaryDot b c.2.2 = t
    generalize x.getLsbD c.1 = xi
    generalize x.getLsbD c.2.1 = xj
    generalize a.getLsbD c.1 = ai
    generalize a.getLsbD c.2.1 = aj
    generalize quadraticComponent cs b x = qx
    generalize quadraticComponent cs b a = qa
    generalize coefficientPolar cs b a x = p
    decide +revert

theorem coefficientPolar_add_right (cs : List (Nat × Nat × BitVec m))
    (b : BitVec m) (a x y : BitVec n) :
    coefficientPolar cs b a (x ^^^ y) =
      (coefficientPolar cs b a x ^^ coefficientPolar cs b a y) := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    simp only [coefficientPolar, BitVec.getLsbD_xor, ih,
      Bool.and_xor_distrib_left, Bool.and_xor_distrib_right]
    simp [Bool.xor_assoc, Bool.xor_comm, Bool.xor_left_comm]

theorem coefficientPolar_comm (cs : List (Nat × Nat × BitVec m))
    (b : BitVec m) (a x : BitVec n) :
    coefficientPolar cs b a x = coefficientPolar cs b x a := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    simp only [coefficientPolar, ih]
    rw [Bool.xor_comm (x.getLsbD c.1 && a.getLsbD c.2.1)]

theorem coefficientPolar_add_left (cs : List (Nat × Nat × BitVec m))
    (b : BitVec m) (a d x : BitVec n) :
    coefficientPolar cs b (a ^^^ d) x =
      (coefficientPolar cs b a x ^^ coefficientPolar cs b d x) := by
  rw [coefficientPolar_comm, coefficientPolar_add_right]
  rw [coefficientPolar_comm cs b x a, coefficientPolar_comm cs b x d]

/-- Canonical basis, most significant coordinate last. -/
def basis : (n : Nat) → List (BitVec n)
  | 0 => []
  | n+1 => (basis n).map (BitVec.cons false) ++ [BitVec.cons true 0]

/-- Equality of additive Boolean maps needs only the basis checks. -/
theorem additive_eq_of_basis (f g : BitVec n → Bool)
    (hf : ∀ x y, f (x ^^^ y) = (f x ^^ f y))
    (hg : ∀ x y, g (x ^^^ y) = (g x ^^ g y))
    (hb : ∀ e ∈ basis n, f e = g e) : ∀ x, f x = g x := by
  induction n with
  | zero =>
    have f0 : f 0 = false := by have h := hf 0 0; simpa using h
    have g0 : g 0 = false := by have h := hg 0 0; simpa using h
    intro x
    have hx : x = 0 := Subsingleton.elim _ _
    rw [hx]
    exact f0.trans g0.symm
  | succ n ih =>
    have hlow := ih (fun x => f (BitVec.cons false x)) (fun x => g (BitVec.cons false x))
      (by intro x y; simpa using hf (BitVec.cons false x) (BitVec.cons false y))
      (by intro x y; simpa using hg (BitVec.cons false x) (BitVec.cons false y))
      (by intro e he; exact hb _ (List.mem_append_left _ (List.mem_map.mpr ⟨e, he, rfl⟩)))
    intro x
    rw [← BitVec.cons_msb_setWidth x]
    generalize x.msb = t
    generalize x.setWidth n = y
    cases t
    · exact hlow y
    · have he := hb (BitVec.cons true 0) (by simp [basis])
      have hdecomp : BitVec.cons true y =
          (BitVec.cons false y ^^^ BitVec.cons true (0 : BitVec n)) := by
        rw [BitVec.cons_xor_cons]
        exact congrArg (BitVec.cons true) (BitVec.xor_zero (x := y)).symm
      rw [hdecomp, hf, hg]
      exact congr (congrArg Bool.xor (hlow y)) he


/-- A sparse column representation; duplicate coordinates are allowed. -/
def columnMap (columns : List (Nat × BitVec k)) (u : BitVec n) : BitVec k :=
  match columns with
  | [] => 0
  | (i, v) :: cs => (if u.getLsbD i then v else 0) ^^^ columnMap cs u

theorem xor_left_comm (a b c : BitVec n) : a ^^^ (b ^^^ c) = b ^^^ (a ^^^ c) := by
  rw [← BitVec.xor_assoc, BitVec.xor_comm a b, BitVec.xor_assoc]

theorem xor_self_cancel (a b : BitVec n) : a ^^^ (a ^^^ b) = b := by
  rw [← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]

theorem columnMap_add (columns : List (Nat × BitVec k)) (u v : BitVec n) :
    columnMap columns (u ^^^ v) = (columnMap columns u ^^^ columnMap columns v) := by
  induction columns with
  | nil => simp [columnMap]
  | cons c cs ih =>
    simp only [columnMap, BitVec.getLsbD_xor, ih]
    cases u.getLsbD c.1 <;> cases v.getLsbD c.1 <;>
      simp [BitVec.xor_assoc, BitVec.xor_comm, xor_left_comm, xor_self_cancel]

theorem binaryDot_add_left (u v x : BitVec n) :
    binaryDot (u ^^^ v) x = (binaryDot u x ^^ binaryDot v x) := by
  rw [binaryDot_comm, binaryDot_xor_right]
  rw [binaryDot_comm x u, binaryDot_comm x v]

/-- Only n squared Boolean checks are needed to certify inverse alignment.
The inverse candidate is an explicitly given additive column map. -/
theorem coefficient_alignment_of_basis
    (cs : List (Nat × Nat × BitVec m)) (b : BitVec m)
    (columns : List (Nat × BitVec n))
    (hcheck : ∀ e ∈ basis n, ∀ d ∈ basis n,
      coefficientPolar cs b (columnMap columns e) d = binaryDot e d) :
    ∀ u x : BitVec n,
      coefficientPolar cs b (columnMap columns u) x = binaryDot u x := by
  intro u
  apply additive_eq_of_basis
  · exact coefficientPolar_add_right cs b (columnMap columns u)
  · exact binaryDot_xor_right u
  · intro d hd
    have h := additive_eq_of_basis
      (fun e : BitVec n => coefficientPolar cs b (columnMap columns e) d)
      (fun e : BitVec n => binaryDot e d)
      (by intro e f; dsimp only; rw [columnMap_add, coefficientPolar_add_left])
      (by intro e f; exact binaryDot_add_left e f d)
      (by intro e he; exact hcheck e he d hd)
    exact h u

/-- Actual Walsh-shift certificate from the quadratic coefficient list and
n squared inverse checks, without an admitted rank-to-Walsh criterion. -/
theorem quadratic_walsh_shift_of_basis
    (cs : List (Nat × Nat × BitVec m)) (b : BitVec m)
    (columns : List (Nat × BitVec n))
    (hcheck : ∀ e ∈ basis n, ∀ d ∈ basis n,
      coefficientPolar cs b (columnMap columns e) d = binaryDot e d)
    (u : BitVec n) :
    walsh (quadratic cs) b u =
      signed (quadraticComponent cs b (columnMap columns u)) (walsh (quadratic cs) b (0 : BitVec n)) := by
  have h := walsh_shift (quadratic cs) b u (columnMap columns u)
  simp only [quadratic_component_correct] at h
  apply h
  intro x
  rw [quadraticComponent_translate, coefficient_alignment_of_basis cs b columns hcheck]

/-- The final bent conclusion additionally requires the exact zero-frequency check. -/
theorem quadratic_bent_of_basis_and_zero
    (cs : List (Nat × Nat × BitVec m)) (b : BitVec m)
    (columns : List (Nat × BitVec n))
    (hcheck : ∀ e ∈ basis n, ∀ d ∈ basis n,
      coefficientPolar cs b (columnMap columns e) d = binaryDot e d)
    (hzero : walsh (quadratic cs) b (0 : BitVec n) * walsh (quadratic cs) b (0 : BitVec n) = (2^n : Nat)) :
    IsBent (quadratic cs : BitVec n → BitVec m) b := by
  intro u
  rw [quadratic_walsh_shift_of_basis cs b columns hcheck u]
  cases quadraticComponent cs b (columnMap columns u) <;> simpa [signed, Int.neg_mul_neg] using hzero


/-- Small executable certificate: n squared checks per output component. -/
def basisAlignmentCheck (cs : List (Nat × Nat × BitVec m)) (b : BitVec m)
    (columns : List (Nat × BitVec n)) : Bool :=
  (basis n).all fun e => (basis n).all fun d =>
    coefficientPolar cs b (columnMap columns e) d == binaryDot e d

theorem basisAlignmentCheck_correct
    (cs : List (Nat × Nat × BitVec m)) (b : BitVec m)
    (columns : List (Nat × BitVec n)) :
    basisAlignmentCheck cs b columns = true ↔
      ∀ e ∈ basis n, ∀ d ∈ basis n,
        coefficientPolar cs b (columnMap columns e) d = binaryDot e d := by
  simp [basisAlignmentCheck, List.all_eq_true, beq_iff_eq]

theorem walsh_quadratic_eq (cs : List (Nat × Nat × BitVec m)) (b : BitVec m)
    (u : BitVec n) :
    walsh (quadratic cs) b u = booleanWalsh (quadraticComponent cs b) u := by
  rw [walsh_eq_booleanWalsh]
  simp only [quadratic_component_correct]

/-- Direct scalar zero sum avoids recomputing vector outputs during evaluation. -/
def componentZeroSum (n : Nat) (cs : List (Nat × Nat × BitVec m)) (b : BitVec m) : Int :=
  sumDomain (fun x : BitVec n => signed (quadraticComponent cs b x) 1)

theorem componentZeroSum_correct (cs : List (Nat × Nat × BitVec m)) (b : BitVec m) :
    componentZeroSum n cs b = walsh (quadratic cs) b (0 : BitVec n) := by
  rw [walsh_quadratic_eq, booleanWalsh_zero]
  rfl

/-- Ready-to-instantiate checked certificate interface. The two hypotheses must
still be proved for every desired concrete component. -/
theorem quadratic_bent_certificate
    (cs : List (Nat × Nat × BitVec m)) (b : BitVec m)
    (columns : List (Nat × BitVec n))
    (hcheck : basisAlignmentCheck cs b columns = true)
    (hzero : componentZeroSum n cs b * componentZeroSum n cs b = (2^n : Nat)) :
    IsBent (quadratic cs : BitVec n → BitVec m) b := by
  apply quadratic_bent_of_basis_and_zero cs b columns
  · exact (basisAlignmentCheck_correct cs b columns).mp hcheck
  · simpa only [componentZeroSum_correct] using hzero

#print axioms quadratic_bent_certificate
#print axioms quadraticComponent_translate
#print axioms additive_eq_of_basis
#print axioms coefficient_alignment_of_basis
#print axioms quadratic_bent_of_basis_and_zero
#print axioms walsh_shift
end QuadraticWalshShift
