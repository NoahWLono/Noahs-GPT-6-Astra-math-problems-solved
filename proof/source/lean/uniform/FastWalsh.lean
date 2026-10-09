import Std
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
namespace FastWalsh

inductive Tree : Nat → Type
  | leaf : Int → Tree 0
  | node : Tree n → Tree n → Tree (n+1)
  deriving DecidableEq

def lookup : Tree n → BitVec n → Int
  | .leaf a, _ => a
  | .node l r, u => lookup (if u.msb then r else l) (u.setWidth _)

def tabulate : {n : Nat} → (BitVec n → Int) → Tree n
  | 0, f => .leaf (f 0)
  | n+1, f => .node (tabulate (fun x => f (BitVec.cons false x)))
                       (tabulate (fun x => f (BitVec.cons true x)))

def zip (op : Int → Int → Int) : Tree n → Tree n → Tree n
  | .leaf a, .leaf b => .leaf (op a b)
  | .node a b, .node c d => .node (zip op a c) (zip op b d)

def transform : Tree n → Tree n
  | .leaf a => .leaf a
  | .node l r =>
    let L := transform l
    let R := transform r
    .node (zip (· + ·) L R) (zip (· - ·) L R)

/-- One Walsh butterfly round, at the given distance from the root. -/
def round : Nat → Tree n → Tree n
  | _, .leaf z => .leaf z
  | 0, .node l r => .node (zip (· + ·) l r) (zip (· - ·) l r)
  | k+1, .node l r => .node (round k l) (round k r)

/-- Apply rounds from the deepest requested level back toward the root. -/
def rounds (offset : Nat) : Nat → Tree n → Tree n
  | 0, t => t
  | k+1, t => rounds offset k (round (offset+k) t)

theorem rounds_peel (a k : Nat) (t : Tree n) :
    rounds a (k+1) t = round a (rounds (a+1) k t) := by
  induction k generalizing t with
  | zero => simp [rounds]
  | succ k ih =>
    rw [rounds, ih]
    simp only [rounds]
    congr 3 <;> omega

theorem rounds_node (a k : Nat) (l r : Tree n) :
    rounds (a+1) k (.node l r) = .node (rounds a k l) (rounds a k r) := by
  induction k generalizing l r with
  | zero => rfl
  | succ k ih =>
    simp only [rounds]
    rw [show a+1+k = (a+k)+1 by omega]
    simp only [round, ih]

theorem transform_eq_rounds (t : Tree n) : transform t = rounds 0 n t := by
  induction t with
  | leaf z => rfl
  | node l r hl hr =>
    rw [rounds_peel, rounds_node]
    simp only [round, transform, hl, hr]

/-- A small proof-producing butterfly step, allowing checked subresults to be shared. -/
theorem transform_node_certificate {l r L R : Tree n} {O : Tree (n+1)}
    (hl : transform l = L) (hr : transform r = R)
    (ho : Tree.node (zip (· + ·) L R) (zip (· - ·) L R) = O) :
    transform (Tree.node l r) = O := by
  simp only [transform, hl, hr]
  exact ho

theorem lookup_zip (op : Int → Int → Int) (a b : Tree n) (u : BitVec n) :
    lookup (zip op a b) u = op (lookup a u) (lookup b u) := by
  induction a with
  | leaf x => cases b; rfl
  | node l r ha hb =>
    cases b with
    | node c d =>
      simp only [zip, lookup]
      split <;> simp_all

def sumDomain : {n : Nat} → (BitVec n → Int) → Int
  | 0, f => f 0
  | n+1, f => sumDomain (fun x => f (BitVec.cons false x)) +
              sumDomain (fun x => f (BitVec.cons true x))

theorem sumDomain_neg (f : BitVec n → Int) :
    sumDomain (fun x => -f x) = -sumDomain f := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [sumDomain, ih]; omega

theorem sum_append (a b : List Int) : (a ++ b).sum = a.sum + b.sum := by
  induction a with
  | nil => simp
  | cons a l ih => simp only [List.cons_append, List.sum_cons, ih]; omega

theorem cons_false_ofNat {n k : Nat} (hk : k < 2^n) :
    BitVec.cons false (BitVec.ofNat n k) = BitVec.ofNat (n+1) k := by
  apply BitVec.eq_of_toNat_eq
  have hk' : k < 2^(n+1) := by rw [Nat.pow_succ]; omega
  simp [BitVec.toNat_cons', Nat.mod_eq_of_lt hk, Nat.mod_eq_of_lt hk']

theorem cons_true_ofNat {n k : Nat} (hk : k < 2^n) :
    BitVec.cons true (BitVec.ofNat n k) = BitVec.ofNat (n+1) (2^n+k) := by
  apply BitVec.eq_of_toNat_eq
  have hk' : 2^n+k < 2^(n+1) := by rw [Nat.pow_succ]; omega
  simp only [BitVec.toNat_cons', BitVec.toNat_ofNat, Bool.toNat_true, Nat.shiftLeft_eq, Nat.one_mul, Nat.mod_eq_of_lt hk, Nat.mod_eq_of_lt hk']

theorem sumDomain_eq_range (f : BitVec n → Int) :
    sumDomain f = ((List.range (2^n)).map fun k => f (BitVec.ofNat n k)).sum := by
  induction n with
  | zero => simp [sumDomain, List.range_succ]
  | succ n ih =>
    simp only [sumDomain, ih, Nat.pow_succ]
    rw [show 2^n * 2 = 2^n + 2^n by omega, List.range_add, List.map_append, sum_append, List.map_map]
    congr 1
    · congr 1
      apply List.map_congr_left
      intro k hk
      rw [cons_false_ofNat (List.mem_range.mp hk)]
    · congr 1
      apply List.map_congr_left
      intro k hk
      rw [cons_true_ofNat (List.mem_range.mp hk)]
      rfl

/-- Exactly the coordinate-dot definition used in the earlier certificates. -/
def binaryDot {n : Nat} (x y : BitVec n) : Bool :=
  (List.range n).foldl (fun a i => a ^^ (x.getLsbD i && y.getLsbD i)) false

theorem foldl_congr {α β : Type} (l : List α) (f g : β → α → β)
    (h : ∀ x ∈ l, ∀ a, f a x = g a x) (a : β) :
    l.foldl f a = l.foldl g a := by
  induction l generalizing a with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.foldl_cons]
    rw [h x (by simp) a]
    apply ih
    intro y hy b
    exact h y (by simp [hy]) b

theorem binaryDot_cons (a b : Bool) (u x : BitVec n) :
    binaryDot (BitVec.cons a u) (BitVec.cons b x) = (binaryDot u x ^^ (a && b)) := by
  unfold binaryDot
  rw [List.range_succ, List.foldl_append]
  simp only [List.foldl_cons, List.foldl_nil, BitVec.getLsbD_cons, if_pos rfl, ↓reduceIte]
  congr 1
  apply foldl_congr
  intro k hk c
  have hkn : k ≠ n := by have := List.mem_range.mp hk; omega
  simp [hkn]


def signed (b : Bool) (z : Int) : Int := if b then -z else z

theorem signed_xor_true (b : Bool) (z : Int) : signed (b ^^ true) z = -signed b z := by
  cases b <;> simp [signed]

theorem signed_not (b : Bool) (z : Int) : signed (!b) z = -signed b z := by
  cases b <;> simp [signed]

def weightedSum (f : BitVec n → Int) (u : BitVec n) : Int :=
  sumDomain (fun x => signed (binaryDot u x) (f x))

theorem weightedSum_cons (f : BitVec (n+1) → Int) (b : Bool) (u : BitVec n) :
    weightedSum f (BitVec.cons b u) =
      weightedSum (fun x => f (BitVec.cons false x)) u +
      (if b then -weightedSum (fun x => f (BitVec.cons true x)) u
       else weightedSum (fun x => f (BitVec.cons true x)) u) := by
  cases b <;> simp [weightedSum, sumDomain, binaryDot_cons, signed_xor_true, signed_not, sumDomain_neg]

theorem transform_correct (f : BitVec n → Int) :
    ∀ u, lookup (transform (tabulate f)) u = weightedSum f u := by
  induction n with
  | zero => intro u; simp [tabulate, transform, lookup, weightedSum, sumDomain, binaryDot, signed]
  | succ n ih =>
    rw [BitVec.forall_cons_iff]
    intro b u
    cases b <;>
      simp [tabulate, transform, lookup, lookup_zip, ih, weightedSum_cons, Int.sub_eq_add_neg]

/-- A full character-weighted sum over the canonical enumeration of the binary vector space. -/
theorem transform_eq_character_sum (f : BitVec n → Int) (u : BitVec n) :
    lookup (transform (tabulate f)) u =
      ((List.range (2^n)).map fun k =>
        signed (binaryDot u (BitVec.ofNat n k)) (f (BitVec.ofNat n k))).sum := by
  rw [transform_correct, weightedSum, sumDomain_eq_range]


/-- The original finite integer Walsh coefficient. -/
def walsh {n m : Nat} (f : BitVec n → BitVec m) (b : BitVec m) (u : BitVec n) : Int :=
  ((List.range (2^n)).map fun k =>
    if binaryDot b (f (BitVec.ofNat n k)) ^^ binaryDot u (BitVec.ofNat n k)
    then (-1 : Int) else 1).sum

def fastWalsh {n m : Nat} (f : BitVec n → BitVec m) (b : BitVec m) : Tree n :=
  transform (tabulate (fun x => signed (binaryDot b (f x)) 1))

theorem signed_signed (b c : Bool) (z : Int) :
    signed c (signed b z) = signed (b ^^ c) z := by
  cases b <;> cases c <;> simp [signed]

/-- Fully generic bridge: the fast transform is exactly the original bit-vector Walsh sum. -/
theorem fastWalsh_correct {n m : Nat} (f : BitVec n → BitVec m) (b : BitVec m) (u : BitVec n) :
    lookup (fastWalsh f b) u = walsh f b u := by
  rw [fastWalsh, transform_eq_character_sum]
  simp only [signed_signed]
  rfl

def allTree (p : Int → Bool) : Tree n → Bool
  | .leaf z => p z
  | .node l r => allTree p l && allTree p r

theorem allTree_iff (p : Int → Bool) (t : Tree n) :
    allTree p t = true ↔ ∀ u, p (lookup t u) = true := by
  induction t with
  | leaf z =>
    constructor
    · intro h u; exact h
    · intro h; exact h 0
  | node l r hl hr =>
    rw [allTree, Bool.and_eq_true, hl, hr, BitVec.forall_cons_iff]
    constructor
    · intro ⟨a,b⟩ c u
      cases c <;> simp only [lookup, BitVec.msb_cons, BitVec.setWidth_cons, Bool.false_eq_true, ↓reduceIte]
      · exact a u
      · exact b u
    · intro h
      constructor
      · intro u; simpa [lookup] using h false u
      · intro u; simpa [lookup] using h true u

def IsBent {n m : Nat} (f : BitVec n → BitVec m) (b : BitVec m) : Prop :=
  ∀ u : BitVec n, walsh f b u * walsh f b u = (2^n : Nat)

def fastBent {n m : Nat} (f : BitVec n → BitVec m) (b : BitVec m) : Bool :=
  allTree (fun z => z*z == (2^n : Nat)) (fastWalsh f b)

theorem fastBent_correct {n m : Nat} (f : BitVec n → BitVec m) (b : BitVec m) :
    fastBent f b = true ↔ IsBent f b := by
  simp only [fastBent, allTree_iff, fastWalsh_correct, beq_iff_eq, IsBent]

#print axioms transform_eq_character_sum
#print axioms fastWalsh_correct
#print axioms fastBent_correct
end FastWalsh
