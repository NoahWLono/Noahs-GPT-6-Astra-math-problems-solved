import QuadraticWalshShift
namespace QuadraticWalshParseval
open FastWalsh QuadraticWalshShift

def energy : Tree n → Int
  | .leaf a => a*a
  | .node l r => energy l + energy r

theorem parallelogram (a b : Int) :
    (a+b)*(a+b)+(a-b)*(a-b)=2*(a*a+b*b) := by
  simp only [Int.add_mul, Int.mul_add, Int.sub_mul, Int.mul_sub]
  omega

theorem zip_energy (a b : Tree n) :
    energy (zip (·+·) a b) + energy (zip (·-·) a b) = 2*(energy a+energy b) := by
  induction a with
  | leaf x => cases b; exact parallelogram _ _
  | node l r hl hr =>
    cases b with
    | node c d =>
      simp only [energy, zip]
      have h1 := hl c
      have h2 := hr d
      omega

theorem transform_energy (t : Tree n) :
    energy (transform t) = (2^n : Nat) * energy t := by
  induction t with
  | leaf a => simp [transform, energy]
  | @node n l r hl hr =>
    simp only [transform, energy]
    rw [zip_energy, hl, hr]
    simp only [Nat.pow_succ, Int.natCast_mul]
    simp [← Int.mul_add, Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]

theorem energy_eq_sumDomain (t : Tree n) :
    energy t = sumDomain (fun u => lookup t u * lookup t u) := by
  induction t with
  | leaf a => rfl
  | node l r hl hr => simp [energy, sumDomain, lookup, hl, hr]

theorem energy_tabulate (f : BitVec n → Int) :
    energy (tabulate f) = sumDomain (fun x => f x * f x) := by
  induction n with
  | zero => rfl
  | succ n ih => simp [tabulate, energy, sumDomain, ih]

theorem sumDomain_const (c : Int) : sumDomain (fun _ : BitVec n => c) = (2^n : Nat)*c := by
  induction n with
  | zero => simp [sumDomain]
  | succ n ih =>
    simp only [sumDomain, ih, Nat.pow_succ, Int.natCast_mul]
    change (↑(2^n : Nat) : Int)*c + (↑(2^n : Nat) : Int)*c = ((↑(2^n : Nat) : Int)*2)*c
    rw [Int.mul_comm (↑(2^n : Nat) : Int) 2, Int.mul_assoc]
    omega

/-- Parseval for exactly the original finite integer Walsh definition. -/
theorem walsh_parseval (f : BitVec n → BitVec m) (b : BitVec m) :
    sumDomain (fun u => walsh f b u * walsh f b u) =
      (2^n : Nat) * (2^n : Nat) := by
  simp only [← fastWalsh_correct]
  rw [← energy_eq_sumDomain]
  unfold fastWalsh
  rw [transform_energy, energy_tabulate]
  have hs : (fun x : BitVec n => signed (binaryDot b (f x)) 1 * signed (binaryDot b (f x)) 1) =
      (fun _ => (1 : Int)) := by
    funext x
    cases binaryDot b (f x) <;> decide
  rw [hs, sumDomain_const]
  simp

/-- The full nondegenerate-quadratic bent theorem, with no zero-sum hypothesis.
The only hypothesis is the concrete n squared polar/inverse basis certificate. -/
theorem quadratic_bent_of_basis
    (cs : List (Nat × Nat × BitVec m)) (b : BitVec m)
    (columns : List (Nat × BitVec n))
    (hcheck : ∀ e ∈ basis n, ∀ d ∈ basis n,
      coefficientPolar cs b (columnMap columns e) d = binaryDot e d) :
    IsBent (quadratic cs : BitVec n → BitVec m) b := by
  have hconst : ∀ u : BitVec n,
      walsh (quadratic cs) b u * walsh (quadratic cs) b u =
      walsh (quadratic cs) b (0 : BitVec n) * walsh (quadratic cs) b (0 : BitVec n) := by
    intro u
    rw [quadratic_walsh_shift_of_basis cs b columns hcheck u]
    cases quadraticComponent cs b (columnMap columns u) <;> simp [signed, Int.neg_mul_neg]
  have hp := walsh_parseval (quadratic cs : BitVec n → BitVec m) b
  simp only [hconst, sumDomain_const] at hp
  have hn : (↑(2^n : Nat) : Int) ≠ 0 := by
    have h : 0 < (2^n : Nat) := Nat.pow_pos (by decide)
    omega
  have hz := Int.eq_of_mul_eq_mul_left hn hp
  exact quadratic_bent_of_basis_and_zero cs b columns hcheck hz

theorem quadratic_bent_certificate
    (cs : List (Nat × Nat × BitVec m)) (b : BitVec m)
    (columns : List (Nat × BitVec n))
    (hcheck : basisAlignmentCheck cs b columns = true) :
    IsBent (quadratic cs : BitVec n → BitVec m) b :=
  quadratic_bent_of_basis cs b columns ((basisAlignmentCheck_correct cs b columns).mp hcheck)

#print axioms walsh_parseval
#print axioms quadratic_bent_certificate
end QuadraticWalshParseval
