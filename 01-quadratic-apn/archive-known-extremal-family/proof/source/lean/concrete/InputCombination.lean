import Quadratic
namespace FastWalsh

theorem binaryDot_comm (x y : BitVec n) : binaryDot x y = binaryDot y x := by
  unfold binaryDot
  apply foldl_congr
  intro i hi a
  simp only [Bool.and_comm]

theorem binaryDot_xor_left (b c x : BitVec n) :
    binaryDot (b ^^^ c) x = (binaryDot b x ^^ binaryDot c x) := by
  rw [binaryDot_comm, binaryDot_xor_right]
  rw [binaryDot_comm x b, binaryDot_comm x c]

theorem signed_mul (b c : Bool) : signed (b ^^ c) 1 = signed b 1 * signed c 1 := by
  cases b <;> cases c <;> decide

theorem tabulate_zip (op : Int → Int → Int) (f g : BitVec n → Int) :
    tabulate (fun x => op (f x) (g x)) = zip op (tabulate f) (tabulate g) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [tabulate, zip, ih]

def signTree {n m : Nat} (f : BitVec n → BitVec m) (b : BitVec m) : Tree n :=
  tabulate (fun x => signed (binaryDot b (f x)) 1)

theorem signTree_xor {n m : Nat} (f : BitVec n → BitVec m) (b c : BitVec m) :
    signTree f (b ^^^ c) = zip (· * ·) (signTree f b) (signTree f c) := by
  unfold signTree
  simp only [binaryDot_xor_left, signed_mul, tabulate_zip]

theorem signTree_zero {n m : Nat} (f : BitVec n → BitVec m) :
    signTree f 0 = tabulate (fun _ : BitVec n => 1) := by
  unfold signTree
  have h (x : BitVec m) : binaryDot 0 x = false := by rw [binaryDot_comm]; exact binaryDot_zero x
  simp only [h, signed, Bool.false_eq_true, ↓reduceIte]

#print axioms signTree_xor
end FastWalsh
