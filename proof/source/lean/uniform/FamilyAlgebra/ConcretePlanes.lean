import FamilyAlgebra.PfaffianExpansion

namespace FamilyAlgebra
variable {E : Type*} [Field E]

def bit (b : Bool) : E := if b then 1 else 0

theorem bit_xor (two_zero : (2 : E) = 0) (b c : Bool) :
    bit (b ^^ c) = (bit b : E) + bit c := by
  have h : (1:E)+1=0 := by simpa only [one_add_one_eq_two] using two_zero
  cases b <;> cases c <;> simp [bit, h]

theorem bit_and (b c : Bool) : bit (b && c) = (bit b : E)*bit c := by
  cases b <;> cases c <;> simp [bit]

def liftSix (x : Six) : Pfaffian.Coordinates E := fun i =>
  match i.val with
  | 0 => bit x.a
  | 1 => bit x.b
  | 2 => bit x.c
  | 3 => bit x.d
  | 4 => bit x.f
  | _ => bit x.g

theorem lift_pf (two_zero : (2 : E) = 0) (x : Six) :
    Pfaffian.pf (liftSix x : Pfaffian.Coordinates E) = bit (q x) := by
  simp only [q, bit_xor two_zero, bit_and]
  rfl

theorem lift_add (two_zero : (2 : E) = 0) (x y : Six) :
    liftSix (add x y) = Pfaffian.plus (liftSix x : Pfaffian.Coordinates E) (liftSix y) := by
  funext i
  rcases i with ⟨i, hi⟩
  match i with
  | 0 | 1 | 2 | 3 | 4 | 5 => simp [liftSix, add, Pfaffian.plus, bit_xor two_zero]
  | i+6 => omega

theorem double_zero (two_zero : (2 : E) = 0) (a : E) : a+a=0 := by
  rw [← two_mul, two_zero, zero_mul]

theorem lift_polar (two_zero : (2 : E) = 0) (x y : Six) :
    Pfaffian.polar (liftSix x : Pfaffian.Coordinates E) (liftSix y) = bit (beta x y) := by
  have h := Pfaffian.pf_plus (liftSix x : Pfaffian.Coordinates E) (liftSix y)
  rw [← lift_add two_zero, lift_pf two_zero, lift_pf two_zero, lift_pf two_zero] at h
  simp only [beta, bit_xor two_zero]
  rw [h]
  have hx := double_zero two_zero (bit (q x))
  have hy := double_zero two_zero (bit (q y))
  calc
    Pfaffian.polar (liftSix x) (liftSix y) =
        ((bit (q x) + bit (q x)) + (bit (q y) + bit (q y))) +
          Pfaffian.polar (liftSix x) (liftSix y) := by rw [hx, hy]; simp
    _ = (bit (q x) + bit (q y) + Pfaffian.polar (liftSix x) (liftSix y) + bit (q x)) + bit (q y) := by ac_rfl

/-- Concrete parity-specific binary coefficient family, with the base at zero. -/
def family (u v w z : Bool) (s t : Nat → Bool) (j : Nat) : Six :=
  if j = 0 then base u v w z
  else if j % 2 = 1 then oddPlane (s j) (t j)
  else evenPlane (s j) (t j)

theorem family_diag (u v w z : Bool) (s t : Nat → Bool) (j : Nat) (hj : 0 < j) :
    q (family u v w z s t j) = (s j || t j) := by
  simp only [family, show ¬j=0 by omega, if_false]
  split <;> simp [odd_anisotropic, even_anisotropic]

theorem family_odd_pair (u v w z : Bool) (s t : Nat → Bool)
    (i j : Nat) (hij : i < j) (hodd : (i+j)%2 = 1) :
    beta (family u v w z s t i) (family u v w z s t j) = false := by
  have hj : ¬j=0 := by omega
  by_cases hi : i=0
  · subst i
    have hjodd : j%2=1 := by omega
    simp [family, hj, hjodd, base_odd_orthogonal]
  · by_cases hio : i%2=1
    · have hje : ¬j%2=1 := by omega
      simp [family, hi, hj, hio, hje, odd_even_orthogonal]
    · have hjo : j%2=1 := by omega
      simp only [family, hi, hj, hio, hjo, if_false, if_true]
      rw [beta_symmetric, odd_even_orthogonal]

theorem beta_zero_right (x : Six) :
    beta x ⟨false,false,false,false,false,false⟩ = false := by
  rcases x with ⟨a,b,c,d,f,g⟩
  simp [beta, add, q]

theorem family_pair_vanish (u v w z : Bool) (s t : Nat → Bool)
    (i j : Nat) (hj : 0 < j) (inactive : (s j || t j) = false) :
    beta (family u v w z s t i) (family u v w z s t j) = false := by
  have hs : s j = false := by cases h : s j <;> simp_all
  have ht : t j = false := by cases h : t j <;> simp_all
  have hz : family u v w z s t j = ⟨false,false,false,false,false,false⟩ := by
    simp [family, show ¬j=0 by omega, hs, ht, oddPlane, evenPlane]
  rw [hz, beta_zero_right]

#print axioms family_odd_pair
#print axioms lift_polar
end FamilyAlgebra
