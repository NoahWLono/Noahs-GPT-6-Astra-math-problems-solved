import OutputExtension
open FastWalsh QuadraticWalshShift
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12
def coefficients : List (Nat × Nat × BitVec 8) := [(0, 1, 0), (0, 2, 0), (0, 3, 3), (0, 4, 0), (0, 5, 48), (0, 6, 1), (0, 7, 128), (0, 8, 16), (0, 9, 4), (0, 10, 192), (0, 11, 0), (1, 2, 0), (1, 3, 0), (1, 4, 48), (1, 5, 3), (1, 6, 128), (1, 7, 16), (1, 8, 129), (1, 9, 192), (1, 10, 0), (1, 11, 196), (2, 3, 48), (2, 4, 3), (2, 5, 48), (2, 6, 16), (2, 7, 129), (2, 8, 144), (2, 9, 0), (2, 10, 196), (2, 11, 192), (3, 4, 0), (3, 5, 0), (3, 6, 8), (3, 7, 64), (3, 8, 0), (3, 9, 2), (3, 10, 128), (3, 11, 16), (4, 5, 0), (4, 6, 64), (4, 7, 0), (4, 8, 72), (4, 9, 128), (4, 10, 16), (4, 11, 130), (5, 6, 0), (5, 7, 72), (5, 8, 64), (5, 9, 16), (5, 10, 130), (5, 11, 144), (6, 7, 0), (6, 8, 0), (6, 9, 3), (6, 10, 0), (6, 11, 32), (7, 8, 0), (7, 9, 0), (7, 10, 32), (7, 11, 3), (8, 9, 32), (8, 10, 3), (8, 11, 32), (9, 10, 0), (9, 11, 0), (10, 11, 0)]
def effective : BitVec 12 → BitVec 8 := quadratic coefficients
def F : BitVec 12 → BitVec 12 := zeroExtend (zeroExtend (zeroExtend (zeroExtend effective)))
def fullCoefficients := liftCoefficients (liftCoefficients (liftCoefficients (liftCoefficients coefficients)))

theorem F_eq_quadratic : F = quadratic fullCoefficients := by
  simp only [F, effective, quadratic_zeroExtend, fullCoefficients]

def IsHomogeneousQuadratic {n m : Nat} (f : BitVec n → BitVec m) : Prop :=
  ∃ cs : List (Nat × Nat × BitVec m),
    (∀ c ∈ cs, c.1 < c.2.1 ∧ c.2.1 < n) ∧ f = quadratic cs

theorem F_quadratic : IsHomogeneousQuadratic F := by
  refine ⟨fullCoefficients, ?_, F_eq_quadratic⟩
  decide

def IsAffine {n m : Nat} (f : BitVec n → BitVec m) : Prop :=
  ∀ x y, f (x ^^^ y) = (f x ^^^ f y ^^^ f 0)

theorem F_nonaffine : ¬ IsAffine F := by
  intro h
  have hn : F ((1 : BitVec 12) ^^^ 8) ≠ (F 1 ^^^ F 8 ^^^ F 0) := by decide
  exact hn (h 1 8)

theorem F_bent_iff (b : BitVec 12) : IsBent F b ↔ IsBent effective (b.setWidth 8) := by
  simp [F, isBent_zeroExtend]

def embed (p : Nat) (x : BitVec 8) : BitVec 12 :=
  BitVec.cons (p.testBit 3) (BitVec.cons (p.testBit 2) (BitVec.cons (p.testBit 1) (BitVec.cons (p.testBit 0) x)))
end N12
