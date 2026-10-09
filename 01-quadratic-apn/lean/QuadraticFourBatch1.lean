import QuadraticFourRaw
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
namespace QuadraticFourRaw
theorem weights001000 : ∀ g h i j k : F,
    weight (poly 0 0 1 0 0 0 g h i j k) ∈ ({0,4,6,8,10,12,16} : Finset ℕ) := by decide

theorem weights001001 : ∀ g h i j k : F,
    weight (poly 0 0 1 0 0 1 g h i j k) ∈ ({0,4,6,8,10,12,16} : Finset ℕ) := by decide

theorem weights001010 : ∀ g h i j k : F,
    weight (poly 0 0 1 0 1 0 g h i j k) ∈ ({0,4,6,8,10,12,16} : Finset ℕ) := by decide

theorem weights001011 : ∀ g h i j k : F,
    weight (poly 0 0 1 0 1 1 g h i j k) ∈ ({0,4,6,8,10,12,16} : Finset ℕ) := by decide

theorem weights001100 : ∀ g h i j k : F,
    weight (poly 0 0 1 1 0 0 g h i j k) ∈ ({0,4,6,8,10,12,16} : Finset ℕ) := by decide

theorem weights001101 : ∀ g h i j k : F,
    weight (poly 0 0 1 1 0 1 g h i j k) ∈ ({0,4,6,8,10,12,16} : Finset ℕ) := by decide

theorem weights001110 : ∀ g h i j k : F,
    weight (poly 0 0 1 1 1 0 g h i j k) ∈ ({0,4,6,8,10,12,16} : Finset ℕ) := by decide

theorem weights001111 : ∀ g h i j k : F,
    weight (poly 0 0 1 1 1 1 g h i j k) ∈ ({0,4,6,8,10,12,16} : Finset ℕ) := by decide

end QuadraticFourRaw
