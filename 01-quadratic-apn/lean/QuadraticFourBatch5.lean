import QuadraticFourRaw
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
namespace QuadraticFourRaw
theorem weights101000 : ∀ g h i j k : F,
    weight (poly 1 0 1 0 0 0 g h i j k) ∈ ({0,4,6,8,10,12,16} : Finset ℕ) := by decide

theorem weights101001 : ∀ g h i j k : F,
    weight (poly 1 0 1 0 0 1 g h i j k) ∈ ({0,4,6,8,10,12,16} : Finset ℕ) := by decide

theorem weights101010 : ∀ g h i j k : F,
    weight (poly 1 0 1 0 1 0 g h i j k) ∈ ({0,4,6,8,10,12,16} : Finset ℕ) := by decide

theorem weights101011 : ∀ g h i j k : F,
    weight (poly 1 0 1 0 1 1 g h i j k) ∈ ({0,4,6,8,10,12,16} : Finset ℕ) := by decide

theorem weights101100 : ∀ g h i j k : F,
    weight (poly 1 0 1 1 0 0 g h i j k) ∈ ({0,4,6,8,10,12,16} : Finset ℕ) := by decide

theorem weights101101 : ∀ g h i j k : F,
    weight (poly 1 0 1 1 0 1 g h i j k) ∈ ({0,4,6,8,10,12,16} : Finset ℕ) := by decide

theorem weights101110 : ∀ g h i j k : F,
    weight (poly 1 0 1 1 1 0 g h i j k) ∈ ({0,4,6,8,10,12,16} : Finset ℕ) := by decide

theorem weights101111 : ∀ g h i j k : F,
    weight (poly 1 0 1 1 1 1 g h i j k) ∈ ({0,4,6,8,10,12,16} : Finset ℕ) := by decide

end QuadraticFourRaw
