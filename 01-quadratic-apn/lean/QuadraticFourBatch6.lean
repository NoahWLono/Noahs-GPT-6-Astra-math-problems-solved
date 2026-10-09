import QuadraticFourRaw
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
namespace QuadraticFourRaw
theorem weights110000 : ∀ g h i j k : F,
    weight (poly 1 1 0 0 0 0 g h i j k) ∈ ({0,4,6,8,10,12,16} : Finset ℕ) := by decide

theorem weights110001 : ∀ g h i j k : F,
    weight (poly 1 1 0 0 0 1 g h i j k) ∈ ({0,4,6,8,10,12,16} : Finset ℕ) := by decide

theorem weights110010 : ∀ g h i j k : F,
    weight (poly 1 1 0 0 1 0 g h i j k) ∈ ({0,4,6,8,10,12,16} : Finset ℕ) := by decide

theorem weights110011 : ∀ g h i j k : F,
    weight (poly 1 1 0 0 1 1 g h i j k) ∈ ({0,4,6,8,10,12,16} : Finset ℕ) := by decide

theorem weights110100 : ∀ g h i j k : F,
    weight (poly 1 1 0 1 0 0 g h i j k) ∈ ({0,4,6,8,10,12,16} : Finset ℕ) := by decide

theorem weights110101 : ∀ g h i j k : F,
    weight (poly 1 1 0 1 0 1 g h i j k) ∈ ({0,4,6,8,10,12,16} : Finset ℕ) := by decide

theorem weights110110 : ∀ g h i j k : F,
    weight (poly 1 1 0 1 1 0 g h i j k) ∈ ({0,4,6,8,10,12,16} : Finset ℕ) := by decide

theorem weights110111 : ∀ g h i j k : F,
    weight (poly 1 1 0 1 1 1 g h i j k) ∈ ({0,4,6,8,10,12,16} : Finset ℕ) := by decide

end QuadraticFourRaw
