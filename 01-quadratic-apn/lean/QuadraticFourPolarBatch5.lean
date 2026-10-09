import QuadraticFourRadicalRaw
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
namespace QuadraticFourRaw
theorem classified101000 : ∀ g h i j k : F,
    classified 1 0 1 0 0 0 g h i j k := by decide

theorem classified101001 : ∀ g h i j k : F,
    classified 1 0 1 0 0 1 g h i j k := by decide

theorem classified101010 : ∀ g h i j k : F,
    classified 1 0 1 0 1 0 g h i j k := by decide

theorem classified101011 : ∀ g h i j k : F,
    classified 1 0 1 0 1 1 g h i j k := by decide

theorem classified101100 : ∀ g h i j k : F,
    classified 1 0 1 1 0 0 g h i j k := by decide

theorem classified101101 : ∀ g h i j k : F,
    classified 1 0 1 1 0 1 g h i j k := by decide

theorem classified101110 : ∀ g h i j k : F,
    classified 1 0 1 1 1 0 g h i j k := by decide

theorem classified101111 : ∀ g h i j k : F,
    classified 1 0 1 1 1 1 g h i j k := by decide

end QuadraticFourRaw
