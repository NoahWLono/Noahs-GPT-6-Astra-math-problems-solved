import QuadraticFourRadicalRaw
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
namespace QuadraticFourRaw
theorem classified111000 : ∀ g h i j k : F,
    classified 1 1 1 0 0 0 g h i j k := by decide

theorem classified111001 : ∀ g h i j k : F,
    classified 1 1 1 0 0 1 g h i j k := by decide

theorem classified111010 : ∀ g h i j k : F,
    classified 1 1 1 0 1 0 g h i j k := by decide

theorem classified111011 : ∀ g h i j k : F,
    classified 1 1 1 0 1 1 g h i j k := by decide

theorem classified111100 : ∀ g h i j k : F,
    classified 1 1 1 1 0 0 g h i j k := by decide

theorem classified111101 : ∀ g h i j k : F,
    classified 1 1 1 1 0 1 g h i j k := by decide

theorem classified111110 : ∀ g h i j k : F,
    classified 1 1 1 1 1 0 g h i j k := by decide

theorem classified111111 : ∀ g h i j k : F,
    classified 1 1 1 1 1 1 g h i j k := by decide

end QuadraticFourRaw
