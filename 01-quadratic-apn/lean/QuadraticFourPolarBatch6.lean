import QuadraticFourRadicalRaw
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
namespace QuadraticFourRaw
theorem classified110000 : ∀ g h i j k : F,
    classified 1 1 0 0 0 0 g h i j k := by decide

theorem classified110001 : ∀ g h i j k : F,
    classified 1 1 0 0 0 1 g h i j k := by decide

theorem classified110010 : ∀ g h i j k : F,
    classified 1 1 0 0 1 0 g h i j k := by decide

theorem classified110011 : ∀ g h i j k : F,
    classified 1 1 0 0 1 1 g h i j k := by decide

theorem classified110100 : ∀ g h i j k : F,
    classified 1 1 0 1 0 0 g h i j k := by decide

theorem classified110101 : ∀ g h i j k : F,
    classified 1 1 0 1 0 1 g h i j k := by decide

theorem classified110110 : ∀ g h i j k : F,
    classified 1 1 0 1 1 0 g h i j k := by decide

theorem classified110111 : ∀ g h i j k : F,
    classified 1 1 0 1 1 1 g h i j k := by decide

end QuadraticFourRaw
