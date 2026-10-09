import QuadraticFourRadicalRaw
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
namespace QuadraticFourRaw
theorem classified001000 : ∀ g h i j k : F,
    classified 0 0 1 0 0 0 g h i j k := by decide

theorem classified001001 : ∀ g h i j k : F,
    classified 0 0 1 0 0 1 g h i j k := by decide

theorem classified001010 : ∀ g h i j k : F,
    classified 0 0 1 0 1 0 g h i j k := by decide

theorem classified001011 : ∀ g h i j k : F,
    classified 0 0 1 0 1 1 g h i j k := by decide

theorem classified001100 : ∀ g h i j k : F,
    classified 0 0 1 1 0 0 g h i j k := by decide

theorem classified001101 : ∀ g h i j k : F,
    classified 0 0 1 1 0 1 g h i j k := by decide

theorem classified001110 : ∀ g h i j k : F,
    classified 0 0 1 1 1 0 g h i j k := by decide

theorem classified001111 : ∀ g h i j k : F,
    classified 0 0 1 1 1 1 g h i j k := by decide

end QuadraticFourRaw
