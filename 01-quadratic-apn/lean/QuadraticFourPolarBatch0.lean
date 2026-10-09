import QuadraticFourRadicalRaw
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
namespace QuadraticFourRaw
theorem classified000000 : ∀ g h i j k : F,
    classified 0 0 0 0 0 0 g h i j k := by decide

theorem classified000001 : ∀ g h i j k : F,
    classified 0 0 0 0 0 1 g h i j k := by decide

theorem classified000010 : ∀ g h i j k : F,
    classified 0 0 0 0 1 0 g h i j k := by decide

theorem classified000011 : ∀ g h i j k : F,
    classified 0 0 0 0 1 1 g h i j k := by decide

theorem classified000100 : ∀ g h i j k : F,
    classified 0 0 0 1 0 0 g h i j k := by decide

theorem classified000101 : ∀ g h i j k : F,
    classified 0 0 0 1 0 1 g h i j k := by decide

theorem classified000110 : ∀ g h i j k : F,
    classified 0 0 0 1 1 0 g h i j k := by decide

theorem classified000111 : ∀ g h i j k : F,
    classified 0 0 0 1 1 1 g h i j k := by decide

end QuadraticFourRaw
