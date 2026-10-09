import QuadraticFourRadicalRaw
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
namespace QuadraticFourRaw
theorem classified010000 : ∀ g h i j k : F,
    classified 0 1 0 0 0 0 g h i j k := by decide

theorem classified010001 : ∀ g h i j k : F,
    classified 0 1 0 0 0 1 g h i j k := by decide

theorem classified010010 : ∀ g h i j k : F,
    classified 0 1 0 0 1 0 g h i j k := by decide

theorem classified010011 : ∀ g h i j k : F,
    classified 0 1 0 0 1 1 g h i j k := by decide

theorem classified010100 : ∀ g h i j k : F,
    classified 0 1 0 1 0 0 g h i j k := by decide

theorem classified010101 : ∀ g h i j k : F,
    classified 0 1 0 1 0 1 g h i j k := by decide

theorem classified010110 : ∀ g h i j k : F,
    classified 0 1 0 1 1 0 g h i j k := by decide

theorem classified010111 : ∀ g h i j k : F,
    classified 0 1 0 1 1 1 g h i j k := by decide

end QuadraticFourRaw
