import QuadraticFourRadicalRaw
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
namespace QuadraticFourRaw
theorem classified011000 : ∀ g h i j k : F,
    classified 0 1 1 0 0 0 g h i j k := by decide

theorem classified011001 : ∀ g h i j k : F,
    classified 0 1 1 0 0 1 g h i j k := by decide

theorem classified011010 : ∀ g h i j k : F,
    classified 0 1 1 0 1 0 g h i j k := by decide

theorem classified011011 : ∀ g h i j k : F,
    classified 0 1 1 0 1 1 g h i j k := by decide

theorem classified011100 : ∀ g h i j k : F,
    classified 0 1 1 1 0 0 g h i j k := by decide

theorem classified011101 : ∀ g h i j k : F,
    classified 0 1 1 1 0 1 g h i j k := by decide

theorem classified011110 : ∀ g h i j k : F,
    classified 0 1 1 1 1 0 g h i j k := by decide

theorem classified011111 : ∀ g h i j k : F,
    classified 0 1 1 1 1 1 g h i j k := by decide

end QuadraticFourRaw
