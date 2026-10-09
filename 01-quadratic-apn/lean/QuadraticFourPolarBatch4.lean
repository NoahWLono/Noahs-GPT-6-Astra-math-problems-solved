import QuadraticFourRadicalRaw
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
namespace QuadraticFourRaw
theorem classified100000 : ∀ g h i j k : F,
    classified 1 0 0 0 0 0 g h i j k := by decide

theorem classified100001 : ∀ g h i j k : F,
    classified 1 0 0 0 0 1 g h i j k := by decide

theorem classified100010 : ∀ g h i j k : F,
    classified 1 0 0 0 1 0 g h i j k := by decide

theorem classified100011 : ∀ g h i j k : F,
    classified 1 0 0 0 1 1 g h i j k := by decide

theorem classified100100 : ∀ g h i j k : F,
    classified 1 0 0 1 0 0 g h i j k := by decide

theorem classified100101 : ∀ g h i j k : F,
    classified 1 0 0 1 0 1 g h i j k := by decide

theorem classified100110 : ∀ g h i j k : F,
    classified 1 0 0 1 1 0 g h i j k := by decide

theorem classified100111 : ∀ g h i j k : F,
    classified 1 0 0 1 1 1 g h i j k := by decide

end QuadraticFourRaw
