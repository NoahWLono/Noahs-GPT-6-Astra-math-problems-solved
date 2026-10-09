import QuadraticFourPairRaw
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
namespace QuadraticFourRaw
theorem pair000000 : ∀ F G H I J K : QuadraticFourRaw.F,
    pairProperty 0 0 0 0 0 0 F G H I J K := by decide

theorem pair000001 : ∀ F G H I J K : QuadraticFourRaw.F,
    pairProperty 0 0 0 0 0 1 F G H I J K := by decide

theorem pair000010 : ∀ F G H I J K : QuadraticFourRaw.F,
    pairProperty 0 0 0 0 1 0 F G H I J K := by decide

theorem pair000011 : ∀ F G H I J K : QuadraticFourRaw.F,
    pairProperty 0 0 0 0 1 1 F G H I J K := by decide

theorem pair000100 : ∀ F G H I J K : QuadraticFourRaw.F,
    pairProperty 0 0 0 1 0 0 F G H I J K := by decide

theorem pair000101 : ∀ F G H I J K : QuadraticFourRaw.F,
    pairProperty 0 0 0 1 0 1 F G H I J K := by decide

theorem pair000110 : ∀ F G H I J K : QuadraticFourRaw.F,
    pairProperty 0 0 0 1 1 0 F G H I J K := by decide

theorem pair000111 : ∀ F G H I J K : QuadraticFourRaw.F,
    pairProperty 0 0 0 1 1 1 F G H I J K := by decide

end QuadraticFourRaw
