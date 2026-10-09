import QuadraticFourPairRaw
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
namespace QuadraticFourRaw
theorem pair111000 : ∀ F G H I J K : QuadraticFourRaw.F,
    pairProperty 1 1 1 0 0 0 F G H I J K := by decide

theorem pair111001 : ∀ F G H I J K : QuadraticFourRaw.F,
    pairProperty 1 1 1 0 0 1 F G H I J K := by decide

theorem pair111010 : ∀ F G H I J K : QuadraticFourRaw.F,
    pairProperty 1 1 1 0 1 0 F G H I J K := by decide

theorem pair111011 : ∀ F G H I J K : QuadraticFourRaw.F,
    pairProperty 1 1 1 0 1 1 F G H I J K := by decide

theorem pair111100 : ∀ F G H I J K : QuadraticFourRaw.F,
    pairProperty 1 1 1 1 0 0 F G H I J K := by decide

theorem pair111101 : ∀ F G H I J K : QuadraticFourRaw.F,
    pairProperty 1 1 1 1 0 1 F G H I J K := by decide

theorem pair111110 : ∀ F G H I J K : QuadraticFourRaw.F,
    pairProperty 1 1 1 1 1 0 F G H I J K := by decide

theorem pair111111 : ∀ F G H I J K : QuadraticFourRaw.F,
    pairProperty 1 1 1 1 1 1 F G H I J K := by decide

end QuadraticFourRaw
