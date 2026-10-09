import QuadraticFourPairRaw
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
namespace QuadraticFourRaw
theorem pair011000 : ∀ F G H I J K : QuadraticFourRaw.F,
    pairProperty 0 1 1 0 0 0 F G H I J K := by decide

theorem pair011001 : ∀ F G H I J K : QuadraticFourRaw.F,
    pairProperty 0 1 1 0 0 1 F G H I J K := by decide

theorem pair011010 : ∀ F G H I J K : QuadraticFourRaw.F,
    pairProperty 0 1 1 0 1 0 F G H I J K := by decide

theorem pair011011 : ∀ F G H I J K : QuadraticFourRaw.F,
    pairProperty 0 1 1 0 1 1 F G H I J K := by decide

theorem pair011100 : ∀ F G H I J K : QuadraticFourRaw.F,
    pairProperty 0 1 1 1 0 0 F G H I J K := by decide

theorem pair011101 : ∀ F G H I J K : QuadraticFourRaw.F,
    pairProperty 0 1 1 1 0 1 F G H I J K := by decide

theorem pair011110 : ∀ F G H I J K : QuadraticFourRaw.F,
    pairProperty 0 1 1 1 1 0 F G H I J K := by decide

theorem pair011111 : ∀ F G H I J K : QuadraticFourRaw.F,
    pairProperty 0 1 1 1 1 1 F G H I J K := by decide

end QuadraticFourRaw
