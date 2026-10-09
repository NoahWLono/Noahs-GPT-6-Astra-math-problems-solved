import QuadraticFourPairRaw
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
namespace QuadraticFourRaw
theorem pair101000 : ∀ F G H I J K : QuadraticFourRaw.F,
    pairProperty 1 0 1 0 0 0 F G H I J K := by decide

theorem pair101001 : ∀ F G H I J K : QuadraticFourRaw.F,
    pairProperty 1 0 1 0 0 1 F G H I J K := by decide

theorem pair101010 : ∀ F G H I J K : QuadraticFourRaw.F,
    pairProperty 1 0 1 0 1 0 F G H I J K := by decide

theorem pair101011 : ∀ F G H I J K : QuadraticFourRaw.F,
    pairProperty 1 0 1 0 1 1 F G H I J K := by decide

theorem pair101100 : ∀ F G H I J K : QuadraticFourRaw.F,
    pairProperty 1 0 1 1 0 0 F G H I J K := by decide

theorem pair101101 : ∀ F G H I J K : QuadraticFourRaw.F,
    pairProperty 1 0 1 1 0 1 F G H I J K := by decide

theorem pair101110 : ∀ F G H I J K : QuadraticFourRaw.F,
    pairProperty 1 0 1 1 1 0 F G H I J K := by decide

theorem pair101111 : ∀ F G H I J K : QuadraticFourRaw.F,
    pairProperty 1 0 1 1 1 1 F G H I J K := by decide

end QuadraticFourRaw
