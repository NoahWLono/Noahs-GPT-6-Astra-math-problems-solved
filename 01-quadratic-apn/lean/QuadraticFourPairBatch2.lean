import QuadraticFourPairRaw
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
namespace QuadraticFourRaw
theorem pair010000 : ∀ F G H I J K : QuadraticFourRaw.F,
    pairProperty 0 1 0 0 0 0 F G H I J K := by decide

theorem pair010001 : ∀ F G H I J K : QuadraticFourRaw.F,
    pairProperty 0 1 0 0 0 1 F G H I J K := by decide

theorem pair010010 : ∀ F G H I J K : QuadraticFourRaw.F,
    pairProperty 0 1 0 0 1 0 F G H I J K := by decide

theorem pair010011 : ∀ F G H I J K : QuadraticFourRaw.F,
    pairProperty 0 1 0 0 1 1 F G H I J K := by decide

theorem pair010100 : ∀ F G H I J K : QuadraticFourRaw.F,
    pairProperty 0 1 0 1 0 0 F G H I J K := by decide

theorem pair010101 : ∀ F G H I J K : QuadraticFourRaw.F,
    pairProperty 0 1 0 1 0 1 F G H I J K := by decide

theorem pair010110 : ∀ F G H I J K : QuadraticFourRaw.F,
    pairProperty 0 1 0 1 1 0 F G H I J K := by decide

theorem pair010111 : ∀ F G H I J K : QuadraticFourRaw.F,
    pairProperty 0 1 0 1 1 1 F G H I J K := by decide

end QuadraticFourRaw
