import QuadraticFourPairRaw
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
namespace QuadraticFourRaw
theorem pair110000 : ∀ F G H I J K : QuadraticFourRaw.F,
    pairProperty 1 1 0 0 0 0 F G H I J K := by decide

theorem pair110001 : ∀ F G H I J K : QuadraticFourRaw.F,
    pairProperty 1 1 0 0 0 1 F G H I J K := by decide

theorem pair110010 : ∀ F G H I J K : QuadraticFourRaw.F,
    pairProperty 1 1 0 0 1 0 F G H I J K := by decide

theorem pair110011 : ∀ F G H I J K : QuadraticFourRaw.F,
    pairProperty 1 1 0 0 1 1 F G H I J K := by decide

theorem pair110100 : ∀ F G H I J K : QuadraticFourRaw.F,
    pairProperty 1 1 0 1 0 0 F G H I J K := by decide

theorem pair110101 : ∀ F G H I J K : QuadraticFourRaw.F,
    pairProperty 1 1 0 1 0 1 F G H I J K := by decide

theorem pair110110 : ∀ F G H I J K : QuadraticFourRaw.F,
    pairProperty 1 1 0 1 1 0 F G H I J K := by decide

theorem pair110111 : ∀ F G H I J K : QuadraticFourRaw.F,
    pairProperty 1 1 0 1 1 1 F G H I J K := by decide

end QuadraticFourRaw
