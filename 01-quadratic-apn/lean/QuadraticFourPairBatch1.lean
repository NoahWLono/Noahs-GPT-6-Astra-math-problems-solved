import QuadraticFourPairRaw
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
namespace QuadraticFourRaw
theorem pair001000 : ∀ F G H I J K : QuadraticFourRaw.F,
    pairProperty 0 0 1 0 0 0 F G H I J K := by decide

theorem pair001001 : ∀ F G H I J K : QuadraticFourRaw.F,
    pairProperty 0 0 1 0 0 1 F G H I J K := by decide

theorem pair001010 : ∀ F G H I J K : QuadraticFourRaw.F,
    pairProperty 0 0 1 0 1 0 F G H I J K := by decide

theorem pair001011 : ∀ F G H I J K : QuadraticFourRaw.F,
    pairProperty 0 0 1 0 1 1 F G H I J K := by decide

theorem pair001100 : ∀ F G H I J K : QuadraticFourRaw.F,
    pairProperty 0 0 1 1 0 0 F G H I J K := by decide

theorem pair001101 : ∀ F G H I J K : QuadraticFourRaw.F,
    pairProperty 0 0 1 1 0 1 F G H I J K := by decide

theorem pair001110 : ∀ F G H I J K : QuadraticFourRaw.F,
    pairProperty 0 0 1 1 1 0 F G H I J K := by decide

theorem pair001111 : ∀ F G H I J K : QuadraticFourRaw.F,
    pairProperty 0 0 1 1 1 1 F G H I J K := by decide

end QuadraticFourRaw
