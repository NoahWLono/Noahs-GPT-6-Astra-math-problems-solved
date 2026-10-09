import QuadraticFourRadicalRaw
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
namespace QuadraticFourRaw

def representative (f g h i j k : F) : V → F :=
  poly 1
    (1 + radicalIndicator f g h i j k ![1,0,0,0])
    (1 + radicalIndicator f g h i j k ![0,1,0,0])
    (1 + radicalIndicator f g h i j k ![0,0,1,0])
    (1 + radicalIndicator f g h i j k ![0,0,0,1]) f g h i j k

theorem representative_eq : ∀ f g h i j k : F, radicalCard f g h i j k = 4 →
    representative f g h i j k = radicalIndicator f g h i j k := by
  intro f g h
  fin_cases f <;> fin_cases g <;> fin_cases h <;> decide

theorem representative_cost : ∀ f g h i j k : F, radicalCard f g h i j k = 4 →
    cost (representative f g h i j k) = 2 := by
  intro f g h
  fin_cases f <;> fin_cases g <;> fin_cases h <;> decide

end QuadraticFourRaw
