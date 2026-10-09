import QuadraticFourRadicalRaw
namespace QuadraticFourRaw

def pairProperty (f g h i j k F G H I J K : QuadraticFourRaw.F) : Prop :=
  radicalCard f g h i j k = 4 → radicalCard F G H I J K = 4 →
    radicalCard (f+F) (g+G) (h+H) (i+I) (j+J) (k+K) = 4 →
      (Finset.univ.filter (fun x : V => inRadical f g h i j k x ∧ inRadical F G H I J K x)).card = 2 ∧
      ∃ x : V, radicalIndicator f g h i j k x + radicalIndicator F G H I J K x +
        radicalIndicator (f+F) (g+G) (h+H) (i+I) (j+J) (k+K) x = 0

instance (f g h i j k F G H I J K : QuadraticFourRaw.F) :
    Decidable (pairProperty f g h i j k F G H I J K) :=
  inferInstanceAs (Decidable (_ → _ → _ → _ ∧ _))
end QuadraticFourRaw
