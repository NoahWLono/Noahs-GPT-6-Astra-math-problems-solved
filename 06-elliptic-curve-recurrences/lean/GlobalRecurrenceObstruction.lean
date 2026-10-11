import EllipticFixedFiber
import GlobalDegreeObstruction
import InvariantDivisor

/-! ASTRA-01 T1 in the actual elliptic function-field/pole-degree formulation.
All translation, valuation, degree, and invariant-fiber ingredients are proved
in the imported local modules; none are hypotheses of this endpoint. -/
namespace Astra01.EllipticPointDivisor
noncomputable section
open WeierstrassCurve.Affine.Chart FunctionField FunctionField.Chart
open scoped RatFunc Polynomial
variable {k : Type*} [Field k] [IsAlgClosed k]
variable (W : WeierstrassCurve.Affine k) [W.IsElliptic]
variable (K : Type*) [Field K] [Algebra W.CoordinateRing K] [IsFractionRing W.CoordinateRing K]
variable [Algebra k[X] K] [IsScalarTower k[X] W.CoordinateRing K]
  [Algebra k⟮X⟯ K] [IsScalarTower k[X] k⟮X⟯ K]
  [_root_.FunctionField k K] [Algebra.IsSeparable k⟮X⟯ K]
local instance : Algebra k K := FunctionField.algebraConstants k K
local instance : IsScalarTower k k[X] K := FunctionField.algebraConstants_isScalarTower k K


local instance : DecidableEq k := Classical.decEq _

theorem zeroDivisor_translation (G P : W.Point) (f : Kˣ) :
    zeroDivisor W K (Units.map (Astra01.EllipticTranslation.translationEquiv W K G).toMonoidHom f) P =
      zeroDivisor W K f (P + G) :=
  congrArg Int.toNat (principalDivisor_translation W K G P f)

theorem poleDivisor_translation (G P : W.Point) (f : Kˣ) :
    poleDivisor W K (Units.map (Astra01.EllipticTranslation.translationEquiv W K G).toMonoidHom f) P =
      poleDivisor W K f (P + G) :=
  congrArg (fun z : ℤ => (-z).toNat) (principalDivisor_translation W K G P f)

theorem translation_semiconjugacy_order_dvd_degree (G : W.Point) (hG : 0 < addOrderOf G)
    (f : K) (hf : ∀ c : k, f ≠ algebraMap k K c)
    (p q : k[X]) (hp : p ≠ 0) (hq : q ≠ 0) (hpq : IsCoprime p q)
    (hdeg : max p.natDegree q.natDegree = 1)
    (he : Astra01.EllipticTranslation.translationEquiv W K G f =
      Polynomial.aeval f p / Polynomial.aeval f q) :
    addOrderOf G ∣ divisorDegree W
      (poleDivisor W K (Units.mk0 f (by simpa using hf 0))) := by
  let e := Astra01.EllipticTranslation.translationEquiv W K G
  let fu : Kˣ := Units.mk0 f (by simpa using hf 0)
  let pu := polynomialValueUnit K f hf p hp
  let qu := polynomialValueUnit K f hf q hq
  have heu : Units.map e.toMonoidHom fu = pu / qu := by
    apply Units.ext
    simpa [e, fu, pu, qu, polynomialValueUnit] using he
  by_cases hq0 : q.natDegree = 0
  · have hp1 : p.natDegree = 1 := by omega
    have hinv : poleDivisor W K (Units.map e.toMonoidHom fu) = poleDivisor W K fu := by
      rw [heu, poleDivisor_rational W K fu pu qu p q hp hq hpq rfl rfl]
      dsimp only [qu]
      rw [zeroDivisor_constant_polynomial W K f hf q hq hq0, hp1, hq0,
        Nat.sub_zero, one_smul, zero_add]
    apply translation_invariant_degree_dvd G (poleDivisor W K fu) hG
    intro P
    exact (poleDivisor_translation W K G P fu).symm.trans
      (congrArg (fun d : W.Point →₀ ℕ => d P) hinv)
  · have hq1 : q.natDegree = 1 := by omega
    obtain ⟨c, hcroot, hctdeg, hcop⟩ := exists_fixed_linear_fiber p q hpq hdeg hq1
    let t := p - Polynomial.C c * q
    have ht0 : t ≠ 0 := by intro h; simp only [t, h, Polynomial.natDegree_zero] at hctdeg; omega
    let tu := polynomialValueUnit K f hf t ht0
    let sf : Kˣ := Units.mk0 (f - algebraMap k K c) (sub_ne_zero.mpr (hf c))
    have hes : Units.map e.toMonoidHom sf = tu / qu := by
      apply Units.ext
      have hs : e (f - algebraMap k K c) = Polynomial.aeval f t / Polynomial.aeval f q := by
        rw [map_sub, e.commutes, he]
        simp only [t, map_sub, map_mul, Polynomial.aeval_C]
        field_simp [nonconstant_polynomial_ne_zero K f hf q hq]
      simpa [sf, tu, qu, polynomialValueUnit] using hs
    have hinv : zeroDivisor W K (Units.map e.toMonoidHom sf) = zeroDivisor W K sf := by
      rw [hes, zeroDivisor_rational_of_degree_le W K fu tu qu t q ht0 hq hcop
        (by change q.natDegree ≤ (p - Polynomial.C c * q).natDegree; omega) rfl rfl]
      exact zeroDivisor_linear_fiber W K f hf t hctdeg ht0 c hcroot
    have hdvd : addOrderOf G ∣ divisorDegree W (zeroDivisor W K sf) := by
      apply translation_invariant_degree_dvd G (zeroDivisor W K sf) hG
      intro P
      exact (zeroDivisor_translation W K G P sf).symm.trans
        (congrArg (fun d : W.Point →₀ ℕ => d P) hinv)
    have hdf := nonconstant_finite_fiber_degree W K f hf c
    change divisorDegree W (zeroDivisor W K sf) = divisorDegree W (poleDivisor W K fu) at hdf
    exact hdf ▸ hdvd

/-- Both conclusions of T1, with an actual reduced rational map and the
constructed elliptic translation automorphism. The degree is the actual
point-divisor pole degree, not a degree/composition oracle. -/
theorem global_recurrence_obstruction (G : W.Point) (n : ℕ) (hn : 2 ≤ n)
    (horder : addOrderOf G = n) (f : K)
    (hf : ∀ c : k, f ≠ algebraMap k K c)
    (p q : k[X]) (hq : q ≠ 0) (hpq : IsCoprime p q)
    (he : Astra01.EllipticTranslation.translationEquiv W K G f =
      Polynomial.aeval f p / Polynomial.aeval f q) :
    max p.natDegree q.natDegree = 1 ∧
      n ∣ divisorDegree W (poleDivisor W K (Units.mk0 f (by simpa using hf 0))) := by
  have hp : p ≠ 0 := by
    intro hp
    have hval : Astra01.EllipticTranslation.translationEquiv W K G f = 0 := by simpa [hp] using he
    have hf0 : f = 0 := (Astra01.EllipticTranslation.translationEquiv W K G).injective
      (hval.trans (map_zero _).symm)
    exact hf 0 (hf0.trans (map_zero _).symm)
  have hd := translation_semiconjugacy_degree_one W K G f hf p q hp hq hpq he
  refine ⟨hd, ?_⟩
  rw [← horder]
  exact translation_semiconjugacy_order_dvd_degree W K G (by omega) f hf p q hp hq hpq hd he

end
end Astra01.EllipticPointDivisor
#print axioms Astra01.EllipticPointDivisor.global_recurrence_obstruction
