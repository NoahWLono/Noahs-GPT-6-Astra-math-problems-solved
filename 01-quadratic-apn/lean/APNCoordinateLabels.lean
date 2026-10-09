import APNIncidence
import QuadraticWalshFamily

namespace APNRedo
open scoped BigOperators Classical

/-- The ordinary binary coordinate dot product, as an actual bilinear form. -/
def coordinateDotForm (n : ℕ) : Bilin (V n) where
  toFun b :=
    { toFun x := dotProduct b x
      map_add' x y := dotProduct_add b x y
      map_smul' c x := dotProduct_smul c b x }
  map_add' b c := by
    apply LinearMap.ext
    intro x
    exact add_dotProduct b c x
  map_smul' c b := by
    apply LinearMap.ext
    intro x
    exact smul_dotProduct c b x

@[simp] theorem coordinateDotForm_apply (n : ℕ) (b x : V n) :
    coordinateDotForm n b x=dotProduct b x := rfl

theorem coordinateDotForm_nondegenerate (n : ℕ) : Nondegenerate (coordinateDotForm n) := by
  intro b hb
  funext i
  have hi := hb (Pi.single i 1)
  simpa only [coordinateDotForm_apply,dotProduct_single,mul_one] using hi

/-- No abstract dual-label assumption: this equivalence is built from coordinate dot product. -/
noncomputable def coordinateLabelEquiv (n : ℕ) : V n ≃ₗ[F] (V n →ₗ[F] F) :=
  formEquiv (coordinateDotForm n) (coordinateDotForm_nondegenerate n)

@[simp] theorem coordinateLabelEquiv_apply (n : ℕ) (b : V n) :
    coordinateLabelEquiv n b=coordinateDotForm n b := rfl

/-- The actual coordinate component function. -/
def coordinateComponent (Q : QuadraticMap F (V n) (V n)) (b x : V n) : F :=
  dotProduct b (Q x)

/-- Its actual polar form as a linear family in the coordinate label. -/
def componentPencil (Q : QuadraticMap F (V n) (V n)) : V n →ₗ[F] Bilin (V n) :=
  (componentPencilDual Q).comp (coordinateDotForm n)

@[simp] theorem componentPencil_apply (Q : QuadraticMap F (V n) (V n)) (b a x : V n) :
    componentPencil Q b a x=dotProduct b (Q.polarBilin a x) := rfl

theorem componentPencil_actual (Q : QuadraticMap F (V n) (V n)) (b : V n) :
    ((coordinateDotForm n b).compQuadraticMap' Q).polarBilin=componentPencil Q b :=
  componentPolarDual_actual Q (coordinateDotForm n b)

/-- Coordinate-dot labels match the previously checked BitVec Walsh dot semantics. -/
theorem coordinateDot_matches_binaryDot (a b : BitVec n) :
    dotProduct (QuadraticWalshMatrix.coords a) (QuadraticWalshMatrix.coords b)=
      QuadraticWalshMatrix.bitF (FastWalsh.binaryDot a b) :=
  (QuadraticWalshFamily.bitF_binaryDot a b).symm

theorem apn_unique_coordinate_radical_label (Q : QuadraticMap F (V 8) (V 8))
    (hQ : APN Q) (a : V 8) (ha : a≠0) :
    ∃! b : V 8, b≠0 ∧ ∀x, componentPencil Q b a x=0 := by
  let e := coordinateLabelEquiv 8
  obtain ⟨d,⟨hd,hr⟩,huniq⟩ := apn_unique_nonzero_radical_label Q hQ a ha
  refine ⟨e.symm d,⟨?_,?_⟩,?_⟩
  · intro he
    apply hd
    have hh := congrArg e he
    simpa only [e.apply_symm_apply,map_zero] using hh
  · intro x
    change componentPolarDual Q (e (e.symm d)) a x=0
    simpa only [e.apply_symm_apply] using hr x
  · intro b hb
    apply e.injective
    rw [e.apply_symm_apply]
    apply huniq
    refine ⟨?_,hb.2⟩
    intro he
    exact hb.1 ((LinearEquiv.map_eq_zero_iff e).mp he)

theorem apn_coordinate_radicals_disjoint (Q : QuadraticMap F (V 8) (V 8))
    (hQ : APN Q) (b c : V 8) (hb : b≠0) (hc : c≠0) (hbc : b≠c) :
    Disjoint (LinearMap.ker (componentPencil Q b)) (LinearMap.ker (componentPencil Q c)) := by
  apply apn_component_radicals_disjoint Q hQ
  · exact (LinearEquiv.map_ne_zero_iff (coordinateLabelEquiv 8)).mpr hb
  · exact (LinearEquiv.map_ne_zero_iff (coordinateLabelEquiv 8)).mpr hc
  · exact fun h => hbc ((coordinateLabelEquiv 8).injective h)

/-- Incidence255 now indexed by the actual eight-bit coordinate labels. -/
theorem apn_coordinate_radical_incidence (Q : QuadraticMap F (V 8) (V 8)) (hQ : APN Q) :
    ∑b ∈ Finset.univ.erase (0:V 8),
      (2^Module.finrank F (LinearMap.ker (componentPencil Q b))-1)=255 := by
  let e := coordinateLabelEquiv 8
  have hs : (∑b ∈ Finset.univ.erase (0:V 8),
      (2^Module.finrank F (LinearMap.ker (componentPencil Q b))-1))=
      ∑d ∈ Finset.univ.erase (0:V 8 →ₗ[F] F),
        (2^Module.finrank F (LinearMap.ker (componentPolarDual Q d))-1) := by
    apply Finset.sum_bij (fun b _ => e b)
    · intro b hb
      exact Finset.mem_erase.mpr ⟨(LinearEquiv.map_ne_zero_iff e).mpr (Finset.mem_erase.mp hb).1,
        Finset.mem_univ _⟩
    · intro b hb c hc he
      exact e.injective he
    · intro d hd
      refine ⟨e.symm d,Finset.mem_erase.mpr ⟨?_,Finset.mem_univ _⟩,e.apply_symm_apply d⟩
      intro he
      have hh := congrArg e he
      exact (Finset.mem_erase.mp hd).1 (by simpa only [e.apply_symm_apply,map_zero] using hh)
    · intro b hb
      rfl
  rw [hs]
  exact apn_radical_incidence_eight Q hQ

#print axioms apn_coordinate_radical_incidence
#print axioms apn_coordinate_radicals_disjoint
end APNRedo
