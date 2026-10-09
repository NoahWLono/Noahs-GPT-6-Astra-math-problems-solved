import QuadraticMapWalsh
import APNCountCongruence

namespace APNRedo
section
variable {E : Type*} [AddCommGroup E] [Module F E] [Nontrivial E]

/-- The ordinary normalized polar of an arbitrary vectorial function. -/
def normalizedPolar (f : E → E) (x y : E) : E :=
  f (x+y)+f x+f y+f 0

/-- An arbitrary function whose actual normalized polar is bilinear yields a
mathlib quadratic map after subtracting its constant term. -/
def quadraticMapOfBilinearPolar (f : E → E) (B : E →ₗ[F] E →ₗ[F] E)
    (hB : ∀x y, normalizedPolar f x y=B x y) : QuadraticMap F E E where
  toFun x := f x+f 0
  toFun_smul c x := by
    have hc : c=0 ∨ c=1 := by
      have hv := ZMod.val_lt c
      have hh : c.val=0 ∨ c.val=1 := by omega
      rcases hh with hh | hh
      · left; exact ZMod.val_injective 2 (by simpa using hh)
      · right; exact ZMod.val_injective 2 (by simpa using hh)
    rcases hc with rfl | rfl
    · simpa only [zero_smul,zero_mul] using binary_add_self (f 0)
    · simp only [one_smul,one_mul]
  exists_companion' := by
    refine ⟨B,?_⟩
    intro x y
    rw [←hB]
    unfold normalizedPolar
    symm
    calc
      (f x+f 0)+(f y+f 0)+(f (x+y)+f x+f y+f 0) =
        (f (x+y)+f 0)+(f x+f x)+(f y+f y)+(f 0+f 0) := by abel
      _ = f (x+y)+f 0 := by simp only [binary_add_self,add_zero]

theorem quadraticMapOfBilinearPolar_reconstruct (f : E → E) (B : E →ₗ[F] E →ₗ[F] E)
    (hB : ∀x y, normalizedPolar f x y=B x y) :
    ∀x, quadraticMapOfBilinearPolar f B hB x+f 0=f x := by
  intro x
  exact binary_add_cancel (f x) (f 0)

theorem quadraticMapOfBilinearPolar_apn (f : E → E) (B : E →ₗ[F] E →ₗ[F] E)
    (hB : ∀x y, normalizedPolar f x y=B x y) (hf : APN f) :
    APN (quadraticMapOfBilinearPolar f B hB) :=
  (apn_add_constant_iff f (f 0)).mpr hf
end

open scoped Classical
/-- Non-bentness is tested by the actual integer Walsh transform, not by a rank
predicate. Labels are the ordinary binary coordinate vectors. -/
noncomputable def nonBentLabels (Q : QuadraticMap F (V 8) (V 8)) (c : V 8) : Finset (V 8) :=
  (Finset.univ.erase 0).filter fun b =>
    ¬FastWalsh.IsBent (encodedQuadraticAffine Q c) (QuadraticWalshMatrix.decode b)

theorem nonBentLabels_eq_degenerateLabels (Q : QuadraticMap F (V 8) (V 8)) (c : V 8) :
    nonBentLabels Q c=degenerateLabels Q := by
  apply Finset.filter_congr
  intro b hb
  rw [encodedQuadraticAffine_bent_iff,QuadraticWalshMatrix.coords_decode]

theorem apn_nonBent_count_congruence (Q : QuadraticMap F (V 8) (V 8))
    (c : V 8) (hQ : APN Q) : (nonBentLabels Q c).card%4=1 := by
  rw [nonBentLabels_eq_degenerateLabels]
  exact apn_degenerate_count_congruence Q hQ

#print axioms apn_nonBent_count_congruence
#print axioms quadraticMapOfBilinearPolar_reconstruct
#print axioms nonBentLabels_eq_degenerateLabels
end APNRedo
