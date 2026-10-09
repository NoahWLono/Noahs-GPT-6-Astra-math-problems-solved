import WeightThirtyModel

namespace BooleanANF
variable {V : Type*} [AddCommGroup V] [Module F₂ V]

private theorem binary_module_add_self (x : V) : x+x=0 := by
  calc
    x+x = ((1 : F₂)+1) • x := by rw [add_smul, one_smul]
    _ = 0 := by rw [CharTwo.add_self_eq_zero, zero_smul]

private theorem profile_shift_axis (f : V → F₂) (e : (Block × Block) ≃ₗ[F₂] V)
    (p : V) (c : Block) (hp : p = e (c,0))
    (he : ∀ x y : Block, f (p+e (x,y)) = delta 0 x+delta 0 y) :
    ∀ a v : Block, f (e (a,v)) = delta c a+delta 0 v := by
  intro a v
  have harg : p+e (a+c,v) = e (a,v) := by
    rw [hp, ← map_add]
    congr 1
    apply Prod.ext
    · change c+(a+c)=a
      rw [add_left_comm, binary_module_add_self, add_zero]
    · simp
  have hh := he (a+c) v
  rw [harg] at hh
  have hd := congrFun (delta_translate (0 : Block) c) a
  simp only [zero_add] at hd
  simpa only [hd] using hh

/-- If zero belongs to exactly one of two transverse flats, their intersection can be
placed at a nonzero first-block vector using purely linear coordinates. -/
theorem TwoTransverseFlats.zero_profile (f : V → F₂) (h : TwoTransverseFlats f)
    (hzero : f 0=1) :
    ∃ (e : (Block × Block) ≃ₗ[F₂] V) (c : Block), c≠0 ∧
      ∀ a v : Block, f (e (a,v)) = delta c a+delta 0 v := by
  classical
  obtain ⟨p,e₀,he₀⟩ := h
  let e : (Block × Block) ≃ₗ[F₂] V :=
    (LinearEquiv.sumArrowLequivProdArrow (Fin 4) (Fin 4) F₂ F₂).symm.trans e₀
  have he : ∀ x y : Block, f (p+e (x,y)) = delta 0 x+delta 0 y := he₀
  let t : Block × Block := e.symm p
  have hp : p=e (t.1,t.2) := (e.apply_symm_apply p).symm
  have hz := he t.1 t.2
  have het : e (t.1,t.2)=p := by simpa only [Prod.mk.eta] using hp.symm
  rw [het,binary_module_add_self,hzero] at hz
  by_cases hx : t.1=0
  · have hy : t.2≠0 := by
      intro hy
      simp [delta,hx,hy,CharTwo.add_self_eq_zero] at hz
    let es : (Block × Block) ≃ₗ[F₂] V := (LinearEquiv.prodComm F₂ Block Block).trans e
    refine ⟨es,t.2,hy,?_⟩
    apply profile_shift_axis f es p t.2
    · simpa [es, hx] using hp
    · intro x y
      simpa [es,add_comm] using he y x
  · have hy : t.2=0 := by
      by_contra hy
      simp [delta,hx,hy] at hz
    refine ⟨e,t.1,hx,?_⟩
    apply profile_shift_axis f e p t.1
    · simpa [hy] using hp
    · exact he

/-- The exact nonzero-label support shape needed by the APN incidence obstruction. -/
theorem TwoTransverseFlats.nonzero_support_profile (f : V → F₂) (h : TwoTransverseFlats f)
    (hzero : f 0=1) :
    ∃ (e : (Block × Block) ≃ₗ[F₂] V) (c : Block), c≠0 ∧
      ∀ a v : Block,
        (f (e (a,v))=1 ∧ e (a,v)≠0) ↔
          (v=0 ∧ a≠0 ∧ a≠c) ∨ (a=c ∧ v≠0) := by
  classical
  obtain ⟨e,c,hc,he⟩ := h.zero_profile f hzero
  refine ⟨e,c,hc,?_⟩
  intro a v
  rw [he]
  have hz : e (a,v)=0 ↔ a=0 ∧ v=0 := by
    rw [← e.map_zero, e.injective.eq_iff]
    exact Prod.mk.inj_iff
  by_cases ha : a=c <;> by_cases hv : v=0 <;> by_cases ha0 : a=0 <;>
    simp [delta,ha,hv,ha0,hz,CharTwo.add_self_eq_zero] at *

end BooleanANF
