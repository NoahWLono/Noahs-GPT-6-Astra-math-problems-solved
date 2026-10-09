import FormNormalization

namespace APNRedo
section
variable {E : Type*} [AddCommGroup E] [Module F E] [FiniteDimensional F E]

/-- Disjoint half-dimensional radicals of two alternating forms force their sum
nonsingular. This is about the actual curried bilinear maps and their ranks. -/
theorem sum_nondegenerate_of_disjoint_half_rank
    (B C : Bilin E) (k : ℕ) (hdim : Module.finrank F E=2*k)
    (hB : ∀x, B x x=0) (hC : ∀x, C x x=0)
    (hrB : Module.finrank F (LinearMap.range B)=k)
    (hrC : Module.finrank F (LinearMap.range C)=k)
    (hDis : Disjoint (LinearMap.ker B) (LinearMap.ker C)) :
    Nondegenerate (B+C) := by
  have hkB : Module.finrank F (LinearMap.ker B)=k := by
    have := B.finrank_range_add_finrank_ker
    omega
  have hkC : Module.finrank F (LinearMap.ker C)=k := by
    have := C.finrank_range_add_finrank_ker
    omega
  have hsup : LinearMap.ker B ⊔ LinearMap.ker C=⊤ :=
    Submodule.eq_top_of_disjoint _ _ (by rw [hdim,hkB,hkC]; omega) hDis
  intro x hx
  have hCx : ∀y, C x y=0 := by
    intro y
    have hm : y ∈ LinearMap.ker B ⊔ LinearMap.ker C := by rw [hsup]; trivial
    obtain ⟨z,hz,w,hw,hy⟩ := Submodule.mem_sup.mp hm
    have hzB : B x z=0 := by
      rw [alternating_symmetric B hB]
      exact LinearMap.congr_fun (show B z=0 from hz) x
    have hzC : C x z=0 := by
      have hh := hx z
      change B x z+C x z=0 at hh
      simpa only [hzB,zero_add] using hh
    have hwC : C x w=0 := by
      rw [alternating_symmetric C hC]
      exact LinearMap.congr_fun (show C w=0 from hw) x
    rw [←hy,map_add,hzC,hwC,add_zero]
  have hBx : B x=0 := by
    apply LinearMap.ext
    intro y
    have hh := hx y
    change B x y+C x y=0 at hh
    simpa only [hCx y,add_zero] using hh
  have hCx' : C x=0 := LinearMap.ext hCx
  exact (Submodule.disjoint_def.mp hDis) x hBx hCx'

#print axioms sum_nondegenerate_of_disjoint_half_rank
end
end APNRedo
