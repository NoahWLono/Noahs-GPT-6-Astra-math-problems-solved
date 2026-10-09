import QuadraticWalshMatrix
namespace QuadraticWalshFamily
open FastWalsh QuadraticWalshShift QuadraticWalshMatrix

theorem pack_false : pack (fun _ : Fin n => false) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simpa only [pack, ih] using (BitVec.false_cons_zero : BitVec.cons false (0 : BitVec n) = 0)

theorem unitVec_last : unitVec (Fin.last n) = BitVec.cons true (0 : BitVec n) := by
  unfold unitVec decode
  simp only [pack]
  congr 1
  · simp [Pi.single_apply, fBit]
  · have he : (fun i : Fin n => fBit ((Pi.single (Fin.last n) (1 : F) : V (n+1)) i.castSucc)) = fun _ => false := by
      funext i
      have hn : i.castSucc ≠ Fin.last n := Fin.castSucc_ne_last i
      simp [Pi.single_apply, hn, fBit]
    rw [he, pack_false]

theorem unitVec_castSucc (i : Fin n) : unitVec i.castSucc = BitVec.cons false (unitVec i) := by
  unfold unitVec decode
  simp only [pack]
  congr 1
  · have hn : Fin.last n ≠ i.castSucc := (Fin.castSucc_ne_last i).symm
    simp [Pi.single_apply, hn, fBit]
  · congr 1
    funext j
    simp [Pi.single_apply]

theorem binaryDot_unitVec (a : BitVec n) (i : Fin n) : binaryDot a (unitVec i) = a.getLsbD i := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    rw [← BitVec.cons_msb_setWidth a]
    refine Fin.lastCases ?_ (fun j => ?_) i
    · rw [unitVec_last, binaryDot_cons, binaryDot_zero]
      simp only [Bool.false_xor, Bool.and_true, Fin.val_last, BitVec.getLsbD_cons, if_pos rfl, ite_true]
    · rw [unitVec_castSucc, binaryDot_cons]
      simp only [Bool.and_false, Bool.xor_false, ih, BitVec.getLsbD_cons]
      have hj : j.castSucc.val ≠ n := Nat.ne_of_lt j.isLt
      simp only [hj, ↓reduceIte]
      rfl



def coordinateDot (u : V n) : V n →ₗ[F] F where
  toFun v := dotProduct u v
  map_add' v w := dotProduct_add u v w
  map_smul' c v := dotProduct_smul c u v

theorem bitF_binaryDot (a b : BitVec n) :
    bitF (binaryDot a b) = dotProduct (coords a) (coords b) := by
  have hf : dotFunctional a = coordinateDot (coords a) := by
    apply functional_ext
    intro i
    change bitF (binaryDot a (unitVec i)) = dotProduct (coords a) (Pi.single i 1)
    rw [binaryDot_unitVec, dotProduct_single, mul_one]
    rfl
  have hh := LinearMap.congr_fun hf (coords b)
  change bitF (binaryDot a (decode (coords b))) = dotProduct (coords a) (coords b) at hh
  rwa [decode_coords] at hh

abbrev Bilin (n : Nat) := V n →ₗ[F] V n →ₗ[F] F

/-- Output coefficient for the upper-triangular input pair (i,j). -/
def pairCoefficient (L : V m →ₗ[F] Bilin n) (i j : Fin n) : BitVec m :=
  decode (fun k => L (Pi.single k 1) (Pi.single i 1) (Pi.single j 1))

theorem pairCoefficient_component (L : V m →ₗ[F] Bilin n) (b : BitVec m)
    (i j : Fin n) : bitF (binaryDot b (pairCoefficient L i j)) =
      L (coords b) (Pi.single i 1) (Pi.single j 1) := by
  rw [bitF_binaryDot]
  unfold pairCoefficient
  rw [coords_decode]
  have hsum : (coords b) = ∑ k : Fin m, (coords b k) • (Pi.single k (1 : F) : V m) := by
    ext k
    simp [Pi.single_apply]
  conv_rhs => rw [hsum]
  simp [map_sum, map_smul, dotProduct, Finset.sum_apply, LinearMap.sum_apply]


theorem bitF_and (a b : Bool) : bitF (a && b) = bitF a * bitF b := by
  cases a <;> cases b <;> decide

def polarTerm (c : Nat × Nat × BitVec m) (b : BitVec m) (a x : BitVec n) : F :=
  bitF (binaryDot b c.2.2) *
    (bitF (x.getLsbD c.1) * bitF (a.getLsbD c.2.1) +
     bitF (a.getLsbD c.1) * bitF (x.getLsbD c.2.1))

theorem coefficientPolar_sum (cs : List (Nat × Nat × BitVec m)) (b : BitVec m)
    (a x : BitVec n) : bitF (coefficientPolar cs b a x) = (cs.map fun c => polarTerm c b a x).sum := by
  induction cs with
  | nil => rfl
  | cons c cs ih => simp only [coefficientPolar, bitF_xor, bitF_and, ih,
      List.map_cons, List.sum_cons, polarTerm]

noncomputable def familyCoefficients (L : V m →ₗ[F] Bilin n) : List (Nat × Nat × BitVec m) :=
  ((Finset.univ.filter fun p : Fin n × Fin n => p.1 < p.2).toList).map
    (fun p => (p.1.val, p.2.val, pairCoefficient L p.1 p.2))

theorem bitF_unitVec_get (i j : Fin n) : bitF ((unitVec i).getLsbD j) = (Pi.single i 1 : V n) j := by
  exact congrFun (coords_decode (Pi.single i 1)) j


theorem sum_tri_delta (f : Fin n → Fin n → F) (a x : Fin n) :
    (∑ i : Fin n, ∑ j : Fin n,
      if i<j then (if j=a then (if i=x then f i j else 0) else 0) else 0) =
      if x<a then f x a else 0 := by
  rw [Finset.sum_eq_single x]
  · rw [Finset.sum_eq_single a]
    · simp
    · intro j hj hja
      simp [hja]
    · simp
  · intro i hi hix
    apply Finset.sum_eq_zero
    intro j hj
    simp [hix]
  · simp

theorem family_polar_entry (L : V m →ₗ[F] Bilin n) (b : BitVec m) (a x : Fin n) :
    bitF (coefficientPolar (familyCoefficients L) b (unitVec a) (unitVec x)) =
      (if x<a then L (coords b) (Pi.single x 1) (Pi.single a 1) else 0) +
      (if a<x then L (coords b) (Pi.single a 1) (Pi.single x 1) else 0) := by
  rw [coefficientPolar_sum]
  unfold familyCoefficients
  simp only [List.map_map]
  rw [← List.sum_toFinset _ (Finset.nodup_toList _), Finset.toList_toFinset]
  simp only [Function.comp_apply, polarTerm, pairCoefficient_component, bitF_unitVec_get]
  simp [Finset.sum_filter, Fintype.sum_prod_type, Pi.single_apply, mul_add,
    Finset.sum_add_distrib, mul_ite, ite_mul]
  rw [sum_tri_delta, sum_tri_delta]


theorem alternating_symmetric (B : Bilin n) (hAlt : ∀ v, B v v = 0) (v w : V n) :
    B v w = B w v := by
  have h := hAlt (v+w)
  simp only [map_add, LinearMap.add_apply] at h
  rw [hAlt v, hAlt w, zero_add, add_zero] at h
  have ht : ∀ a b : F, a+b=0 → a=b := by decide
  exact ht _ _ (by simpa [add_comm] using h)

/-- The generated upper-triangular vector coefficient list realizes the given
alternating linear family exactly at every actual output mask. -/
theorem family_polarForm_eq (L : V m →ₗ[F] Bilin n)
    (hAlt : ∀ t v, L t v v = 0) (b : BitVec m) :
    polarForm (familyCoefficients L) b = L (coords b) := by
  apply (Pi.basisFun F (Fin n)).ext
  intro i
  apply functional_ext
  intro j
  simp only [Pi.basisFun_apply]
  change bitF (coefficientPolar (familyCoefficients L) b (unitVec i) (unitVec j)) =
    L (coords b) (Pi.single i 1) (Pi.single j 1)
  rw [family_polar_entry]
  rcases lt_trichotomy i j with hij | hij | hij
  · simp [hij, not_lt_of_ge (le_of_lt hij)]
  · subst j
    simp only [lt_self_iff_false, if_false, zero_add]
    exact (hAlt (coords b) (Pi.single i 1)).symm
  · simp only [hij, if_true, not_lt_of_ge (le_of_lt hij), if_false, add_zero]
    exact alternating_symmetric (L (coords b)) (hAlt (coords b)) _ _

/-- A complete constructor-to-Walsh bridge: the left side is the original finite
Walsh bentness of a concretely defined vectorial quadratic coefficient list. -/
theorem family_bent_iff (L : V m →ₗ[F] Bilin n)
    (hAlt : ∀ t v, L t v v = 0) (b : BitVec m) :
    IsBent (quadratic (familyCoefficients L) : BitVec n → BitVec m) b ↔
      Nondegenerate (L (coords b)) := by
  exact bent_iff_nondegenerate_of_polarForm_eq (familyCoefficients L) b
    (L (coords b)) (family_polarForm_eq L hAlt b)

#print axioms family_polarForm_eq
#print axioms family_bent_iff
#print axioms family_polar_entry
#print axioms pairCoefficient_component
end QuadraticWalshFamily
