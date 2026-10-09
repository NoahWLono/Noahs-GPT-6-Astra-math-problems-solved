import FamilyAlgebra.TraceCoordinates

namespace FamilyAlgebra
variable {E : Type*} [Field E]

def sixCoord (x : Six) : Fin 6 → Bool := fun i => match i.val with
  | 0 => x.a | 1 => x.b | 2 => x.c | 3 => x.d | 4 => x.f | _ => x.g

theorem sixCoord_injective : Function.Injective sixCoord := by
  intro x y h
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  have h2 := congrFun h 2
  have h3 := congrFun h 3
  have h4 := congrFun h 4
  have h5 := congrFun h 5
  cases x
  cases y
  simp only [sixCoord] at h0 h1 h2 h3 h4 h5
  cases h0; cases h1; cases h2; cases h3; cases h4; cases h5
  rfl

theorem liftSix_coord (x : Six) (i : Fin 6) : (liftSix x : Pfaffian.Coordinates E) i = bit (sixCoord x i) := by
  rcases i with ⟨i,hi⟩
  match i with
  | 0 | 1 | 2 | 3 | 4 | 5 => rfl
  | i+6 => omega

theorem vectorSum_coord (xs : List (Pfaffian.Coordinates E)) (i : Fin 6) :
    Pfaffian.vectorSum xs i = Pfaffian.scalarSum (xs.map (fun x => x i)) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [Pfaffian.vectorSum, Pfaffian.plus, Pfaffian.scalarSum, ih]

theorem pencil_coord (a : E) (X : Nat → Six) (n : Nat) (i : Fin 6) :
    pencil a X n i = binarySum (fun j => a^j) (fun j => sixCoord (X j) i) n := by
  rw [pencil, vectorSum_coord, List.map_map]
  have hm : (fun j => Pfaffian.scale (a^j) (liftSix (X j)) i) =
      (fun j => if sixCoord (X j) i then a^j else 0) := by
    funext j
    rw [Pfaffian.scale, liftSix_coord]
    cases sixCoord (X j) i <;> simp [bit]
  change Pfaffian.scalarSum ((List.range n).map (fun j => Pfaffian.scale (a^j) (liftSix (X j)) i)) = _
  rw [hm, scalarSum_range]

/-- Independence of the power basis makes the entire coefficient sequence
(up to the pencil's length) recoverable from its six field coordinates. -/
theorem pencil_injective (two_zero : (2:E)=0) (a : E) (n : Nat)
    (independent : ∀ bits, binarySum (fun k => a^k) bits n=0 ↔ ∀ k, k<n → bits k=false)
    (X Y : Nat → Six) (heq : pencil a X n = pencil a Y n) :
    ∀ j, j<n → X j=Y j := by
  intro j hj
  apply sixCoord_injective
  funext i
  have hcoord := congrFun heq i
  rw [pencil_coord, pencil_coord] at hcoord
  have hz : binarySum (fun k => a^k) (fun k => sixCoord (X k) i ^^ sixCoord (Y k) i) n=0 := by
    rw [binarySum_xor two_zero, hcoord, double_zero two_zero]
  have hb := (independent _).mp hz j hj
  cases hx : sixCoord (X j) i <;> cases hy : sixCoord (Y j) i <;> simp_all

theorem odd_injective : ∀ s t s' t', oddPlane s t=oddPlane s' t' → s=s' ∧ t=t' := by decide

theorem even_injective : ∀ s t s' t', evenPlane s t=evenPlane s' t' → s=s' ∧ t=t' := by decide

theorem family_parameter_injective (two_zero : (2:E)=0) (a : E) (n : Nat) (positive : 0<n)
    (independent : ∀ bits, binarySum (fun k => a^k) bits n=0 ↔ ∀ k, k<n → bits k=false)
    (u v w z u' v' w' z' : Bool) (s t s' t' : Nat → Bool)
    (heq : pencil a (family u v w z s t) n = pencil a (family u' v' w' z' s' t') n) :
    u=u' ∧ v=v' ∧ w=w' ∧ z=z' ∧ ∀ j, 0<j → j<n → s j=s' j ∧ t j=t' j := by
  have hc := pencil_injective two_zero a n independent _ _ heq
  have h0 := hc 0 positive
  simp only [family, if_true] at h0
  rcases base_injective u v w z u' v' w' z' h0 with ⟨hu,hv,hw,hz⟩
  refine ⟨hu,hv,hw,hz,?_⟩
  intro j hj hjn
  have hx := hc j hjn
  simp only [family, show ¬j=0 by omega, if_false] at hx
  by_cases ho : j%2=1
  · simp only [ho, if_true] at hx
    exact odd_injective _ _ _ _ hx
  · simp only [ho, if_false] at hx
    exact even_injective _ _ _ _ hx

/-- Symmetric zero-diagonal matrix corresponding to six alternating entries
in characteristic two. -/
def altMatrix (x : Pfaffian.Coordinates E) : TraceCoordinates.Matrix4 E := fun i j =>
  match i.val, j.val with
  | 0,1 | 1,0 => x 0
  | 0,2 | 2,0 => x 1
  | 0,3 | 3,0 => x 2
  | 1,2 | 2,1 => x 3
  | 1,3 | 3,1 => x 4
  | 2,3 | 3,2 => x 5
  | _,_ => 0

theorem altMatrix_injective : Function.Injective (altMatrix : Pfaffian.Coordinates E → TraceCoordinates.Matrix4 E) := by
  intro x y h
  funext i
  rcases i with ⟨i,hi⟩
  match i with
  | 0 => exact congrArg (fun K => K 0 1) h
  | 1 => exact congrArg (fun K => K 0 2) h
  | 2 => exact congrArg (fun K => K 0 3) h
  | 3 => exact congrArg (fun K => K 1 2) h
  | 4 => exact congrArg (fun K => K 1 3) h
  | 5 => exact congrArg (fun K => K 2 3) h
  | i+6 => omega

/-- The constructed trace pencil retains every effective parameter whenever
its scalar functional is nonzero. -/
theorem trace_family_parameter_injective {F : Type*} [AddCommGroup F]
    (T : E →+ F) (nonzero : T ≠ 0)
    (two_zero : (2:E)=0) (a : E) (n : Nat) (positive : 0<n)
    (independent : ∀ bits, binarySum (fun k => a^k) bits n=0 ↔ ∀ k, k<n → bits k=false)
    (u v w z u' v' w' z' : Bool) (s t s' t' : Nat → Bool)
    (heq : TraceCoordinates.form T (altMatrix (pencil a (family u v w z s t) n)) =
      TraceCoordinates.form T (altMatrix (pencil a (family u' v' w' z' s' t') n))) :
    u=u' ∧ v=v' ∧ w=w' ∧ z=z' ∧ ∀ j, 0<j → j<n → s j=s' j ∧ t j=t' j := by
  apply family_parameter_injective two_zero a n positive independent
  apply altMatrix_injective
  exact TraceCoordinates.transfer_injective T nonzero heq

#print axioms trace_family_parameter_injective
#print axioms family_parameter_injective
end FamilyAlgebra
