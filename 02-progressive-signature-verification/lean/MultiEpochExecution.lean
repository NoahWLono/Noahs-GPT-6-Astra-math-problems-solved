import StoredBufferedExecution
import GlobalSignatureCompiler
import EpochPrefix

/-! Actual promotion/reset machine. All bank samples are mathematical inputs;
only the current and next bank are in the operational state. A prefix consists
of complete reservation phases followed by one possibly partial phase. -/
namespace ProgressivePool.MultiEpochExecution
open Classical
open StoredCheckExecution
open StoredBufferedExecution
open IndexedPreparation
open EpochComposition
variable {F H : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {s n m R r : ℕ}
abbrev Bank (F : Type*) (s n : ℕ) := Fin s → Fin n → F
abbrev Prepared (F : Type*) (s m : ℕ) := Fin s → Fin m → F
abbrev Program (F H : Type*) (s m n r : ℕ) :=
  InvocationProgram (Fin s) (Input F m n) H H r
abbrev Phase (F H : Type*) (s m n R : ℕ) := H → Program F H s m n R

def Ready (A : Fin n → Fin m → F) (C : Bank F s n) (Z : Prepared F s m) : Prop :=
  ∀ j col, Z j col = storedRow A (C j) col

structure Result (F H : Type*) (s n m : ℕ) where
  output : H
  current : Bank F s n
  prepared : Prepared F s m
  pending : CursorState F s m
  trace : List Bool
  reservations : ℕ
  checkingMultiplications : ℕ
  checkingAdditions : ℕ
  checkingSubtractions : ℕ
  preparationMultiplications : ℕ

/-- A complete phase promotes precisely the computed pending matrix. The new
pending cursor is reset by the next recursive call. Neither promotion nor the
active checker recomputes CA from the raw public matrix. -/
noncomputable def run (A : Fin n → Fin m → F) (W : ℕ)
    (terminal : Phase F H s m n r) :
    (phases : List (Phase F H s m n R)) → H → Bank F s n → Prepared F s m →
    Samples (Bank F s n) (phases.length+1) → Result F H s n m
  | [], h, C, Z, future =>
      let e := storedBufferedRun A Z C future.1 W (terminal h) initialCursor
      ⟨e.output, C, Z, e.pending, e.trace, e.reservations,
        e.multiplications, e.additions, e.subtractions, e.pending.buffer.multiplications⟩
  | p::ps, h, C, Z, future =>
      let e := storedBufferedRun A Z C future.1 W (p h) initialCursor
      let rest := run A W terminal ps e.output future.1
        (fun j col => e.pending.buffer.value (j,col)) future.2
      ⟨rest.output, rest.current, rest.prepared, rest.pending,
        e.trace ++ rest.trace, e.reservations + rest.reservations,
        e.multiplications + rest.checkingMultiplications,
        e.additions + rest.checkingAdditions,
        e.subtractions + rest.checkingSubtractions,
        e.pending.buffer.multiplications + rest.preparationMultiplications⟩

/-- Cold setup is the same indexed multiplication accumulator, not a free
prepared-key assumption. -/
noncomputable def coldRun (A : Fin n → Fin m → F) (W : ℕ)
    (terminal : Phase F H s m n r) (phases : List (Phase F H s m n R))
    (h : H) (draws : Samples (Bank F s n) (phases.length+2)) : Result F H s n m :=
  let setup := runCursor A draws.1 (s*m*n) initialCursor
  let rest := run A W terminal phases h draws.1
    (fun j col => setup.buffer.value (j,col)) draws.2
  { rest with preparationMultiplications :=
      setup.buffer.multiplications + rest.preparationMultiplications }

/-- Residual-oracle specification used by the probability experiment. It has
no prepared coefficients and never observes the prefetched bank. -/
noncomputable def rawRun (A : Fin n → Fin m → F)
    (terminal : Phase F H s m n r) :
    (phases : List (Phase F H s m n R)) → H → Bank F s n →
    Samples (Bank F s n) (phases.length+1) → H × Bank F s n
  | [], h, C, _ =>
      (runOutput C (flattenInvocations (mapInvocationInputs A (terminal h))), C)
  | p::ps, h, C, future =>
      rawRun A terminal ps
        (runOutput C (flattenInvocations (mapInvocationInputs A (p h))))
        future.1 future.2

/-- Transition-consistent full phases: every execution uses the reserved R
slots before promotion. Zero-check and aborted invocations still occupy slots.
This condition concerns executed reservations, never successful checks. -/
def Full (A : Fin n → Fin m → F) (p : Phase F H s m n R) : Prop :=
  ∀ h C, (invocationDepths C (mapInvocationInputs A (p h))).length = R

/-- The operational multi-epoch machine refines the residual experiment, and
its final active coefficients are genuinely ready after every promotion. -/
theorem run_refines (A : Fin n → Fin m → F) (W : ℕ)
    (terminal : Phase F H s m n r) (phases : List (Phase F H s m n R))
    (hB : s*m*n = R*W) (hFull : ∀ p ∈ phases, Full A p)
    (h : H) (C : Bank F s n) (Z : Prepared F s m) (hZ : Ready A C Z)
    (future : Samples (Bank F s n) (phases.length+1)) :
    (run A W terminal phases h C Z future).output = (rawRun A terminal phases h C future).1 ∧
    (run A W terminal phases h C Z future).current = (rawRun A terminal phases h C future).2 ∧
    Ready A (run A W terminal phases h C Z future).current
      (run A W terminal phases h C Z future).prepared := by
  induction phases generalizing h C Z with
  | nil =>
      exact ⟨storedBuffered_output A Z C future.1 W hZ (terminal h) initialCursor, rfl, hZ⟩
  | cons p ps ih =>
      let e := storedBufferedRun A Z C future.1 W (p h) initialCursor
      have ho : e.output = runOutput C (flattenInvocations (mapInvocationInputs A (p h))) :=
        storedBuffered_output A Z C future.1 W hZ (p h) initialCursor
      have hr : e.reservations = R := by
        rw [storedBuffered_reservations, storedBuffered_depths A Z C future.1 W hZ]
        exact hFull p (by simp) h C
      have hz' : Ready A future.1 (fun j col => e.pending.buffer.value (j,col)) :=
        (storedBuffered_boundary A Z C future.1 R W (p h) hr hB).1
      have rec := ih (fun p hp => hFull p (by simp [hp])) e.output future.1
        (fun j col => e.pending.buffer.value (j,col)) hz' future.2
      simpa only [run, rawRun, ←ho] using rec

/-- Initial preparation plus all actual promotions preserve the same experiment. -/
theorem coldRun_refines (A : Fin n → Fin m → F) (W : ℕ)
    (terminal : Phase F H s m n r) (phases : List (Phase F H s m n R))
    (hB : s*m*n = R*W) (hFull : ∀ p ∈ phases, Full A p) (h : H)
    (draws : Samples (Bank F s n) (phases.length+2)) :
    (coldRun A W terminal phases h draws).output =
      (rawRun A terminal phases h draws.1 draws.2).1 ∧
    (coldRun A W terminal phases h draws).current =
      (rawRun A terminal phases h draws.1 draws.2).2 ∧
    Ready A (coldRun A W terminal phases h draws).current
      (coldRun A W terminal phases h draws).prepared := by
  exact run_refines A W terminal phases hB hFull h draws.1 _
    (cursor_complete A draws.1).1 draws.2

#print axioms run_refines
#print axioms coldRun_refines
end ProgressivePool.MultiEpochExecution
