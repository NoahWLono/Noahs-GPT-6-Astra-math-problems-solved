import CompletedStoppedInvocation

/-! Epoch counts and ideal field-draw resources of the actual stopping runner.
These count accesses to an ideal independent bank tape. They do not assert a
bit-level random-number implementation or a bound on entropy-source latency. -/
namespace ProgressivePool.EpochResourceBounds
open Classical MultiEpochExecution StoredCheckExecution StoredBufferedExecution
open IndexedPreparation EpochComposition StoppingEpochExecution
variable {F H : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {s m n R r : ℕ}
set_option maxHeartbeats 1200000

/-- Every promoted epoch consumed exactly R invocation reservations. -/
theorem run_reservation_epochs (A : Fin n → Fin m → F) (W : ℕ) (stop : H → Bool)
    (terminal : Phase F H s m n r) (phases : List (Phase F H s m n R))
    (hB : s*m*n = R*W) (hFull : ∀ p ∈ phases, ConditionalFull A stop p)
    (h : H) (C : Bank F s n) (Z : Prepared F s m) (hZ : Ready A C Z)
    (future : Samples (Bank F s n) (phases.length+1)) :
    let actual := StoppingEpochExecution.run A W stop terminal phases h C Z future
    actual.reservations = actual.selectedEpoch*R + actual.localReservations := by
  dsimp only
  induction phases generalizing h C Z with
  | nil => simp [StoppingEpochExecution.run, phaseResult]
  | cons p ps ih =>
      let e := storedBufferedRun A Z C future.1 W (p h) initialCursor
      have ho : e.output = runOutput C (flattenInvocations (mapInvocationInputs A (p h))) :=
        storedBuffered_output A Z C future.1 W hZ (p h) initialCursor
      have hc : e.reservations = (invocationDepths C (mapInvocationInputs A (p h))).length :=
        phase_reservations A W C future.1 Z hZ (p h)
      by_cases hb : stop e.output = true
      · have hbActual : stop (storedBufferedRun A Z C future.1 W (p h) initialCursor).output = true := hb
        simp only [StoppingEpochExecution.run, hbActual, ite_true, phaseResult, Nat.zero_mul, Nat.zero_add]
      · have hfalse : stop (storedBufferedRun A Z C future.1 W (p h) initialCursor).output = false :=
          Bool.eq_false_iff.mpr hb
        have hraw : stop (runOutput C (flattenInvocations (mapInvocationInputs A (p h)))) = false := by
          rw [← ho]; exact hfalse
        have hR : e.reservations = R := hc.trans ((hFull p (by simp) h C).1 hraw)
        have hz' : Ready A future.1 (fun j col => e.pending.buffer.value (j,col)) :=
          (storedBuffered_boundary A Z C future.1 R W (p h) hR hB).1
        have rec := ih (fun p hp => hFull p (by simp [hp])) e.output future.1
          (fun j col => e.pending.buffer.value (j,col)) hz' future.2
        simp only [StoppingEpochExecution.run, hfalse, Bool.false_eq_true, ite_false, prepend]
        change e.reservations +
          (StoppingEpochExecution.run A W stop terminal ps e.output future.1 (fun j col => e.pending.buffer.value (j,col)) future.2).reservations = _
        rw [hR, rec]
        ring

theorem coldRun_reservation_epochs (A : Fin n → Fin m → F) (W : ℕ) (stop : H → Bool)
    (terminal : Phase F H s m n r) (phases : List (Phase F H s m n R))
    (hB : s*m*n = R*W) (hFull : ∀ p ∈ phases, ConditionalFull A stop p)
    (h : H) (draws : Samples (Bank F s n) (phases.length+2)) :
    let actual := StoppingEpochExecution.coldRun A W stop terminal phases h draws
    actual.reservations = actual.selectedEpoch*R + actual.localReservations := by
  exact run_reservation_epochs A W stop terminal phases hB hFull h draws.1 _
    (cursor_complete A draws.1).1 draws.2

/-- The separately executed fresh final invocation adds one reservation in
both the global and final local epoch ledgers. -/
theorem final_reservation_epochs (A : Fin n → Fin m → F) (W : ℕ) (stop : H → Bool)
    (terminal : Phase F H s m n r) (phases : List (Phase F H s m n R))
    (hB : s*m*n = R*W) (hFull : ∀ p ∈ phases, ConditionalFull A stop p)
    (h : H) (draws : Samples (Bank F s n) (phases.length+2))
    (aux : H → Bool) (candidate : H → Input F m n) (t : ℕ) (indices : Fin t → Fin s) :
    let prior := StoppingEpochExecution.coldRun A W stop terminal phases h draws
    (CompletedStoppedInvocation.finish A W aux candidate prior t indices).reservations =
      prior.selectedEpoch*R + (prior.localReservations+1) := by
  dsimp only [CompletedStoppedInvocation.finish]
  rw [coldRun_reservation_epochs A W stop terminal phases hB hFull]
  omega

/-- A prefix with at most N reservations enters at most floor(N/R)+1 epochs. -/
theorem entered_epochs_le_of_reservations_le
    (selected localCount total R N : ℕ) (hR : 0 < R)
    (heq : total = selected*R + localCount) (hN : total ≤ N) :
    selected+1 ≤ N/R+1 := by
  have hh : selected*R ≤ N := by omega
  exact Nat.add_le_add_right ((Nat.le_div_iff_mul_le hR).mpr hh) 1

/-- Concrete conservative epoch allowance for a 64-bit invocation budget. -/
theorem epoch_budget_u64 : (2^64 : ℕ)/262144+1 ≤ 2^64 := by norm_num

/-- Operationally matched ideal lookahead-bank reads: one head at each entered
epoch, and no head in any unentered suffix after stopping. -/
noncomputable def lookaheadReads (A : Fin n → Fin m → F) (W : ℕ) (stop : H → Bool)
    (terminal : Phase F H s m n r) :
    (phases : List (Phase F H s m n R)) → H → Bank F s n → Prepared F s m →
      Samples (Bank F s n) (phases.length+1) → ℕ
  | [], _, _, _, _ => 1
  | p::ps, h, C, Z, future =>
      let e := storedBufferedRun A Z C future.1 W (p h) initialCursor
      if stop e.output then 1 else 1 + lookaheadReads A W stop terminal ps e.output future.1
        (fun j col => e.pending.buffer.value (j,col)) future.2

theorem lookaheadReads_eq (A : Fin n → Fin m → F) (W : ℕ) (stop : H → Bool)
    (terminal : Phase F H s m n r) (phases : List (Phase F H s m n R))
    (h : H) (C : Bank F s n) (Z : Prepared F s m)
    (future : Samples (Bank F s n) (phases.length+1)) :
    lookaheadReads A W stop terminal phases h C Z future =
      (StoppingEpochExecution.run A W stop terminal phases h C Z future).selectedEpoch+1 := by
  induction phases generalizing h C Z with
  | nil => rfl
  | cons p ps ih =>
      simp only [lookaheadReads, StoppingEpochExecution.run]
      split
      · rfl
      · simp only [prepend]
        rw [ih]
        omega

/-- One initial active bank, followed by the entered epochs' lookahead banks. -/
noncomputable def bankHeadReads (A : Fin n → Fin m → F) (W : ℕ) (stop : H → Bool)
    (terminal : Phase F H s m n r) (phases : List (Phase F H s m n R))
    (h : H) (draws : Samples (Bank F s n) (phases.length+2)) : ℕ :=
  let setup := runCursor A draws.1 (s*m*n) initialCursor
  1 + lookaheadReads A W stop terminal phases h draws.1
    (fun j col => setup.buffer.value (j,col)) draws.2

theorem bankHeadReads_eq (A : Fin n → Fin m → F) (W : ℕ) (stop : H → Bool)
    (terminal : Phase F H s m n r) (phases : List (Phase F H s m n R))
    (h : H) (draws : Samples (Bank F s n) (phases.length+2)) :
    bankHeadReads A W stop terminal phases h draws =
      (StoppingEpochExecution.coldRun A W stop terminal phases h draws).selectedEpoch+2 := by
  simp only [bankHeadReads, StoppingEpochExecution.coldRun, lookaheadReads_eq]
  omega

/-- Each ideal bank consists of s*n independent uniform field elements. -/
noncomputable def idealFieldDraws (A : Fin n → Fin m → F) (W : ℕ) (stop : H → Bool)
    (terminal : Phase F H s m n r) (phases : List (Phase F H s m n R))
    (h : H) (draws : Samples (Bank F s n) (phases.length+2)) : ℕ :=
  (s*n) * bankHeadReads A W stop terminal phases h draws

theorem idealFieldDraws_eq (A : Fin n → Fin m → F) (W : ℕ) (stop : H → Bool)
    (terminal : Phase F H s m n r) (phases : List (Phase F H s m n R))
    (h : H) (draws : Samples (Bank F s n) (phases.length+2)) :
    idealFieldDraws A W stop terminal phases h draws =
      (s*n)*((StoppingEpochExecution.coldRun A W stop terminal phases h draws).selectedEpoch+2) := by
  rw [idealFieldDraws, bankHeadReads_eq]


/-- Two banks at cold setup (active and pending), then s*n ideal field draws
for each of the selectedEpoch promotions actually taken. -/
theorem idealFieldDraws_setup_promotions (A : Fin n → Fin m → F) (W : ℕ) (stop : H → Bool)
    (terminal : Phase F H s m n r) (phases : List (Phase F H s m n R))
    (h : H) (draws : Samples (Bank F s n) (phases.length+2)) :
    idealFieldDraws A W stop terminal phases h draws =
      2*(s*n) + (StoppingEpochExecution.coldRun A W stop terminal phases h draws).selectedEpoch*(s*n) := by
  rw [idealFieldDraws_eq]
  ring

/-- Continuing into the next epoch entails exactly one new lookahead-bank
burst, s*n ideal field draws, before the remaining suffix's later reads. -/
theorem promotion_field_draw_burst (A : Fin n → Fin m → F) (W : ℕ) (stop : H → Bool)
    (terminal : Phase F H s m n r) (p : Phase F H s m n R)
    (ps : List (Phase F H s m n R)) (h : H) (C : Bank F s n) (Z : Prepared F s m)
    (future : Samples (Bank F s n) ((p::ps).length+1))
    (hcontinue : stop (storedBufferedRun A Z C future.1 W (p h) initialCursor).output = false) :
    (s*n)*lookaheadReads A W stop terminal (p::ps) h C Z future =
      s*n + (s*n)*lookaheadReads A W stop terminal ps
        (storedBufferedRun A Z C future.1 W (p h) initialCursor).output future.1
        (fun j col => (storedBufferedRun A Z C future.1 W (p h) initialCursor).pending.buffer.value (j,col))
        future.2 := by
  simp only [lookaheadReads, hcontinue, Bool.false_eq_true, ite_false, Nat.mul_add, Nat.mul_one]

#print axioms run_reservation_epochs
#print axioms coldRun_reservation_epochs
#print axioms final_reservation_epochs
#print axioms epoch_budget_u64
#print axioms bankHeadReads_eq
#print axioms idealFieldDraws_eq
#print axioms promotion_field_draw_burst
end ProgressivePool.EpochResourceBounds
