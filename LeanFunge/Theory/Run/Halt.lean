/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanFunge.Core.Semantics
import Mathlib.Data.Nat.Notation

/-!
# Run-Level Halting Characterization

A program halts exactly when the instruction pointer reaches the `@` cell
outside string mode. This module makes that precise: the single-step halting
condition is a `halt` instruction at the pointer outside string mode, and a
finite run halts exactly when some intermediate state satisfies it.

## Theorems

* `decodeChar_halt_iff`: A character decodes to `halt` exactly when it is `@`.
* `step_none_iff_halt`: A step halts exactly when the pointer is outside
  string mode at a `halt` cell.
* `run_none_exists_halt`: A halting run reaches a state whose next step halts.
* `halts_iff_reaches_halt`: A run halts exactly when it reaches a state whose
  next step halts.
* `halts_iff`: A run halts exactly when it reaches a `halt` cell outside
  string mode.
* `halts_iff_at`: A run halts exactly when it reaches the `@` cell outside
  string mode.
* `halts_of_at_cell`: Reaching the `@` cell outside string mode halts the run.
-/

namespace LeanFunge

/-- A character decodes to `halt` exactly when it is `@`. -/
theorem decodeChar_halt_iff (c : Char) : decodeChar c = .halt ↔ c = '@' := by
  constructor
  · intro h
    unfold decodeChar at h
    split at h <;> simp at h
    · rfl
  · intro h
    rw [h]
    rfl

/-- A step halts exactly when the pointer is outside string mode at a `halt`
    cell. -/
theorem step_none_iff_halt (s : State w h) :
    step s = none ↔ (¬ s.stringMode ∧ decodeChar (s.grid.get s.pc.1 s.pc.2) = .halt) := by
  constructor
  · intro h
    unfold step at h
    cases hsm : s.stringMode with
    | true => simp [hsm] at h
    | false =>
        rw [hsm] at h
        cases hdec : decodeChar (s.grid.get s.pc.1 s.pc.2) with
        | halt => exact ⟨by simp, rfl⟩
        | _ => simp [hdec] at h
  · intro h
    rcases h with ⟨hsm, hdec⟩
    unfold step
    cases hm : s.stringMode with
    | true => exfalso; exact hsm (by simp [hm])
    | false => simp [hdec]

/-- A halting run reaches a state whose next step halts. -/
theorem run_none_exists_halt (s : State w h) (n : ℕ) (hnone : run n s = none) :
    ∃ (m : ℕ) (sₘ : State w h), m < n ∧ run m s = some sₘ ∧ step sₘ = none := by
  induction n with
  | zero =>
      rw [run] at hnone
      cases hnone
  | succ n ih =>
      rcases hrun : run n s with _ | sₙ
      · rcases ih hrun with ⟨m, sₘ, hm, hr, hs⟩
        refine ⟨m, sₘ, Nat.lt_trans hm (Nat.lt_succ_self n), hr, hs⟩
      · rw [run, hrun] at hnone
        have hstep : step sₙ = none := by simpa only using hnone
        exact ⟨n, sₙ, Nat.lt_succ_self n, hrun, hstep⟩

/-- A run halts exactly when it reaches a state whose next step halts. -/
theorem halts_iff_reaches_halt (s : State w h) :
    halts s ↔ ∃ (m : ℕ) (sₘ : State w h), run m s = some sₘ ∧ step sₘ = none := by
  constructor
  · intro h
    rcases h with ⟨n, hn⟩
    rcases run_none_exists_halt s n hn with ⟨m, sₘ, _hm, hr, hs⟩
    exact ⟨m, sₘ, hr, hs⟩
  · intro h
    rcases h with ⟨m, sₘ, hr, hs⟩
    refine ⟨m + 1, ?_⟩
    rw [run]
    rw [hr]
    exact hs

/-- A run halts exactly when it reaches a `halt` cell outside string mode. -/
theorem halts_iff (s : State w h) :
    halts s ↔ ∃ (m : ℕ) (sₘ : State w h),
      run m s = some sₘ ∧ ¬ sₘ.stringMode ∧
        decodeChar (sₘ.grid.get sₘ.pc.1 sₘ.pc.2) = .halt := by
  rw [halts_iff_reaches_halt]
  constructor
  · intro h
    rcases h with ⟨m, sₘ, hr, hs⟩
    exact ⟨m, sₘ, hr, (step_none_iff_halt sₘ).mp hs⟩
  · intro h
    rcases h with ⟨m, sₘ, hr, hh⟩
    exact ⟨m, sₘ, hr, (step_none_iff_halt sₘ).mpr hh⟩

/-- A run halts exactly when it reaches the `@` cell outside string mode. -/
theorem halts_iff_at (s : State w h) :
    halts s ↔ ∃ (m : ℕ) (sₘ : State w h),
      run m s = some sₘ ∧ ¬ sₘ.stringMode ∧ sₘ.grid.get sₘ.pc.1 sₘ.pc.2 = '@' := by
  rw [halts_iff]
  constructor
  · intro h
    rcases h with ⟨m, sₘ, hr, hsm, hdec⟩
    exact ⟨m, sₘ, hr, hsm, (decodeChar_halt_iff _).mp hdec⟩
  · intro h
    rcases h with ⟨m, sₘ, hr, hsm, hat⟩
    exact ⟨m, sₘ, hr, hsm, (decodeChar_halt_iff _).mpr hat⟩

/-- Reaching the `@` cell outside string mode halts the run. -/
theorem halts_of_at_cell (s : State w h) (m : ℕ) (sₘ : State w h)
    (hr : run m s = some sₘ) (hsm : ¬ sₘ.stringMode)
    (hat : sₘ.grid.get sₘ.pc.1 sₘ.pc.2 = '@') : halts s := by
  rw [halts_iff_at]
  exact ⟨m, sₘ, hr, hsm, hat⟩

end LeanFunge
