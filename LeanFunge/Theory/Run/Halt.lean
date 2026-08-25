/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanFunge.Core.Semantics
import LeanFunge.Theory.Run.Relational
import Mathlib.Data.Nat.Notation
import Mathlib.Logic.ExistsUnique

/-!
# Run-Level Halting Characterization

A program halts exactly when the instruction pointer reaches the `@` cell
outside string mode. This module makes that precise: the single-step halting
condition is a `halt` instruction at the pointer outside string mode, and a
finite run halts exactly when some intermediate state satisfies it. That
halting configuration is moreover unique, so the output of a halting program
is well defined.

## Theorems

* `decodeChar_halt_iff`: A character decodes to the halt instruction exactly
  when it is `@`.
* `step_none_iff_halt`: A step halts exactly when the pointer is outside
  string mode at a halt cell.
* `run_none_exists_halt`: A halting run reaches a state whose next step halts.
* `halts_iff_reaches_halt`: A run halts exactly when it reaches a state whose
  next step halts.
* `halts_iff`: A run halts exactly when it reaches a halt cell outside
  string mode.
* `halts_iff_at`: A run halts exactly when it reaches the `@` cell outside
  string mode.
* `halts_of_at_cell`: Reaching the `@` cell outside string mode halts the run.
* `run_none_add`: Once a run yields `none`, running longer still does.
* `halts_iff_of_run`: Halting transports across a finite prefix of a run.
* `run_none_stays_none`: Once a run has halted it stays halted.
* `halt_unique`: A run reaches at most one halting configuration, at one step
  count.
* `halt_output_unique`: The output of a halting run is unique.
* `halts_unique_final`: A halting run has a unique final state, reached at a
  unique step count — for a fixed program and input the output is determined.
-/

namespace LeanFunge

/-- A character decodes to `halt` exactly when it is `@`. -/
theorem decodeChar_halt_iff (c : Char) : decodeChar c = .halt ↔ c = '@' := by
  constructor
  · intro h
    unfold decodeChar at h
    split at h <;> simp only [reduceCtorEq] at h
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
    | true => simp only [hsm, reduceCtorEq] at h
    | false =>
        rw [hsm] at h
        cases hdec : decodeChar (s.grid.get s.pc.1 s.pc.2) with
        | halt => exact ⟨by simp only [Bool.false_eq_true, not_false_eq_true]
            , rfl⟩
        | _ => simp only [hdec, reduceCtorEq] at h
  · intro h
    rcases h with ⟨hsm, hdec⟩
    unfold step
    cases hm : s.stringMode with
    | true => exfalso; exact hsm (by simp only [hm])
    | false => simp only [hdec]

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

/-- Once a run yields `none`, running longer still yields `none`. -/
theorem run_none_add (s : State w h) {n : ℕ} (hn : run n s = none) (m : ℕ) :
    run (n + m) s = none := by
  induction m with
  | zero => simpa only [Nat.add_zero] using hn
  | succ j ih => rw [← Nat.add_assoc] at *; rw [run, ih]; rfl

/-- Halting transports across a finite prefix of a run: a state halts exactly
    when any state it reaches halts. The reachable state stands in for the
    original, which is what lets a bootstrap prefix be discharged. -/
theorem halts_iff_of_run (s s' : State w h) (k : ℕ)
    (hk : run k s = some s') : halts s ↔ halts s' := by
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨n - k, ?_⟩
    rcases Nat.lt_or_ge n k with hlt | hle
    · -- `s` already halted before reaching `s'`, contradicting `run k s = some s'`
      exfalso
      have hsplit := run_none_add s hn (k - n)
      rw [Nat.add_sub_cancel' (Nat.le_of_lt hlt)] at hsplit
      rw [hsplit] at hk; cases hk
    · cases hr : run (n - k) s' with
      | none => rfl
      | some t =>
          exfalso
          have hcomp : run (k + (n - k)) s = some t :=
            run_append s s' (some t) k (n - k) hk hr
          rw [Nat.add_sub_cancel' hle] at hcomp
          rw [hcomp] at hn; cases hn
  · rintro ⟨n, hn⟩
    exact ⟨k + n, run_append s s' none k n hk hn⟩

/-- Once a run has halted it stays halted: no later step count revives it. -/
theorem run_none_stays_none (s : State w h) (k : ℕ) (hs : step s = none)
    (hk : 0 < k) : run k s = none := by
  rcases k with _ | k
  · exact absurd hk (by decide)
  · clear hk
    induction k with
    | zero => rw [run, run]; exact hs
    | succ k ih => rw [run, ih]; rfl

/-- A run reaches at most one halting configuration, at one step count: the
    `@` the pointer reaches, and when it reaches it, are both determined. -/
theorem halt_unique (s : State w h) {m m' : ℕ} {sₘ sₘ' : State w h}
    (hr : run m s = some sₘ) (hs : step sₘ = none)
    (hr' : run m' s = some sₘ') (hs' : step sₘ' = none) :
    m = m' ∧ sₘ = sₘ' := by
  have key : ∀ (a b : ℕ) (sa sb : State w h), a ≤ b →
      run a s = some sa → step sa = none → run b s = some sb →
      a = b ∧ sa = sb := by
    intro a b sa sb hab ha hsa hb
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hab
    rcases Nat.eq_zero_or_pos k with hk | hk
    · subst hk
      rw [Nat.add_zero] at hb
      rw [ha] at hb
      injection hb with hb
      exact ⟨rfl, hb⟩
    · have hnone : run (a + k) s = none := run_append s sa none a k ha
        (run_none_stays_none sa k hsa hk)
      rw [hnone] at hb
      cases hb
  rcases Nat.le_total m m' with hle | hle
  · exact key m m' sₘ sₘ' hle hr hs hr'
  · obtain ⟨he, hse⟩ := key m' m sₘ' sₘ hle hr' hs' hr
    exact ⟨he.symm, hse.symm⟩

/-- The output of a halting run is unique. -/
theorem halt_output_unique (s : State w h) {m m' : ℕ} {sₘ sₘ' : State w h}
    (hr : run m s = some sₘ) (hs : step sₘ = none)
    (hr' : run m' s = some sₘ') (hs' : step sₘ' = none) :
    sₘ.output = sₘ'.output := by
  rw [(halt_unique s hr hs hr' hs').2]

/-- A halting run has a unique final state, reached at a unique step count: for
    a fixed program and input the resulting output is determined. -/
theorem halts_unique_final (s : State w h) (hh : halts s) :
    ∃! p : ℕ × State w h, run p.1 s = some p.2 ∧ step p.2 = none := by
  rcases (halts_iff_reaches_halt s).mp hh with ⟨m, sₘ, hr, hs⟩
  refine ⟨(m, sₘ), ⟨hr, hs⟩, ?_⟩
  rintro ⟨m', sₘ'⟩ ⟨hr', hs'⟩
  obtain ⟨he, hse⟩ := halt_unique s hr' hs' hr hs
  simp only [Prod.mk.injEq]
  exact ⟨he, hse⟩

end LeanFunge
