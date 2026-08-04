/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import Mathlib.Data.Nat.Init

/-!
# Termination Analysis

## Theorems

* `decreasing_seq_bound`: A strictly decreasing sequence of naturals has
  `a k + k` at most `a 0`.
* `decreasing_seq_hits_zero`: A strictly decreasing sequence of naturals
  reaches zero at index `a 0`.
* `runMachine_succ`: One more machine step runs one more transition.
* `runMachine_shift`: A single transition shifts the run index.
* `decreasing_machine_terminates`: A machine whose transitions strictly
  decrease a natural counter halts or reaches counter zero in finitely many
  steps.
* `countdownNext_decreasing`: The countdown transition is strictly decreasing.

A countdown loop — such as the Countdown and Factorial examples, whose cell
counters strictly decrease toward zero — is exactly such a machine, so these
theorems provide its termination analysis.
-/

namespace LeanFunge

/-- A strictly decreasing sequence of naturals from `a 0` has `a k + k ≤ a 0`.
    Every step decreases the value by at least one. -/
theorem decreasing_seq_bound {a : ℕ → ℕ} (hdec : ∀ k, a (k + 1) < a k) :
    ∀ k, a k + k ≤ a 0 := by
  intro k
  induction k with
  | zero => omega
  | succ k ih =>
      have h1 : a (k + 1) + 1 ≤ a k := Nat.succ_le_of_lt (hdec k)
      have hstep : a (k + 1) + 1 + k ≤ a 0 := by
        omega
      omega

/-- A strictly decreasing sequence of naturals reaches `0` at index `a 0`. -/
theorem decreasing_seq_hits_zero {a : ℕ → ℕ} (hdec : ∀ k, a (k + 1) < a k) :
    a (a 0) = 0 := by
  have hb := decreasing_seq_bound hdec (a 0)
  omega

/-- Run a machine for a number of steps from an initial counter. -/
def runMachine (steps : ℕ) (next : ℕ → Option ℕ) (n : ℕ) : Option ℕ :=
  match steps with
  | 0 => some n
  | steps + 1 => (runMachine steps next n).bind next

/-- One more machine step runs one more transition. -/
theorem runMachine_succ (k : ℕ) (next : ℕ → Option ℕ) (n : ℕ) :
    runMachine (k + 1) next n = (runMachine k next n).bind next :=
  rfl

/-- A single transition shifts the run index: if `next n = some m`, then
    running `k + 1` steps from `n` is running `k` steps from `m`. -/
theorem runMachine_shift {next : ℕ → Option ℕ} {n m : ℕ} (h : next n = some m) :
    ∀ k, runMachine (Nat.succ k) next n = runMachine k next m := by
  intro k
  induction k with
  | zero =>
      rw [runMachine_succ]
      change next n = some m
      exact h
  | succ k ih =>
      rw [runMachine_succ]
      rw [ih]
      rw [← runMachine_succ]

/-- A machine whose transitions strictly decrease a natural counter halts or
    reaches counter `0` within `n` steps. -/
theorem decreasing_machine_terminates {next : ℕ → Option ℕ}
    (hdec : ∀ {n m}, next n = some m → m < n) (n : ℕ) :
    ∃ steps, steps ≤ n ∧
      (match runMachine steps next n with
       | none => True
       | some m => m = 0) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      cases hnext : next n with
      | none =>
          by_cases hn : n = 0
          · subst n
            refine ⟨0, by omega, ?_⟩
            rfl
          · refine ⟨1, by omega, ?_⟩
            rw [runMachine_succ]
            change (match next n with | none => True | some m => m = 0)
            rw [hnext]
            trivial
      | some m =>
          have hm : m < n := hdec hnext
          rcases ih m hm with ⟨steps, hsteps, hterm⟩
          refine ⟨steps + 1, by omega, ?_⟩
          rw [runMachine_shift hnext]
          exact hterm

/-- The counter transition of a countdown loop: `n + 1` steps down to `n`, and
    `0` halts. -/
def countdownNext : ℕ → Option ℕ
  | 0 => none
  | n + 1 => some n

/-- The countdown transition is strictly decreasing. -/
theorem countdownNext_decreasing {n m : ℕ} (h : countdownNext n = some m) :
    m < n := by
  cases n with
  | zero => cases h
  | succ n =>
      simp only [countdownNext] at h
      injection h with hn
      omega

end LeanFunge
