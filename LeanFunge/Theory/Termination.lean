/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import Mathlib.Data.Nat.Init

/-!
# Termination Analysis

## Main definitions

* `runMachine`: Run a counter machine for finitely many steps.
* `runStep`: Run a transition function from an arbitrary state type.
* `rankedMachine_terminates`: A ranking-function termination principle for any
  state type.
* `countdownNext`: The counter transition of a countdown loop.
* `twoCounterNext`: A two-counter transition.

## Theorems

* `decreasing_seq_bound`: A strictly decreasing sequence of naturals has
  `a k + k` at most `a 0`.
* `decreasing_seq_hits_zero`: A strictly decreasing sequence of naturals
  reaches zero at index `a 0`.
* `runStep_succ`: One more transition step runs one more transition.
* `runStep_shift`: A single transition shifts the run index.
* `runMachine_succ`: One more machine step runs one more transition.
* `runMachine_shift`: A single transition shifts the run index.
* `decreasing_machine_terminates`: A machine whose transitions strictly
  decrease a natural counter halts or reaches counter zero in finitely many
  steps.
* `rankedMachine_terminates`: A machine whose transitions strictly decrease a
  ranking function halts or reaches rank zero in finitely many steps.
* `countdownNext_decreasing`: The countdown transition is strictly decreasing.
* `twoCounterNext_decreasing`: The sum of the two counters strictly decreases.
* `twoCounter_terminates`: The two-counter machine terminates.

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

/-- Run a transition function for a number of steps from an initial state. -/
def runStep (steps : ℕ) {α : Type} (next : α → Option α) (a : α) : Option α :=
  match steps with
  | 0 => some a
  | steps + 1 => (runStep steps next a).bind next

/-- One more transition step runs one more transition. -/
theorem runStep_succ (k : ℕ) {α : Type} (next : α → Option α) (a : α) :
    runStep (k + 1) next a = (runStep k next a).bind next :=
  rfl

/-- A single transition shifts the run index. -/
theorem runStep_shift {α : Type} {next : α → Option α} {a b : α}
    (h : next a = some b) : ∀ k, runStep (Nat.succ k) next a = runStep k next b := by
  intro k
  induction k with
  | zero =>
      rw [runStep_succ]
      change next a = some b
      exact h
  | succ k ih =>
      rw [runStep_succ]
      rw [ih]
      rw [← runStep_succ]

/-- A machine whose transitions strictly decrease a ranking function halts or
    reaches a state of rank `0` within `rank a` steps. -/
theorem rankedMachine_terminates {α : Type} (rank : α → ℕ) (next : α → Option α)
    (hdec : ∀ {a b}, next a = some b → rank b < rank a) (a : α) :
    ∃ steps, steps ≤ rank a ∧
      (match runStep steps next a with
       | none => True
       | some b => rank b = 0) := by
  let P : ℕ → Prop := fun m => ∀ a', rank a' = m → ∃ steps, steps ≤ m ∧
      (match runStep steps next a' with
       | none => True
       | some b => rank b = 0)
  have hmain : P (rank a) := by
    refine Nat.strong_induction_on (rank a) ?_
    intro n ih a' ha'
    cases hnext : next a' with
    | none =>
        by_cases hr : rank a' = 0
        · refine ⟨0, by omega, ?_⟩
          change rank a' = 0
          exact hr
        · refine ⟨1, by omega, ?_⟩
          rw [runStep_succ]
          change (match next a' with | none => True | some b => rank b = 0)
          rw [hnext]
          trivial
    | some b =>
        have hb' : rank b < rank a' := hdec hnext
        have hb : rank b < n := by
          rw [ha'] at hb'
          exact hb'
        rcases ih (rank b) hb b rfl with ⟨steps, hsteps, hterm⟩
        refine ⟨steps + 1, by omega, ?_⟩
        rw [runStep_shift hnext]
        exact hterm
  exact hmain a rfl

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

/-- A two-counter transition: decrement the first counter until zero, then the
    second. -/
def twoCounterNext : ℕ × ℕ → Option (ℕ × ℕ)
  | (0, 0) => none
  | (a + 1, b) => some (a, b)
  | (0, b + 1) => some (0, b)

/-- The sum of the two counters strictly decreases on every transition. -/
theorem twoCounterNext_decreasing {a b : ℕ × ℕ} (h : twoCounterNext a = some b) :
    b.1 + b.2 < a.1 + a.2 := by
  cases a with
  | mk a1 a2 =>
      cases a1 with
      | zero =>
          cases a2 with
          | zero => cases h
          | succ a2 =>
              simp only [twoCounterNext] at h
              injection h with hb
              rw [← hb]
              omega
      | succ a1 =>
          simp only [twoCounterNext] at h
          injection h with hb
          rw [← hb]
          omega

/-- The two-counter machine terminates: within `a + b` steps it reaches the
    zero state. -/
theorem twoCounter_terminates (a b : ℕ) :
    ∃ steps, steps ≤ a + b ∧
      (match runStep steps twoCounterNext (a, b) with
       | none => True
       | some c => c.1 + c.2 = 0) := by
  rcases rankedMachine_terminates (fun s : ℕ × ℕ => s.1 + s.2) twoCounterNext
    twoCounterNext_decreasing (a, b) with ⟨steps, hle, hterm⟩
  refine ⟨steps, ?_, ?_⟩
  · simpa only using hle
  · cases hrun : runStep steps twoCounterNext (a, b) with
    | none => trivial
    | some c =>
        have hc := hterm
        rw [hrun] at hc
        simpa only using hc

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
