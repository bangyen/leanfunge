/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanFunge.Theory.Termination

/-!
# Termination Tests
-/

namespace LeanFunge.Tests

open LeanFunge

example {a : ℕ → ℕ} (hdec : ∀ k, a (k + 1) < a k) : a (a 0) = 0 :=
  decreasing_seq_hits_zero hdec

example {a : ℕ → ℕ} (hdec : ∀ k, a (k + 1) < a k) (k : ℕ) : a k + k ≤ a 0 :=
  decreasing_seq_bound hdec k

example : ∃ steps, steps ≤ 3 ∧
    (match runMachine steps countdownNext 3 with | none => True | some m => m = 0) :=
  decreasing_machine_terminates (next := countdownNext) (hdec := countdownNext_decreasing) 3

example : runMachine 3 countdownNext 3 = some 0 := by
  decide

example {n m : ℕ} (h : countdownNext n = some m) : m < n :=
  countdownNext_decreasing h

example {α : Type} (rank : α → ℕ) (next : α → Option α)
    (hdec : ∀ {a b}, next a = some b → rank b < rank a) (a : α) :
    ∃ steps, steps ≤ rank a ∧
      (match runStep steps next a with | none => True | some b => rank b = 0) :=
  rankedMachine_terminates rank next hdec a

example {a b : ℕ × ℕ} (h : twoCounterNext a = some b) : b.1 + b.2 < a.1 + a.2 :=
  twoCounterNext_decreasing h

example (a b : ℕ) :
    ∃ steps, steps ≤ a + b ∧
      (match runStep steps twoCounterNext (a, b) with
       | none => True
       | some c => c.1 + c.2 = 0) :=
  twoCounter_terminates a b

end LeanFunge.Tests
