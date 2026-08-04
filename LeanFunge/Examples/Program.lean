/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanFunge.Theory.Program
import LeanFunge.Theory.Step

/-!
# Program Equivalence Examples

Concrete examples of no-op padding preserving program behavior.
-/

namespace LeanFunge.Examples

def haltLeft : Program 2 1 := Grid.ofRows 2 1 [['@', ' ']]

def haltRight : Program 2 1 := Grid.ofRows 2 1 [[' ', '@']]

def haltRightAfterSpace : State 2 1 :=
  { State.init haltRight with
    pc := stepPos 2 1 (State.init haltRight).dir (State.init haltRight).pc }

theorem haltLeft_run_succ (n : ℕ) :
    run (n + 1) (State.init haltLeft) = none := by
  simpa [Nat.add_comm] using
    run_halts_mono (State.init haltLeft) (n := 1) (m := n) (by rfl)

theorem haltRight_run_two_add (n : ℕ) :
    run (n + 2) (State.init haltRight) = none := by
  simpa [Nat.add_comm] using
    run_halts_mono (State.init haltRight) (n := 2) (m := n) (by rfl)

theorem halt_padded_ordered_equiv : Program.ordered_trace_equiv haltLeft haltRight := by
  apply Program.ordered_trace_equiv_of_nop_continuation
  · rfl
  · rfl
  · rfl
  · apply Program.run_observe_eq_of_finite_prefix
      (State.init haltLeft) haltRightAfterSpace 1
    · intro d
      simpa [Nat.add_comm] using haltLeft_run_succ d
    · intro d
      have hrun := Program.run_succ_eq_run_from_step
        (s := State.init haltRight)
        (s' := haltRightAfterSpace)
        (by
          rw [step_nop (State.init haltRight) rfl rfl]
          rfl) (d + 1)
      rw [haltRight_run_two_add d] at hrun
      simpa [Nat.add_comm] using hrun.symm
    · intro n hn
      have : n = 0 := by omega
      subst this
      rfl

def arithmeticPaddedLeft : Program 6 1 :=
  Grid.ofRows 6 1 [(String.toList "23+.@ ")]

def arithmeticPaddedRight : Program 6 1 :=
  Grid.ofRows 6 1 [(String.toList " 23+.@")]

def arithmeticPaddedRightAfterSpace : State 6 1 :=
  { State.init arithmeticPaddedRight with pc := (1, 0) }

theorem arithmeticPaddedRight_step :
    step (State.init arithmeticPaddedRight) =
      some arithmeticPaddedRightAfterSpace := by
  rw [step_nop (State.init arithmeticPaddedRight) rfl (by decide)]
  rfl

theorem arithmeticPaddedLeft_halts (n : ℕ) :
    run (n + 5) (State.init arithmeticPaddedLeft) = none := by
  simpa [Nat.add_comm] using
    run_halts_mono (State.init arithmeticPaddedLeft) (n := 5) (m := n) (by decide)

theorem arithmeticPaddedRight_halts (n : ℕ) :
    run (n + 6) (State.init arithmeticPaddedRight) = none := by
  simpa [Nat.add_comm] using
    run_halts_mono (State.init arithmeticPaddedRight) (n := 6) (m := n) (by decide)

theorem arithmetic_padded_ordered_equiv :
    Program.ordered_trace_equiv arithmeticPaddedLeft arithmeticPaddedRight := by
  apply Program.ordered_trace_equiv_of_nop_continuation
  · decide
  · decide
  · decide
  · apply Program.run_observe_eq_of_finite_prefix
      (State.init arithmeticPaddedLeft) arithmeticPaddedRightAfterSpace 5
    · intro d
      simpa [Nat.add_comm] using arithmeticPaddedLeft_halts d
    · intro d
      have hrun := Program.run_succ_eq_run_from_step
        (s := State.init arithmeticPaddedRight)
        (s' := arithmeticPaddedRightAfterSpace)
        arithmeticPaddedRight_step (d + 5)
      rw [arithmeticPaddedRight_halts d] at hrun
      simpa [Nat.add_comm] using hrun.symm
    · intro n hn
      cases n with
      | zero => decide
      | succ n =>
          cases n with
          | zero => decide
          | succ n =>
              cases n with
              | zero => decide
              | succ n =>
                  cases n with
                  | zero => decide
                  | succ n =>
                      cases n with
                      | zero => decide
                      | succ n => omega

end LeanFunge.Examples
