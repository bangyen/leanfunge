/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanFunge.Theory.Program

/-!
# Program Equivalence Examples

Concrete examples of no-op padding preserving program behavior.
-/

namespace LeanFunge.Examples

def haltLeft : Program 2 1 := Grid.ofRows 2 1 [['@', ' ']]

def haltRight : Program 2 1 := Grid.ofRows 2 1 [[' ', '@']]

theorem haltLeft_run_succ (n : ℕ) :
    run (n + 1) (State.init haltLeft) = none := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change (run (n + 1) (State.init haltLeft)).bind step = none
      rw [ih]
      rfl

theorem haltRight_run_two_add (n : ℕ) :
    run (n + 2) (State.init haltRight) = none := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change (run (n + 2) (State.init haltRight)).bind step = none
      rw [ih]
      rfl

theorem halt_padded_ordered_equiv : Program.ordered_trace_equiv haltLeft haltRight := by
  apply Program.ordered_trace_equiv_one_step_prefix
  · rfl
  · intro n
    cases n with
    | zero => rfl
    | succ n =>
        rw [haltLeft_run_succ n, haltRight_run_two_add n]

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
  induction n with
  | zero => decide
  | succ n ih =>
      change (run (n + 5) (State.init arithmeticPaddedLeft)).bind step = none
      rw [ih]
      rfl

theorem arithmeticPaddedRight_halts (n : ℕ) :
    run (n + 6) (State.init arithmeticPaddedRight) = none := by
  induction n with
  | zero => decide
  | succ n ih =>
      change (run (n + 6) (State.init arithmeticPaddedRight)).bind step = none
      rw [ih]
      rfl

theorem arithmetic_padded_ordered_equiv :
    Program.ordered_trace_equiv arithmeticPaddedLeft arithmeticPaddedRight := by
  apply Program.ordered_trace_equiv_of_step_continuation
    arithmeticPaddedRightAfterSpace
  · exact arithmeticPaddedRight_step
  · decide
  · intro n
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
                    | succ n =>
                        have hrun := Program.run_succ_eq_run_from_step
                          (s := State.init arithmeticPaddedRight)
                          (s' := arithmeticPaddedRightAfterSpace)
                          arithmeticPaddedRight_step (n + 5)
                        rw [arithmeticPaddedRight_halts n] at hrun
                        rw [arithmeticPaddedLeft_halts n]
                        rw [← hrun]

end LeanFunge.Examples
