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
      (State.init haltLeft) (Program.nop_successor (State.init haltRight)) 1
    · intro d
      simpa [Nat.add_comm] using haltLeft_run_succ d
    · intro d
      have hrun := Program.run_succ_eq_run_from_step
        (s := State.init haltRight)
        (s' := Program.nop_successor (State.init haltRight))
        (Program.step_nop_successor (State.init haltRight) rfl rfl) (d + 1)
      rw [haltRight_run_two_add d] at hrun
      simpa [Nat.add_comm] using hrun.symm
    · intro n hn
      have : n = 0 := by omega
      subst this
      rfl

def arithmeticOriginal : Program 5 1 :=
  Grid.ofRows 5 1 [(String.toList "23+.@")]

def arithmeticPaddedLeft : Program 6 1 :=
  Grid.ofRows 6 1 [(String.toList "23+.@ ")]

def arithmeticPaddedRight : Program 6 1 :=
  Grid.ofRows 6 1 [(String.toList " 23+.@")]

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
      (State.init arithmeticPaddedLeft)
      (Program.nop_successor (State.init arithmeticPaddedRight)) 5
    · intro d
      simpa [Nat.add_comm] using arithmeticPaddedLeft_halts d
    · intro d
      have hrun := Program.run_succ_eq_run_from_step
        (s := State.init arithmeticPaddedRight)
        (s' := Program.nop_successor (State.init arithmeticPaddedRight))
        (Program.step_nop_successor (State.init arithmeticPaddedRight) rfl (by decide))
        (d + 5)
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

def arithmeticLeadingSpace : Program 6 1 :=
  Grid.prependSpace arithmeticOriginal

theorem arithmeticOriginal_halts (n : ℕ) :
    run (n + 5) (State.init arithmeticOriginal) = none := by
  simpa [Nat.add_comm] using
    run_halts_mono (State.init arithmeticOriginal) (n := 5) (m := n) (by decide)

theorem arithmeticLeadingSpace_halts (n : ℕ) :
    run (n + 6) (State.init arithmeticLeadingSpace) = none := by
  simpa [Nat.add_comm] using
    run_halts_mono (State.init arithmeticLeadingSpace) (n := 6) (m := n) (by decide)

theorem arithmetic_leading_space_ordered_equiv :
    Program.ordered_trace_equiv_between arithmeticOriginal arithmeticLeadingSpace := by
  apply Program.ordered_trace_equiv_between_one_step_prefix
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
                        rw [arithmeticOriginal_halts n,
                          arithmeticLeadingSpace_halts n]
                        rfl

def arithmeticPaddingRelation (s : State 5 1) (t : State 6 1) : Prop :=
  ∃ n, n < 5 ∧ run n (State.init arithmeticOriginal) = some s ∧
    run (n + 1) (State.init arithmeticLeadingSpace) = some t

theorem arithmeticOriginal_next_some (n : ℕ) (hn : n < 4) :
    ∃ s, run (n + 1) (State.init arithmeticOriginal) = some s := by
  cases n with
  | zero => exact ⟨_, rfl⟩
  | succ n =>
      cases n with
      | zero => exact ⟨_, rfl⟩
      | succ n =>
          cases n with
          | zero => exact ⟨_, rfl⟩
          | succ n =>
              cases n with
              | zero => exact ⟨_, rfl⟩
              | succ n => omega

theorem arithmeticLeadingSpace_next_some (n : ℕ) (hn : n < 4) :
    ∃ t, run (n + 2) (State.init arithmeticLeadingSpace) = some t := by
  cases n with
  | zero => exact ⟨_, rfl⟩
  | succ n =>
      cases n with
      | zero => exact ⟨_, rfl⟩
      | succ n =>
          cases n with
          | zero => exact ⟨_, rfl⟩
          | succ n =>
              cases n with
              | zero => exact ⟨_, rfl⟩
              | succ n => omega

theorem arithmetic_padding_observe (n : ℕ) :
    Program.observe (run n (State.init arithmeticOriginal)) =
      Program.observe (run (n + 1) (State.init arithmeticLeadingSpace)) := by
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
                      rw [arithmeticOriginal_halts n, arithmeticLeadingSpace_halts n]
                      rfl

theorem arithmetic_padding_state_simulation :
    Program.state_simulation arithmeticPaddingRelation := by
  intro s t hst
  rcases hst with ⟨n, hn, hs, ht⟩
  have hobs : Program.observe (some s) = Program.observe (some t) := by
    have hshift := arithmetic_padding_observe n
    rw [hs, ht] at hshift
    exact hshift
  refine ⟨hobs, ?_, ?_, ?_⟩
  · constructor
    · intro hhalt
      by_cases hsmall : n < 4
      · rcases arithmeticOriginal_next_some n hsmall with ⟨s', hs'⟩
        rw [run, hs] at hs'
        change step s = some s' at hs'
        rw [hhalt] at hs'
        contradiction
      · have : n = 4 := by omega
        subst this
        have hnone := arithmeticLeadingSpace_halts 0
        rw [run, ht] at hnone
        change step t = none at hnone
        exact hnone
    · intro hhalt
      by_cases hsmall : n < 4
      · rcases arithmeticLeadingSpace_next_some n hsmall with ⟨t', ht'⟩
        rw [run, ht] at ht'
        change step t = some t' at ht'
        rw [hhalt] at ht'
        contradiction
      · have : n = 4 := by omega
        subst this
        have hnone := arithmeticOriginal_halts 0
        rw [run, hs] at hnone
        change step s = none at hnone
        exact hnone
  · intro s' hstep
    have hsmall : n < 4 := by
      by_contra hnsmall
      have hn4 : n = 4 := by omega
      subst n
      have hnone := arithmeticOriginal_halts 0
      rw [run, hs] at hnone
      change step s = none at hnone
      rw [hstep] at hnone
      cases hnone
    rcases arithmeticLeadingSpace_next_some n hsmall with ⟨t', ht'⟩
    have hnext : step t = some t' := by
      rw [run, ht] at ht'
      change step t = some t' at ht'
      exact ht'
    refine ⟨t', hnext, ?_⟩
    refine ⟨n + 1, by omega, ?_, ?_⟩
    · rw [run, hs]
      change step s = some s'
      exact hstep
    · exact ht'
  · intro t' hstep
    have hsmall : n < 4 := by
      by_contra hnsmall
      have hn4 : n = 4 := by omega
      subst n
      have hnone := arithmeticLeadingSpace_halts 0
      rw [run, ht] at hnone
      change step t = none at hnone
      rw [hstep] at hnone
      cases hnone
    rcases arithmeticOriginal_next_some n hsmall with ⟨s', hs'⟩
    have hnext : step s = some s' := by
      rw [run, hs] at hs'
      change step s = some s' at hs'
      exact hs'
    refine ⟨s', hnext, ?_⟩
    refine ⟨n + 1, by omega, ?_, ?_⟩
    · exact hs'
    · rw [run, ht]
      change step t = some t'
      exact hstep

theorem arithmetic_padding_continuation_observe (n : ℕ) :
    Program.observe (run n (State.init arithmeticOriginal)) =
      Program.observe (run n (Program.nop_successor
        (State.init arithmeticLeadingSpace))) := by
  apply Program.run_observations_of_state_simulation
    arithmetic_padding_state_simulation
  refine ⟨0, by decide, rfl, ?_⟩
  change step (State.init arithmeticLeadingSpace) =
    some (Program.nop_successor (State.init arithmeticLeadingSpace))
  exact Program.step_nop_successor (State.init arithmeticLeadingSpace) rfl (by decide)

theorem arithmetic_leading_space_bisim_equiv :
    Program.ordered_trace_equiv_between arithmeticOriginal arithmeticLeadingSpace := by
  apply Program.ordered_trace_equiv_between_one_step_prefix
  · decide
  · intro n
    rw [Program.run_succ_eq_run_from_step
      (Program.step_nop_successor (State.init arithmeticLeadingSpace) rfl (by decide))]
    exact arithmetic_padding_continuation_observe n

def rotatedArithmeticState : State 1 5 :=
  Program.rotateCWState (State.init arithmeticOriginal)

theorem rotated_arithmetic_output :
    (run 4 rotatedArithmeticState).map (fun s => s.output) = some "5" := by
  decide

theorem rotated_arithmetic_halts : run 5 rotatedArithmeticState = none := by
  decide

def rotateCounter : Program 2 2 :=
  Grid.ofRows 2 2 [['1', '_'], ['@', ' ']]

theorem rotateCounter_step1 :
    Program.observe (run 1 (State.init rotateCounter)) = some ([1], "") := by
  decide

theorem rotateCounterRotated_halts :
    run 1 (State.init (Grid.rotateCW rotateCounter)) = none := by
  decide

/-- Clockwise rotation changes the behavior of a program using `_`: the
    original pushes `1` while the rotated program halts immediately, so
    rotation is not sound in general. -/
theorem arithmetic_io_behavior :
    Program.ioBehavior (State.init arithmeticOriginal) 4 = some ([], "5") := by
  decide

theorem rotateCounter_not_ordered_equiv :
    ¬ Program.ordered_trace_equiv_between rotateCounter (Grid.rotateCW rotateCounter) := by
  intro h
  rcases h with ⟨f, g, hf, hg, hforward, hbackward⟩
  have hm := hforward 1
  rw [rotateCounter_step1] at hm
  cases h : f 1 with
  | zero =>
      have h0 : run 0 (State.init (Grid.rotateCW rotateCounter)) =
        some (State.init (Grid.rotateCW rotateCounter)) := rfl
      rw [h, h0] at hm
      change some ([1], "") = some ([] , "") at hm
      injection hm with h1
      injection h1 with h2 h3
      exact (by decide : ¬ ([1] : Stack) = ([] : Stack)) h2
  | succ m =>
      have haltm : run (m + 1) (State.init (Grid.rotateCW rotateCounter)) = none := by
        simpa [Nat.add_comm] using run_halts_mono
          (State.init (Grid.rotateCW rotateCounter)) (n := 1) (m := m)
          rotateCounterRotated_halts
      rw [h, haltm] at hm
      cases hm

end LeanFunge.Examples
