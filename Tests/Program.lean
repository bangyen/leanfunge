/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanFunge.Theory.Program

/-!
# Program Equivalence Tests
-/

namespace LeanFunge.Tests

open LeanFunge

example (p : Program w h) : Program.equiv p p :=
  Program.equiv_refl p

example {p q : Program w h} (h : Program.equiv p q) : Program.equiv q p :=
  Program.equiv_symm h

example {p q r : Program w h} (hpq : Program.equiv p q) (hqr : Program.equiv q r) :
    Program.equiv p r :=
  Program.equiv_trans hpq hqr

example {p q : Program w h} (h : Program.equiv p q) :
    Program.observational_equiv p q :=
  Program.equiv_observational_equiv h

example (p : Program w h) : Program.observational_equiv p p :=
  Program.observational_equiv_refl p

example {p q : Program w h} (h : Program.observational_equiv p q) :
    Program.observational_equiv q p :=
  Program.observational_equiv_symm h

example {p q r : Program w h}
    (hpq : Program.observational_equiv p q)
    (hqr : Program.observational_equiv q r) :
    Program.observational_equiv p r :=
  Program.observational_equiv_trans hpq hqr

example {p q : Program w h} (h : Program.observational_equiv p q) :
    Program.trace_equiv p q :=
  Program.observational_equiv_trace_equiv h

example (p : Program w h) : Program.trace_equiv p p :=
  Program.trace_equiv_refl p

example {p q : Program w h} (h : Program.trace_equiv p q) : Program.trace_equiv q p :=
  Program.trace_equiv_symm h

example {p q r : Program w h}
    (hpq : Program.trace_equiv p q) (hqr : Program.trace_equiv q r) :
    Program.trace_equiv p r :=
  Program.trace_equiv_trans hpq hqr

example {p q : Program w h} (h : Program.observational_equiv p q) :
    Program.ordered_trace_equiv p q :=
  Program.observational_equiv_ordered_trace_equiv h

example (p : Program w h) : Program.ordered_trace_equiv p p :=
  Program.ordered_trace_equiv_refl p

example {p q : Program w h} (h : Program.ordered_trace_equiv p q) :
    Program.ordered_trace_equiv q p :=
  Program.ordered_trace_equiv_symm h

example {p q r : Program w h}
    (hpq : Program.ordered_trace_equiv p q)
    (hqr : Program.ordered_trace_equiv q r) :
    Program.ordered_trace_equiv p r :=
  Program.ordered_trace_equiv_trans hpq hqr

example {w h : ℕ} (s : State w h) (hm : s.stringMode = false)
    (hcell : s.grid.get s.pc.1 s.pc.2 = ' ') :
    Program.observe (step s) = some (s.stack, s.output) :=
  Program.step_nop_observe s hm hcell

example {w h : ℕ} (s : State w h) (n : ℕ) (s' : State w h)
    (h : run n s = some s')
    (hn : ∀ k, k ≤ n → ∀ sₖ, run k s = some sₖ →
      sₖ.stringMode = false ∧ decodeChar (sₖ.grid.get sₖ.pc.1 sₖ.pc.2) = .nop) :
    Program.observe (run n s) = some (s.stack, s.output) :=
  Program.run_nop_observe s n s' h hn

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

example : Program.trace_equiv haltLeft haltRight := by
  constructor
  · intro n
    cases n with
    | zero => exact ⟨0, rfl⟩
    | succ n =>
        refine ⟨2, ?_⟩
        rw [haltLeft_run_succ, haltRight_run_two_add]
  · intro n
    cases n with
    | zero => exact ⟨0, rfl⟩
    | succ n =>
        cases n with
        | zero => exact ⟨0, rfl⟩
        | succ n =>
            refine ⟨1, ?_⟩
            rw [haltLeft_run_succ, haltRight_run_two_add]

example : Program.ordered_trace_equiv haltLeft haltRight := by
  let f : ℕ → ℕ := fun n => if n = 0 then 0 else 2
  let g : ℕ → ℕ := fun n => if n ≤ 1 then 0 else 1
  refine ⟨f, g, ?_, ?_, ?_, ?_⟩
  · intro a b hab
    simp only [f]
    by_cases ha : a = 0 <;> by_cases hb : b = 0 <;> simp [ha, hb] at *
  · intro a b hab
    simp only [g]
    by_cases ha : a ≤ 1
    · simp [ha]
    · have hb : ¬ b ≤ 1 := by
        intro hb
        exact ha (Nat.le_trans hab hb)
      simp [ha, hb]
  · intro n
    cases n with
    | zero => rfl
    | succ n =>
        simp only [f]
        rw [if_neg (Nat.succ_ne_zero n)]
        rw [haltLeft_run_succ, haltRight_run_two_add]
  · intro n
    cases n with
    | zero => rfl
    | succ n =>
        cases n with
        | zero => rfl
        | succ n =>
            simp only [g]
            rw [if_neg]
            · rw [haltLeft_run_succ, haltRight_run_two_add]
            · omega

example : Program.ordered_trace_equiv haltLeft haltRight := by
  apply Program.ordered_trace_equiv_halt_shift
  · exact fun n => by
      rw [haltLeft_run_succ n]
      rfl
  · exact fun n => by
      rw [haltRight_run_two_add n]
      rfl
  · rfl
  · rfl

end LeanFunge.Tests
