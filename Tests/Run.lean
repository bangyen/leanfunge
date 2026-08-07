/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanFunge.Theory.Run

/-!
# Run-Level Invariance Tests
-/

namespace LeanFunge.Tests

open LeanFunge

example {w h : ℕ} (s : State w h) (s' : State w h) (hstep : step s = some s')
    (hp : stepPreservesGrid s) : s'.grid = s.grid :=
  step_grid_of_stepPreservesGrid hstep hp

example (s : State w h) (n : ℕ) (s' : State w h)
    (h : run n s = some s')
    (hno : ∀ k, k ≤ n → ∀ sₖ, run k s = some sₖ → stepPreservesGrid sₖ) :
    s'.grid = s.grid :=
  run_grid_invariant s n s' h hno

example {w h : ℕ} (s : State w h) (s' : State w h) (hstep : step s = some s')
    (hn : stepPreservesStack s) : s'.stack = s.stack :=
  step_stack_of_stepPreservesStack hstep hn

example (s : State w h) (n : ℕ) (s' : State w h)
    (h : run n s = some s')
    (hn : ∀ k, k ≤ n → ∀ sₖ, run k s = some sₖ → stepPreservesStack sₖ) :
    s'.stack = s.stack :=
  run_stack_invariant s n s' h hn

example {w h : ℕ} (s : State w h) (n : ℕ) (result : Option (State w h))
    (h : run n s = result) : runRel n s result :=
  run_refines_runRel n s result h

example {w h : ℕ} (s : State w h) (result : Option (State w h)) :
    runRel 1 s result ↔ stepRel s result :=
  runRel_one s result

example {w h : ℕ} (s : State w h) {n : ℕ} (h : runRel n s none) (m : ℕ) :
    runRel (n + m) s none :=
  runRel_halts_mono s h m

example {w h : ℕ} (s s' : State w h) (result : Option (State w h))
    (n m : ℕ) (h₁ : runRel n s (some s')) (h₂ : runRel m s' result) :
    runRel (n + m) s result :=
  runRel_append s s' result n m h₁ h₂

example {w h : ℕ} (s s' : State w h) (result : Option (State w h))
    (n m : ℕ) (h₁ : run n s = some s') (h₂ : run m s' = result) :
    run (n + m) s = result :=
  run_append s s' result n m h₁ h₂

example (w h k x y : ℕ) :
    run k { State.init (Grid.space w h) with pc := (x, y), dir := .right } ≠ none :=
  run_space_some w h k x y

example (c : Char) : decodeChar c = .halt ↔ c = '@' :=
  decodeChar_halt_iff c

example (s : State w h) :
    step s = none ↔ (¬ s.stringMode ∧ decodeChar (s.grid.get s.pc.1 s.pc.2) = .halt) :=
  step_none_iff_halt s

example (s : State w h) (n : ℕ) (hnone : run n s = none) :
    ∃ m sₘ, m < n ∧ run m s = some sₘ ∧ step sₘ = none :=
  run_none_exists_halt s n hnone

example (s : State w h) : halts s ↔ ∃ m sₘ, run m s = some sₘ ∧ step sₘ = none :=
  halts_iff_reaches_halt s

example (s : State w h) :
    halts s ↔ ∃ m sₘ, run m s = some sₘ ∧ ¬ sₘ.stringMode ∧
      sₘ.grid.get sₘ.pc.1 sₘ.pc.2 = '@' :=
  halts_iff_at s

example (s s' : State w h) (hstep : step s = some s') :
    ∃ pre : List Char, s.input = pre ++ s'.input :=
  step_input_prefix s s' hstep

example (s s' : State w h) (hstep : step s = some s') :
    ∃ suf : String, s'.output = s.output ++ suf :=
  step_output_prefix s s' hstep

example (s : State w h) (n : ℕ) (s' : State w h) (h : run n s = some s') :
    ∃ pre : List Char, s.input = pre ++ s'.input :=
  run_input_prefix s n s' h

example (s : State w h) (n : ℕ) (s' : State w h) (h : run n s = some s') :
    ∃ suf : String, s'.output = s.output ++ suf :=
  run_output_prefix s n s' h

end LeanFunge.Tests
