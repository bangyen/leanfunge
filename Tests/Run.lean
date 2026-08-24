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
    (hstr : s.stringMode = false)
    (hins : decodeChar (s.grid.get s.pc.1 s.pc.2) = .put) :
    s'.grid = Grid.put s.grid (putX s) (putY s) (putChar s) :=
  step_grid_put hstep hstr hins

example {w h : ℕ} (s : State w h) (s' : State w h) (x y : ℕ)
    (hstep : step s = some s') (hp : stepPreservesCell x y s) :
    s'.grid.get x y = s.grid.get x y :=
  step_cell_of_stepPreservesCell x y hstep hp

example (x y : ℕ) (s : State w h) (n : ℕ) (s' : State w h)
    (h : run n s = some s')
    (hno : ∀ k, k ≤ n → ∀ sₖ, run k s = some sₖ → stepPreservesCell x y sₖ) :
    s'.grid.get x y = s.grid.get x y :=
  run_cell_invariant x y s n s' h hno

example {w h : ℕ} (s : State w h) (s' : State w h) (hstep : step s = some s') :
    s'.grid = applyWrite s.grid (stepWrite s) :=
  step_grid_applyWrite hstep

example (s : State w h) (n : ℕ) (s' : State w h) (h : run n s = some s') :
    s'.grid
      = (runWrites n s).foldl (fun g wt => Grid.put g wt.1 wt.2.1 wt.2.2) s.grid :=
  run_grid_writes s n s' h

example {w h : ℕ} (s : State w h) (hw : 0 < w) (hh : 0 < h)
    (hg : gridNoPut s.grid) : stepPreservesGrid s :=
  stepPreservesGrid_of_gridNoPut hw hh hg

example {w h : ℕ} (s : State w h) (hw : 0 < w) (hh : 0 < h)
    (hg : gridNoPut s.grid) (n : ℕ) (s' : State w h) (h : run n s = some s') :
    s'.grid = s.grid :=
  run_grid_invariant_of_noPut hw hh hg n s' h

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

example (s : State w h) (hsm : s.stringMode = true)
    (hcell : s.grid.get s.pc.1 s.pc.2 ≠ '"') :
    step s = some { s with
      stack := Stack.push s.stack (Int.ofNat (s.grid.get s.pc.1 s.pc.2).toNat),
      pc := stepPos w h s.dir s.pc } :=
  step_string_general s hsm hcell

example (x y n : ℕ) (s : State w h) (hpc : s.pc = (x % w, y % h))
    (hsm : s.stringMode = true) (hstr : StringRun s.grid s.dir x y n) :
    run n s = some { s with
      stack := List.reverse (stringCodes s.grid s.dir x y n) ++ s.stack,
      pc := runPos w h n s.dir (x % w, y % h) } :=
  run_string x y n s hpc hsm hstr

example (s : State w h) (hm : s.stringMode = false)
    (hcell : s.grid.get s.pc.1 s.pc.2 = ',') :
    step s = some { s with
      output := s.output.push (Char.ofNat (Int.toNat (Stack.top s.stack))),
      stack := Stack.drop s.stack,
      pc := stepPos w h s.dir s.pc } :=
  step_printChar_general s hm hcell

end LeanFunge.Tests
