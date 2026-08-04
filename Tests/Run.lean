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

end LeanFunge.Tests
