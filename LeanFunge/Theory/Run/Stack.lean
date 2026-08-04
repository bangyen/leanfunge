/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanFunge.Core.Semantics
import Mathlib.Data.Nat.Notation

/-!
# Run-Level Stack Invariance

## Main definitions

* `stepPreservesStack`: A state whose next step cannot change the stack.

## Theorems

* `step_stack_of_stepPreservesStack`: A no-op step leaves the stack unchanged.
* `run_stack_invariant`: If every state reached during a run is a no-op, the
  stack is unchanged across the whole run.
-/

namespace LeanFunge

/-- A state whose next step cannot change the stack: a `nop` outside string
    mode. -/
def stepPreservesStack (s : State w h) : Prop :=
  s.stringMode = false ∧ decodeChar (s.grid.get s.pc.1 s.pc.2) = .nop

/-- A no-op step leaves the stack unchanged. -/
theorem step_stack_of_stepPreservesStack {s s' : State w h} (hstep : step s = some s')
    (hn : stepPreservesStack s) : s'.stack = s.stack := by
  rcases hn with ⟨hm, hnop⟩
  unfold step at hstep
  dsimp only at hstep
  rw [hm, hnop] at hstep
  change some (stepState s .nop) = some s' at hstep
  injection hstep with hs'
  rw [← hs']
  unfold stepState
  rfl

/-- If every state reached during a run is a no-op, the stack is unchanged
    across the whole run. -/
theorem run_stack_invariant (s : State w h) (n : ℕ) (s' : State w h)
    (h : run n s = some s')
    (hn : ∀ k, k ≤ n → ∀ sₖ, run k s = some sₖ → stepPreservesStack sₖ) :
    s'.stack = s.stack := by
  induction n generalizing s' with
  | zero =>
      rw [run] at h
      injection h with hs'
      rw [hs']
  | succ n ih =>
      rcases hrun : run n s with _ | sₙ
      · rw [run, hrun] at h
        cases h
      · rw [run, hrun] at h
        have hstep : step sₙ = some s' := by simpa only using h
        have hsₙ : sₙ.stack = s.stack := by
          apply ih sₙ hrun
          intro k hk sₖ hsₖ
          exact hn k (Nat.le_trans hk (Nat.le_succ n)) sₖ hsₖ
        exact (step_stack_of_stepPreservesStack hstep (hn n (Nat.le_succ n) sₙ hrun)).trans hsₙ

end LeanFunge
