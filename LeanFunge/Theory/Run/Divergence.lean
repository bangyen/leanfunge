/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanFunge.Core.Semantics

/-!
# Run-Level Divergence

Programs whose every step is a no-op never halt. This module proves the basic
divergence facts: on an all-space playfield the interpreter runs forever
without ever modifying the playfield or entering string mode.

## Theorems

* `run_space_step`: A run on an all-space playfield always has a successor
  state with the same grid and string mode off.
* `run_space_some`: A run on an all-space playfield never halts.
-/

namespace LeanFunge

/-- On an all-space playfield every step is a nop: each run has a successor
    state whose playfield is still all spaces and whose string mode is still
    off. -/
theorem run_space_step (w h : ℕ) (k x y : ℕ) :
    ∃ s_k : State w h,
      run k { State.init (Grid.space w h) with pc := (x, y), dir := .right } = some s_k ∧
      s_k.grid = Grid.space w h ∧ s_k.stringMode = false := by
  induction k with
  | zero =>
      refine ⟨{ State.init (Grid.space w h) with pc := (x, y), dir := .right }, rfl, ?_, ?_⟩
      · rfl
      · rfl
  | succ k ih =>
      rcases ih with ⟨s_k, hk, hgrid, hsm⟩
      have hcell : s_k.grid.get s_k.pc.1 s_k.pc.2 = ' ' := by
        rw [hgrid]
        rfl
      have hdec : decodeChar ' ' = .nop := by
        unfold decodeChar
        rfl
      have hstep : step s_k = some { s_k with pc := stepPos w h s_k.dir s_k.pc } := by
        unfold step
        simp only [hsm, hcell, hdec, stepState]
      refine ⟨{ s_k with pc := stepPos w h s_k.dir s_k.pc }, ?_, ?_, ?_⟩
      · rw [run, hk]
        change step s_k = some { s_k with pc := stepPos w h s_k.dir s_k.pc }
        rw [hstep]
      · exact hgrid
      · exact hsm

/-- A run on an all-space playfield never halts. -/
theorem run_space_some (w h : ℕ) (k x y : ℕ) :
    run k { State.init (Grid.space w h) with pc := (x, y), dir := .right } ≠ none := by
  rcases run_space_step w h k x y with ⟨s_k, hk, _, _⟩
  rw [hk]
  intro h
  cases h

end LeanFunge
