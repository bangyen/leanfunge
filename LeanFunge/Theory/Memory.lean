/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanFunge.Examples.Quine
import LeanFunge.Examples.SelfMod
import LeanFunge.Theory.Grid
import LeanFunge.Theory.Run.Grid

/-!
# The Memory Model of the Example Programs

The run-level memory model applied to the verified examples. The example
modules pin their playfields down by kernel computation at a fixed number of
steps; the theorems here lift those computations to statements about the whole
playfield, and — for the quine — about every number of steps.

## Main definitions

* `selfmodWrite`, `execWrite`: The single cell each self-modifying example
  writes.

## Theorems

* `quine_gridNoPut`: The quine's playfield contains no put instruction.
* `quine_grid_invariant`: The quine never modifies itself, at any number of
  steps — it reads its own source with get but never writes.
* `selfmod_runWrites`: The self-writing program performs exactly one write.
* `selfmod_grid`: After 8 steps the playfield is the initial playfield with
  that one cell written.
* `selfmod_grid_other`: Every other cell of the self-writing program is
  unchanged.
* `exec_runWrites`: The write-and-execute program performs exactly one write.
* `exec_grid`: After 7 steps the playfield is the initial playfield with that
  one cell written.
* `exec_grid_other`: Every other cell of the write-and-execute program is
  unchanged.
-/

namespace LeanFunge.Examples

open LeanFunge

/-- The quine's playfield contains no put instruction. -/
theorem quine_gridNoPut : gridNoPut quineGrid := by decide

/-- The quine never modifies itself, at any number of steps: it reads its own
    source with `g` but never writes. Unlike the example module's
    kernel-computed facts, this holds for every `n`. -/
theorem quine_grid_invariant (n : ℕ) (s' : State 45 1)
    (h : run n quineState = some s') : s'.grid = quineGrid :=
  run_grid_invariant_of_noPut (by decide) (by decide) quine_gridNoPut n s' h

/-- The single cell the self-writing program writes: `@` at `(8, 0)`. -/
def selfmodWrite : ℕ × ℕ × Char := (8, 0, '@')

/-- The self-writing program performs exactly one write in its 8 steps. -/
theorem selfmod_runWrites : runWrites 8 selfmodState = [selfmodWrite] := by
  decide

/-- After 8 steps the playfield is the initial playfield with `@` written at
    `(8, 0)` — the whole playfield, not just the written cell. -/
theorem selfmod_grid (s : State 10 1) (h : run 8 selfmodState = some s) :
    s.grid = Grid.put selfmodGrid 8 0 '@' := by
  have hw := run_grid_writes selfmodState 8 s h
  rw [selfmod_runWrites] at hw
  simpa only [List.foldl_cons, List.foldl_nil] using hw

/-- Every cell of the self-writing program other than `(8, 0)` is unchanged. -/
theorem selfmod_grid_other (s : State 10 1) (h : run 8 selfmodState = some s)
    (x y : ℕ) (hne : x % 10 ≠ 8 % 10 ∨ y % 1 ≠ 0 % 1) :
    s.grid.get x y = selfmodGrid.get x y := by
  rw [selfmod_grid s h]
  exact Grid.get_put_other _ _ _ _ _ _ hne

/-- The single cell the write-and-execute program writes: `1` at `(7, 0)`. -/
def execWrite : ℕ × ℕ × Char := (7, 0, '1')

/-- The write-and-execute program performs exactly one write in its 7 steps. -/
theorem exec_runWrites : runWrites 7 execState = [execWrite] := by
  decide

/-- After 7 steps the playfield is the initial playfield with `1` written at
    `(7, 0)` — the whole playfield, not just the written cell. -/
theorem exec_grid (s : State 10 1) (h : run 7 execState = some s) :
    s.grid = Grid.put execGrid 7 0 '1' := by
  have hw := run_grid_writes execState 7 s h
  rw [exec_runWrites] at hw
  simpa only [List.foldl_cons, List.foldl_nil] using hw

/-- Every cell of the write-and-execute program other than `(7, 0)` is
    unchanged. -/
theorem exec_grid_other (s : State 10 1) (h : run 7 execState = some s)
    (x y : ℕ) (hne : x % 10 ≠ 7 % 10 ∨ y % 1 ≠ 0 % 1) :
    s.grid.get x y = execGrid.get x y := by
  rw [exec_grid s h]
  exact Grid.get_put_other _ _ _ _ _ _ hne

end LeanFunge.Examples
