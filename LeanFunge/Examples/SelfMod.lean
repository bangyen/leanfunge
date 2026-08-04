/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanFunge.Core.Semantics

/-!
# Self-Modification

Programs that modify their own playfield with `p` and then execute the
written instruction.

## Main definitions

* `selfmodRow`, `selfmodGrid`, `selfmodState`: A program that writes its own
  halting `@` instruction.
* `execRow`, `execGrid`, `execState`: A program that writes a `1` instruction
  and then executes it.

## Theorems

* `selfmod_writes`: After 8 steps the cell `(8, 0)` holds `@`.
* `selfmod_halts`: The program halts after 9 steps.
* `exec_writes`: After 7 steps the cell `(7, 0)` holds `1`.
* `exec_stack`: After 9 steps the stack is `[1]`.
* `exec_halts`: The program halts after 10 steps.
-/

namespace LeanFunge.Examples

/-- The 10-cell row `>88*80p  `: computes `64` (`8*8`), stores `@` at
    `(8, 0)` with `p`, and then runs into it. -/
def selfmodRow : List Char := String.toList ">88*80p  "

/-- The playfield of the self-writing program. -/
def selfmodGrid : Grid 10 1 := Grid.ofRows 10 1 [selfmodRow]

/-- The initial state of the self-writing program. -/
def selfmodState : State 10 1 := State.init selfmodGrid

/-- The 10-cell row `>77*70p  @`: computes `49` (`7*7`), stores `1` at
    `(7, 0)` with `p`, and then executes the written `1`. -/
def execRow : List Char := String.toList ">77*70p  @"

/-- The playfield of the write-and-execute program. -/
def execGrid : Grid 10 1 := Grid.ofRows 10 1 [execRow]

/-- The initial state of the write-and-execute program. -/
def execState : State 10 1 := State.init execGrid

/-- After 8 steps the cell `(8, 0)` holds `@`. -/
theorem selfmod_writes :
    (run 8 selfmodState).map (fun s => s.grid.get 8 0) = some '@' := by
  decide

/-- The program halts after 9 steps. -/
theorem selfmod_halts : run 9 selfmodState = none := by
  decide

/-- After 7 steps the cell `(7, 0)` holds `1`. -/
theorem exec_writes :
    (run 7 execState).map (fun s => s.grid.get 7 0) = some '1' := by
  decide

/-- After 9 steps the stack is `[1]`; the written instruction was executed. -/
theorem exec_stack :
    (run 9 execState).map (fun s => s.stack) = some [1] := by
  decide

/-- The program halts after 10 steps. -/
theorem exec_halts : run 10 execState = none := by
  decide

end LeanFunge.Examples
