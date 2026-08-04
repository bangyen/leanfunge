/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanFunge.Core.Semantics

/-!
# Arithmetic

The single-row program `23+.@` computes `2 + 3 = 5`, prints it, and halts.

## Main definitions

* `arithmeticRow`, `arithmeticGrid`, `arithmeticState`: The program, its
  playfield, and its initial state.

## Theorems

* `arithmetic_stack_top`: After 3 steps the stack top is `5`.
* `arithmetic_output`: After 4 steps the output is `5`.
* `arithmetic_halts`: The program halts after 5 steps.
-/

namespace LeanFunge.Examples

/-- The 5-cell row `23+.@`. -/
def arithmeticRow : List Char := String.toList "23+.@"

/-- The playfield of the arithmetic program. -/
def arithmeticGrid : Grid 5 1 := Grid.ofRows 5 1 [arithmeticRow]

/-- The initial state of the arithmetic program. -/
def arithmeticState : State 5 1 := State.init arithmeticGrid

/-- After 3 steps the stack top is `5`. -/
theorem arithmetic_stack_top :
    (run 3 arithmeticState).map (fun s => Stack.top s.stack) = some 5 := by
  decide

/-- After 4 steps the output is `5`. -/
theorem arithmetic_output :
    (run 4 arithmeticState).map (fun s => s.output) = some "5" := by
  decide

/-- The program halts after 5 steps. -/
theorem arithmetic_halts : run 5 arithmeticState = none := by
  decide

end LeanFunge.Examples
