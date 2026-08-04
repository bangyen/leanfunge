/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanFunge.Core.Semantics

/-!
# Integer Input

Programs that read a decimal integer with `&` from the input stream.

## Main definitions

* `inputRow`, `inputGrid`, `inputState`: A program that reads `5` and adds `2`.
* `multiRow`, `multiGrid`, `multiState`: A program that reads a multi-digit
  integer.
* `negRow`, `negGrid`, `negState`: A program that reads a negative integer.

## Theorems

* `input_output`: After 4 steps the output is `7`.
* `input_halts`: The program halts after 5 steps.
* `multi_output`: After 2 steps the output is `12`.
* `multi_halts`: The program halts after 3 steps.
* `neg_stack`: After 1 step the stack top is `-3`.
* `neg_halts`: The program halts after 2 steps.
-/

namespace LeanFunge.Examples

/-- The 5-cell row `&2+.@`. -/
def inputRow : List Char := String.toList "&2+.@"

/-- The playfield of the input program. -/
def inputGrid : Grid 5 1 := Grid.ofRows 5 1 [inputRow]

/-- The initial state, with input `5`. -/
def inputState : State 5 1 := { (State.init inputGrid) with input := String.toList "5" }

/-- The 3-cell row `&.@`. -/
def multiRow : List Char := String.toList "&.@"

/-- The playfield of the multi-digit program. -/
def multiGrid : Grid 3 1 := Grid.ofRows 3 1 [multiRow]

/-- The initial state, with input `12`. -/
def multiState : State 3 1 := { (State.init multiGrid) with input := String.toList "12" }

/-- The 2-cell row `&@`. -/
def negRow : List Char := String.toList "&@"

/-- The playfield of the negative program. -/
def negGrid : Grid 2 1 := Grid.ofRows 2 1 [negRow]

/-- The initial state, with input `-3`. -/
def negState : State 2 1 := { (State.init negGrid) with input := String.toList "-3" }

/-- After 4 steps the output is `7`. -/
theorem input_output :
    (run 4 inputState).map (fun s => s.output) = some "7" := by
  decide

/-- The program halts after 5 steps. -/
theorem input_halts : run 5 inputState = none := by
  decide

/-- After 2 steps the output is `12`. -/
theorem multi_output :
    (run 2 multiState).map (fun s => s.output) = some "12" := by
  decide

/-- The program halts after 3 steps. -/
theorem multi_halts : run 3 multiState = none := by
  decide

/-- After 1 step the stack top is `-3`. -/
theorem neg_stack :
    (run 1 negState).map (fun s => Stack.top s.stack) = some (-3) := by
  decide

/-- The program halts after 2 steps. -/
theorem neg_halts : run 2 negState = none := by
  decide

end LeanFunge.Examples
