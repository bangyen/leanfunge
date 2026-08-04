/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanFunge.Core.Semantics

/-!
# Factorial

A looping program that computes `3! = 6` and halts. The counter lives in the
cell `(0, 0)` and the accumulator on the stack. Each iteration multiplies the
accumulator by the counter with `*`, decrements the counter, stores it back
with `p`, and loops; the `|` instruction exits upward when the counter reaches
zero, leaving `6` on the stack.

## Main definitions

* `factorialRow`, `factorialGrid`, `factorialState`: The program, its
  playfield, and its initial state.

## Theorems

* `factorial_stack`: After 133 steps the stack is `[6]`.
* `factorial_halts`: The program halts after 134 steps.
-/

namespace LeanFunge.Examples

/-- The four rows of the factorial program. -/
def factorialRows : List (List Char) :=
  [String.toList "300p1>>>00g!|             ",
   String.toList "            >00g*00g1-00pv",
   String.toList "       ^                 <",
   String.toList "            @             "]

/-- The playfield of the factorial program. -/
def factorialGrid : Grid 26 4 := Grid.ofRows 26 4 factorialRows

/-- The initial state of the factorial program. -/
def factorialState : State 26 4 := State.init factorialGrid

/-- After 133 steps the stack is `[6]`. -/
theorem factorial_stack :
    (run 133 factorialState).map (fun s => s.stack) = some [6] := by
  decide

/-- The program halts after 134 steps. -/
theorem factorial_halts : run 134 factorialState = none := by
  decide

end LeanFunge.Examples
