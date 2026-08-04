/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanFunge.Core.Semantics

/-!
# Hello World

A single-row Befunge program that prints `Hello World!` using string mode and
twelve `,` instructions, then halts.

## Main definitions

* `helloRow`, `helloGrid`, `helloState`: The program, its playfield, and its
  initial state.

## Theorems

* `hello_world_output`: After 26 steps the output is `Hello World!`.
* `hello_world_halts`: The program halts after 27 steps.
-/

namespace LeanFunge.Examples

/-- The 27-cell row `"!dlroW olleH",,,,,,,,,,,,@`. -/
def helloRow : List Char := String.toList "\"!dlroW olleH\",,,,,,,,,,,,@"

/-- The playfield of the Hello World program. -/
def helloGrid : Grid 27 1 := Grid.ofRows 27 1 [helloRow]

/-- The initial state of the Hello World program. -/
def helloState : State 27 1 := State.init helloGrid

/-- After 26 steps the output is `Hello World!`. -/
theorem hello_world_output :
    (run 26 helloState).map (fun s => s.output) = some "Hello World!" := by
  decide

/-- The program halts after 27 steps. -/
theorem hello_world_halts : run 27 helloState = none := by
  decide

end LeanFunge.Examples
