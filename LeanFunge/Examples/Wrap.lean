/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanFunge.Core.Semantics

/-!
# Toroidal Wrap

The single-row program `88*00p` computes `64` with `88*`, writes the
character `@` into its own first cell with `00p`, and then steps off the right
edge of the playfield. The toroidal wrap brings the pointer back to column `0`,
where it executes the self-written `@` and halts — demonstrating the wrap on a
playfield whose first cell the program started at.

## Main definitions

* `wrapRow`, `wrapGrid`, `wrapState`: The program, its playfield, and its
  initial state.

## Theorems

* `wrap_writes`: After 6 steps the pointer has wrapped to `(0, 0)`, where the
  playfield now holds the self-written `@`.
* `wrap_halts`: The program halts after 7 steps.
-/

namespace LeanFunge.Examples

/-- The six-cell row `88*00p`. -/
def wrapRow : List Char :=
  String.toList "88*00p"

/-- The playfield of the wrap program. -/
def wrapGrid : Grid 6 1 :=
  Grid.ofRows 6 1 [wrapRow]

/-- The initial state of the wrap program. -/
def wrapState : State 6 1 :=
  State.init wrapGrid

/-- After 6 steps the pointer has wrapped to `(0, 0)`, where the playfield now
    holds the self-written `@`. -/
theorem wrap_writes :
    (run 6 wrapState).map (fun s => (s.pc, s.grid.get 0 0)) = some ((0, 0), '@') := by
  decide

/-- The program halts after 7 steps, when the pointer executes the written
    `@` it wrapped around to. -/
theorem wrap_halts : run 7 wrapState = none := by
  decide

end LeanFunge.Examples
