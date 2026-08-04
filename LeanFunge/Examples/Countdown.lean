/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanFunge.Core.Semantics

/-!
# Countdown

A looping program that prints `321` and halts. The counter lives in the cell
`(0, 0)`; each iteration fetches it, prints it with `.`, decrements it with
`1-`, stores it back with `p`, and loops. The `|` instruction exits upward
when the counter reaches zero.

## Main definitions

* `countdownRow`, `countdownGrid`, `countdownState`: The program, its
  playfield, and its initial state.

## Theorems

* `countdown_output`: After 131 steps the output is `321`.
* `countdown_halts`: The program halts after 133 steps.
-/

namespace LeanFunge.Examples

/-- The four rows of the countdown program. -/
def countdownRows : List (List Char) :=
  [String.toList "300p>>>00g!|              ",
   String.toList "           >00g.00g1-00pv ",
   String.toList "      ^                 < ",
   String.toList "           @             "]

/-- The playfield of the countdown program. -/
def countdownGrid : Grid 26 4 := Grid.ofRows 26 4 countdownRows

/-- The initial state of the countdown program. -/
def countdownState : State 26 4 := State.init countdownGrid

/-- After 131 steps the output is `321`. -/
theorem countdown_output :
    (run 131 countdownState).map (fun s => s.output) = some "321" := by
  decide

/-- The program halts after 133 steps. -/
theorem countdown_halts : run 133 countdownState = none := by
  decide

end LeanFunge.Examples
