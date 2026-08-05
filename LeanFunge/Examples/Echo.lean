/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanFunge.Core.Semantics

/-!
# Echo

The single-row program `~,@` reads one character from the input stream with
`~` and prints it back with `,`, then halts.

## Main definitions

* `echoGrid`, `echoState`: The program's playfield and its initial state
  reading `x`.

## Theorems

* `echo_output`: After 2 steps the output is the echoed character `x`.
* `echo_halts`: The program halts after 3 steps.
-/

namespace LeanFunge.Examples

/-- The playfield of the echo program. -/
def echoGrid : Grid 3 1 :=
  Grid.ofRows 3 1 [String.toList "~,@"]

/-- The initial state, reading `x`. -/
def echoState : State 3 1 :=
  { (State.init echoGrid) with input := String.toList "x" }

/-- After 2 steps the output is the echoed character `x`. -/
theorem echo_output :
    (run 2 echoState).map (fun s => s.output) = some "x" := by
  decide

/-- The program halts after 3 steps. -/
theorem echo_halts : run 3 echoState = none := by
  decide

end LeanFunge.Examples
