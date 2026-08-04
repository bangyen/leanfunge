/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanFunge.Core.Semantics

/-!
# The Trampoline

The single-row program `12#3+@` exercises the `#` trampoline: the `3` cell is
skipped, so the final sum is `1 + 2 = 3` rather than `1 + 2 + 3`.

## Main definitions

* `trampRow`, `trampGrid`, `trampState`: The program, its playfield, and its
  initial state.

## Theorems

* `trampoline_skips`: After 4 steps the stack is exactly `[3]`.
* `trampoline_halts`: The program halts after 5 steps.
-/

namespace LeanFunge.Examples

/-- The 6-cell row `12#3+@`. -/
def trampRow : List Char := String.toList "12#3+@"

/-- The playfield of the trampoline program. -/
def trampGrid : Grid 6 1 := Grid.ofRows 6 1 [trampRow]

/-- The initial state of the trampoline program. -/
def trampState : State 6 1 := State.init trampGrid

/-- After 4 steps the stack is exactly `[3]`; the `3` cell was skipped. -/
theorem trampoline_skips :
    (run 4 trampState).map (fun s => s.stack) = some [3] := by
  decide

/-- The program halts after 5 steps. -/
theorem trampoline_halts : run 5 trampState = none := by
  decide

end LeanFunge.Examples
