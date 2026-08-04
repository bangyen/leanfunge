/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanFunge.Core.Semantics

/-!
# Put and Get

The program `521p21g.@` stores the value `5` into the playfield with `p` and
retrieves it with `g`, demonstrating Befunge's self-modifying playfield.

## Main definitions

* `putRows`, `putGrid`, `putState`: The program, its playfield, and its
  initial state.

## Theorems

* `put_get_roundtrip`: After 8 steps the output is `5`.
* `put_get_halts`: The program halts after 9 steps.
-/

namespace LeanFunge.Examples

/-- The two rows of the put/get program: `521p21g.@` over a blank row. -/
def putRows : List (List Char) :=
  [String.toList "521p21g.@", String.toList "        "]

/-- The playfield of the put/get program. -/
def putGrid : Grid 9 2 := Grid.ofRows 9 2 putRows

/-- The initial state of the put/get program. -/
def putState : State 9 2 := State.init putGrid

/-- After 8 steps the output is `5`. -/
theorem put_get_roundtrip :
    (run 8 putState).map (fun s => s.output) = some "5" := by
  decide

/-- The program halts after 9 steps. -/
theorem put_get_halts : run 9 putState = none := by
  decide

end LeanFunge.Examples
