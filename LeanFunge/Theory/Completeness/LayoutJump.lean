/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanFunge.Core.Semantics
import LeanFunge.Theory.Completeness.Layout
import LeanFunge.Theory.Completeness.PairEncoding
import LeanFunge.Theory.Completeness.TwoCounter

/-!
# The Jump Corridor on the Generated Playfield

The generated playfield plus a jump corridor: for the `decz` block's jump
target, a corridor row above the block carries the branch-up flow to the
target's entry column and drops it down. With the corridor added, the
generated playfield of the transfer program fully simulates the two-counter
machine on both branches: counter 1 zero jumps to the halt, counter 1
positive falls through the decrement.

The corridor is placed on the gap row just above the `decz` block (row 1):
a `>` at the branch column `(7, 1)` turns the up-flow right toward the
target's entry column, and a `v` at `(11, 1)` drops it down column 11 to the
halt block.

## Main definitions

* `corridorGrid`: The generated playfield with the jump corridor.
* `jumpStart`: The initial interpreter state for counters `(c1, c2)`.

## Theorems

* `transfer_jump_halts`: The generated playfield halts on the zero branch.
* `transfer_jump_stack`: The zero branch leaves the encoding of `(0, 1)`.
* `transfer_fall_halts`: The generated playfield halts on the fall-through
  branch.
* `transfer_fall_stack`: The fall-through branch leaves the encoding of
  `(1, 1)`.
* `transfer_simulation_jump`: The zero-branch interpreter stack is the
  encoding of the final two-counter machine counters.
-/

namespace LeanFunge

namespace Completeness

/-- The generated playfield of the transfer program plus the jump corridor:
    the `>` at `(7, 1)` turns the branch-up flow right, and the `v` at
    `(11, 1)` drops it down the halt block's entry column. -/
def corridorGrid : Grid (playfieldWidth layoutProgram) (playfieldHeight layoutProgram) :=
  Grid.put (Grid.put (playfieldOf layoutProgram) 7 1 '>') 11 1 'v'

/-- The initial interpreter state for counters `(c1, c2)`: the encoded pair on
    the stack and the pointer at the first block's entry. -/
def jumpStart (c1 c2 : ℕ) : State (playfieldWidth layoutProgram) (playfieldHeight layoutProgram) :=
  { State.init corridorGrid with
    stack := [Int.ofNat (encode c1 c2)],
    pc := (0, 0) }

/-- The generated playfield halts on the zero branch: the `decz` jumps to the
    halt through the corridor. -/
theorem transfer_jump_halts : run 24 (jumpStart 0 0) = none := by
  decide

/-- The zero branch leaves the encoding of `(0, 1)` on the stack. -/
theorem transfer_jump_stack :
    (run 23 (jumpStart 0 0)).map (fun s => s.stack) = some [Int.ofNat (encode 0 1)] := by
  decide

/-- The generated playfield halts on the fall-through branch. -/
theorem transfer_fall_halts : run 22 (jumpStart 1 0) = none := by
  decide

/-- The fall-through branch leaves the encoding of `(1, 1)` on the stack. -/
theorem transfer_fall_stack :
    (run 21 (jumpStart 1 0)).map (fun s => s.stack) = some [Int.ofNat (encode 1 1)] := by
  decide

/-- The zero-branch interpreter stack is the encoding of the final
    two-counter machine counters. -/
theorem transfer_simulation_jump :
    (run 23 (jumpStart 0 0)).map (fun s => s.stack)
      = (CMInstr.run layoutProgram 2 (CMInstr.startCM 0 0)).map
          (fun s => [Int.ofNat (encode s.c1 s.c2)]) := by
  decide

end Completeness

end LeanFunge
