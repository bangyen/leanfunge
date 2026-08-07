/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanFunge.Theory.Completeness.Layout
import LeanFunge.Theory.Completeness.Loop
import LeanFunge.Theory.Completeness.PairEncoding

/-!
# The Loop on the Generated Playfield

The generator emits the corridors for the looping program's jump edges: the
`decz` block's edge to the halt on header row 0 and the `jump` block's
backward edge to the `decz` block on header row 2. On the generated playfield
the loop moves `c1` into `c2`: each iteration decrements `c1`, increments
`c2`, and routes back through the backward corridor; when `c1` reaches zero
the `decz` branch jumps through the forward corridor to the halt.

## Main definitions

* `loopCorridorStart`: The initial interpreter state for counters `(c1, c2)`.

## Theorems

* `loop_corridor_back`: After the first iteration the pointer is back at the
  entry of instruction 0 with the encoding of `(2, 1)`.
* `loop_corridor_halts`: The generated playfield halts.
* `loop_corridor_stack`: The interpreter leaves the encoding of `(0, 3)` on
  the stack.
* `loop_corridor_simulation`: The final interpreter stack is exactly the
  encoding of the final two-counter machine counters.
-/

namespace LeanFunge

namespace Completeness

/-- The initial interpreter state for counters `(c1, c2)`: the encoded pair on
    the stack and the pointer at the entry of instruction 0. -/
def loopCorridorStart (c1 c2 : ℕ) : State (playfieldWidth loopProgram) (playfieldHeight loopProgram) :=
  { State.init (playfieldOf loopProgram) with
    stack := [Int.ofNat (encode c1 c2)],
    pc := (0, 4) }

/-- After the first iteration the pointer is back at the entry of instruction
    0 with the encoding of `(2, 1)`. -/
theorem loop_corridor_back :
    (run 36 (loopCorridorStart 3 0)).map (fun s => s.stack) = some [Int.ofNat (encode 2 1)] := by
  decide

/-- The generated playfield halts. -/
theorem loop_corridor_halts : run 137 (loopCorridorStart 3 0) = none := by
  decide

/-- The interpreter leaves the encoding of `(0, 3)` on the stack. -/
theorem loop_corridor_stack :
    (run 136 (loopCorridorStart 3 0)).map (fun s => s.stack) = some [Int.ofNat (encode 0 3)] := by
  decide

/-- The final interpreter stack is exactly the encoding of the final
    two-counter machine counters. -/
theorem loop_corridor_simulation :
    (run 136 (loopCorridorStart 3 0)).map (fun s => s.stack)
      = (CMInstr.run loopProgram 10 (CMInstr.startCM 3 0)).map
          (fun s => [Int.ofNat (encode s.c1 s.c2)]) := by
  decide

end Completeness

end LeanFunge
