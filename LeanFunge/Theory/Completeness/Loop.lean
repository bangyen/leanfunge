/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanFunge.Core.Semantics
import LeanFunge.Theory.Completeness.PairEncoding
import LeanFunge.Theory.Completeness.TwoCounter

/-!
# A Looping Simulated Two-Counter Machine

This module runs a two-counter machine with a genuine backward jump inside a
LeanFunge playfield and verifies, by kernel computation, that the interpreter
simulates it with the counters encoded as the single stack value
`2^c1 * 3^c2`.

The program moves counter 1 into counter 2 by looping:

```
0: decz c1 3     -- if c1 = 0 jump to 3 (halt), else c1-- and continue
1: inc c2        -- c2++
2: jump 0        -- unconditional backward jump to 0
3: halt
```

Starting from `(c1, c2) = (3, 0)`, the loop runs three times and halts with
`(0, 3)`. The playfield routes the backward jump `2 -> 0` up column 5 to the
routing row, left to column 0, and down into instruction 0's block — the
corridor pattern for loops.

## Main definitions

* `loopRows`, `loopGrid`: The playfield and its rows.
* `loopProgram`: The looping two-counter machine above.
* `loopStart`: The initial interpreter state for counters `(c1, c2)`.

## Theorems

* `loop_program_end`: The two-counter machine reaches `(pc, c1, c2) = (3, 0, 3)`.
* `loop_program_halts`: The two-counter machine halts.
* `loop_stack`: The interpreter leaves the encoding of `(0, 3)` on the stack.
* `loop_halts`: The interpreter halts.
* `loop_back_jump`: After the first iteration the pointer is back at the
  entry of instruction 0 with the encoding of `(2, 1)`.
* `loop_simulation`: The final interpreter stack is exactly the encoding of
  the final two-counter machine counters.
-/

namespace LeanFunge

namespace Completeness

/-- The rows of the loop playfield. -/
def loopRows : List (List Char) :=
  [ String.toList "v  <<       ",
    String.toList ">@          ",
    String.toList "v    <      ",
    String.toList ">:2%|       ",
    String.toList "    2       ",
    String.toList "    /       ",
    String.toList "v   <       ",
    String.toList ">3*v        ",
    String.toList "v  <        ",
    String.toList ">    ^      " ]

/-- The loop playfield. -/
def loopGrid : Grid 12 10 := Grid.ofRows 12 10 loopRows

/-- The looping two-counter machine. -/
def loopProgram : CMProgram :=
  [.decz 0 3, .inc 1, .jump 0, .halt]

/-- The initial interpreter state for counters `(c1, c2)`: the encoded pair on
    the stack and the pointer at the entry of instruction 0. -/
def loopStart (c1 c2 : ℕ) : State 12 10 :=
  { State.init loopGrid with
    stack := [Int.ofNat (encode c1 c2)],
    pc := (0, 3) }

/-- The two-counter machine reaches `(pc, c1, c2) = (3, 0, 3)`. -/
theorem loop_program_end :
    CMInstr.run loopProgram 10 (CMInstr.startCM 3 0) = some { pc := 3, c1 := 0, c2 := 3 } := by
  decide

/-- The two-counter machine halts. -/
theorem loop_program_halts : CMInstr.run loopProgram 11 (CMInstr.startCM 3 0) = none := by
  decide

/-- The interpreter leaves the encoding of `(0, 3)` on the stack. -/
theorem loop_stack :
    (run 127 (loopStart 3 0)).map (fun s => s.stack) = some [Int.ofNat (encode 0 3)] := by
  decide

/-- The interpreter halts. -/
theorem loop_halts : run 128 (loopStart 3 0) = none := by
  decide

/-- After the first iteration the pointer is back at the entry of instruction
    0 with the encoding of `(2, 1)` on the stack: the backward jump has been
    taken. -/
theorem loop_back_jump :
    (run 38 (loopStart 3 0)).map (fun s => (s.stack, s.pc)) = some ([Int.ofNat (encode 2 1)], (0, 3)) := by
  decide

/-- The final interpreter stack is exactly the encoding of the final
    two-counter machine counters. -/
theorem loop_simulation :
    (run 127 (loopStart 3 0)).map (fun s => s.stack)
      = (CMInstr.run loopProgram 10 (CMInstr.startCM 3 0)).map
          (fun s => [Int.ofNat (encode s.c1 s.c2)]) := by
  decide

end Completeness

end LeanFunge
