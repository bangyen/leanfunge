/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanFunge.Core.Semantics
import LeanFunge.Theory.Completeness.PairEncoding
import LeanFunge.Theory.Completeness.TwoCounter

/-!
# A Looping Simulated Two-Counter Machine on Counter 2

The counter-2 analogue of the loop example: this program tests and decrements
counter 2 rather than counter 1, exercising the `% 3`/`/ 3` branch of the
`decz` block snippet. The interpreter verifies, by kernel computation, that
the machine is simulated with the counters encoded as `2^c1 * 3^c2`.

The program moves counter 2 into counter 1 by looping:

```
0: decz c2 3     -- if c2 = 0 jump to 3 (halt), else c2-- and continue
1: inc c1        -- c1++
2: jump 0        -- unconditional backward jump to 0
3: halt
```

Starting from `(c1, c2) = (0, 3)`, the loop runs three times and halts with
`(3, 0)`. The playfield is the loop playfield with the block-0 test changed
to `: 3 % |` and the decrement to `3 /`, so the `|` branches down exactly when
the value is divisible by 3 (counter 2 positive).

## Main definitions

* `loop2Rows`, `loop2Grid`: The playfield and its rows.
* `loop2Program`: The looping two-counter machine above.
* `loop2Start`: The initial interpreter state for counters `(c1, c2)`.

## Theorems

* `loop2_program_end`: The two-counter machine reaches `(pc, c1, c2) = (3, 3, 0)`.
* `loop2_program_halts`: The two-counter machine halts.
* `loop2_stack`: The interpreter leaves the encoding of `(3, 0)` on the stack.
* `loop2_halts`: The interpreter halts.
* `loop2_back_jump`: After the first iteration the pointer is back at the
  entry of instruction 0 with the encoding of `(1, 2)`.
* `loop2_simulation`: The final interpreter stack is exactly the encoding of
  the final two-counter machine counters.
-/

namespace LeanFunge

namespace Completeness

/-- The rows of the counter-2 loop playfield. -/
def loop2Rows : List (List Char) :=
  [ String.toList "v  <<       ",
    String.toList ">@          ",
    String.toList "v    <      ",
    String.toList ">:3%|       ",
    String.toList "    3       ",
    String.toList "    /       ",
    String.toList "v   <       ",
    String.toList ">2*v        ",
    String.toList "v  <        ",
    String.toList ">    ^      " ]

/-- The counter-2 loop playfield. -/
def loop2Grid : Grid 12 10 := Grid.ofRows 12 10 loop2Rows

/-- The counter-2 looping two-counter machine. -/
def loop2Program : CMProgram :=
  [.decz 1 3, .inc 0, .jump 0, .halt]

/-- The initial interpreter state for counters `(c1, c2)`: the encoded pair on
    the stack and the pointer at the entry of instruction 0. -/
def loop2Start (c1 c2 : ℕ) : State 12 10 :=
  { State.init loop2Grid with
    stack := [Int.ofNat (encode c1 c2)],
    pc := (0, 3) }

/-- The two-counter machine reaches `(pc, c1, c2) = (3, 3, 0)`. -/
theorem loop2_program_end :
    CMInstr.run loop2Program 10 (CMInstr.startCM 0 3) = some { pc := 3, c1 := 3, c2 := 0 } := by
  decide

/-- The two-counter machine halts. -/
theorem loop2_program_halts : CMInstr.run loop2Program 11 (CMInstr.startCM 0 3) = none := by
  decide

/-- The interpreter leaves the encoding of `(3, 0)` on the stack. -/
theorem loop2_stack :
    (run 127 (loop2Start 0 3)).map (fun s => s.stack) = some [Int.ofNat (encode 3 0)] := by
  decide

/-- The interpreter halts. -/
theorem loop2_halts : run 128 (loop2Start 0 3) = none := by
  decide

/-- After the first iteration the pointer is back at the entry of instruction
    0 with the encoding of `(1, 2)` on the stack: the backward jump has been
    taken. -/
theorem loop2_back_jump :
    (run 38 (loop2Start 0 3)).map (fun s => (s.stack, s.pc)) = some ([Int.ofNat (encode 1 2)], (0, 3)) := by
  decide

/-- The final interpreter stack is exactly the encoding of the final
    two-counter machine counters. -/
theorem loop2_simulation :
    (run 127 (loop2Start 0 3)).map (fun s => s.stack)
      = (CMInstr.run loop2Program 10 (CMInstr.startCM 0 3)).map
          (fun s => [Int.ofNat (encode s.c1 s.c2)]) := by
  decide

end Completeness

end LeanFunge
