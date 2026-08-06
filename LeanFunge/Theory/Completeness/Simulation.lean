/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanFunge.Core.Semantics
import LeanFunge.Theory.Completeness.PairEncoding
import LeanFunge.Theory.Completeness.TwoCounter

/-!
# A Concrete Simulated Two-Counter Machine

This module runs a small two-counter machine inside a LeanFunge playfield and
verifies, by kernel computation, that the interpreter simulates it
step-for-step with the counters encoded as the single stack value
`2^c1 * 3^c2`.

The program is

```
0: inc c2
1: decz c1 3     -- if c1 = 0 jump to 3 (halt), else c1-- and continue
2: inc c1
3: halt
```

and the playfield implements it with one instruction per horizontal block:

* instruction 0 (`inc c2`): `>3*v`
* instruction 1 (`decz c1`): `>:2%|` with the decrement `2/` below the `|`
* instruction 2 (`inc c1`): `>2*  ^`
* instruction 3 (`halt`): `>@`

The `|` branches downward on an even encoding (counter 1 positive, decrement
and continue) and upward on an odd encoding (counter 1 zero, jump to the halt
block). Routing happens in the left column and the `^`/`<` corridors.

## Main definitions

* `transferRows`, `transferGrid`: The playfield and its rows.
* `transferProgram`: The two-counter machine above.
* `start`: The initial Befunge state for counters `(c1, c2)`.
* `startCM`: The initial two-counter machine state for counters `(c1, c2)`.

## Theorems

* `program_end`: The two-counter machine reaches `(pc, c1, c2) = (3, 1, 1)`.
* `program_halts`: The two-counter machine halts.
* `transfer_stack`: The interpreter leaves the encoding of `(1, 1)` on the
  stack.
* `transfer_halts`: The interpreter halts.
* `decz_entry_stack`: The stack at the entry of the `decz` block encodes
  `(1, 1)`.
* `decz_continue_entry`: After the decrement path, the stack at instruction 2
  encodes `(0, 1)`.
* `transfer_stack_zero`: Starting from zero counters, the stack encodes
  `(0, 1)`.
* `transfer_halts_zero`: Starting from zero counters, the interpreter halts.
* `decz_jump_entry`: On an odd encoding the `|` jumps to the halt block with
  the stack unchanged.
* `transfer_simulation`: The final interpreter stack is exactly the encoding of
  the final two-counter machine counters.
-/

namespace LeanFunge

namespace Completeness

/-- The rows of the transfer playfield. -/
def transferRows : List (List Char) :=
  [ String.toList "v  <<      ",
    String.toList ">@          ",
    String.toList "^    <     ",
    String.toList ">3*v       ",
    String.toList "v  <       ",
    String.toList ">:2%|      ",
    String.toList "    2      ",
    String.toList "    /      ",
    String.toList "v   <      ",
    String.toList ">2*  ^     " ]

/-- The transfer playfield. -/
def transferGrid : Grid 12 10 := Grid.ofRows 12 10 transferRows

/-- The simulated two-counter machine. -/
def transferProgram : CMProgram :=
  [.inc 1, .decz 0 3, .inc 0, .halt]

/-- The initial interpreter state for counters `(c1, c2)`: the encoded pair on
    the stack and the pointer at the entry of instruction 0. -/
def start (c1 c2 : ℕ) : State 12 10 :=
  { State.init transferGrid with
    stack := [Int.ofNat (encode c1 c2)],
    pc := (0, 3) }

/-- The initial two-counter machine state for counters `(c1, c2)`. -/
def startCM (c1 c2 : ℕ) : CMState :=
  { pc := 0, c1 := c1, c2 := c2 }

/-- The two-counter machine reaches `(pc, c1, c2) = (3, 1, 1)`. -/
theorem program_end :
    CMInstr.run transferProgram 3 (startCM 1 0) = some { pc := 3, c1 := 1, c2 := 1 } := by
  decide

/-- The two-counter machine halts. -/
theorem program_halts : CMInstr.run transferProgram 4 (startCM 1 0) = none := by
  decide

/-- The interpreter leaves the encoding of `(1, 1)` on the stack. -/
theorem transfer_stack :
    (run 39 (start 1 0)).map (fun s => s.stack) = some [Int.ofNat (encode 1 1)] := by
  decide

/-- The interpreter halts. -/
theorem transfer_halts : run 40 (start 1 0) = none := by
  decide

/-- The stack at the entry of the `decz` block encodes `(1, 1)`. -/
theorem decz_entry_stack :
    (run 8 (start 1 0)).map (fun s => (s.stack, s.pc)) =
      some ([Int.ofNat (encode 1 1)], (0, 5)) := by
  decide

/-- After the decrement path, the stack at instruction 2 encodes `(0, 1)`. -/
theorem decz_continue_entry :
    (run 20 (start 1 0)).map (fun s => (s.stack, s.pc)) =
      some ([Int.ofNat (encode 0 1)], (0, 9)) := by
  decide

/-- Starting from zero counters, the stack encodes `(0, 1)`. -/
theorem transfer_stack_zero :
    (run 23 (start 0 0)).map (fun s => s.stack) = some [Int.ofNat (encode 0 1)] := by
  decide

/-- Starting from zero counters, the interpreter halts. -/
theorem transfer_halts_zero : run 24 (start 0 0) = none := by
  decide

/-- On an odd encoding the `|` jumps to the halt block with the stack
    unchanged. -/
theorem decz_jump_entry :
    (run 22 (start 0 0)).map (fun s => (s.stack, s.pc)) =
      some ([Int.ofNat (encode 0 1)], (0, 1)) := by
  decide

/-- The final interpreter stack is exactly the encoding of the final
    two-counter machine counters. -/
theorem transfer_simulation :
    (run 39 (start 1 0)).map (fun s => s.stack)
      = (CMInstr.run transferProgram 3 (startCM 1 0)).map
          (fun s => [Int.ofNat (encode s.c1 s.c2)]) := by
  decide

end Completeness

end LeanFunge
