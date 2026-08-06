/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanFunge.Core.Semantics
import LeanFunge.Theory.Completeness.PairEncoding
import LeanFunge.Theory.Completeness.Routing
import LeanFunge.Theory.Completeness.TwoCounter
import Mathlib.Tactic.IntervalCases

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
* `loop_routing_back`: The backward-jump corridor, proved symbolically with
  the routing lemmas.
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

/-- The backward-jump corridor, proved symbolically: from block 2's entry,
    moving right, the corridor carries the pointer through the `^`-up, `<`-left,
    and `v`-down turns back to block 0's entry without touching the stack. -/
theorem loop_routing_back (s : State 12 10)
    (hpc : s.pc = (0, 9)) (hsm : s.stringMode = false)
    (hgrid : s.grid = loopGrid) :
    run 18 s = some { s with pc := (0, 3), dir := .down } := by
  have hA : run 1 s = some { s with pc := (1, 9), dir := .right } := by
    rw [show run 1 s = step s by rfl]
    rw [step_dir_right s hsm (by rw [hgrid, hpc]; decide)]
    rw [hpc]
    rw [show stepPos 12 10 Direction.right (0, 9) = (1, 9) by decide]
  have hB : run 5 { s with pc := (1, 9), dir := .right } =
      some { s with pc := (5, 8), dir := .up } := by
    rw [run_spaces_turn 1 9 4 { s with pc := (1, 9), dir := .right } Direction.right Direction.up
        (by norm_num) (by change s.stringMode = false; exact hsm) (by rfl)
        (by change SpacesRun s.grid Direction.right 1 9 4; rw [hgrid];
            intro k hk; interval_cases k <;> decide)
        (by
          change s.grid.get (runPos 12 10 4 Direction.right (1 % 12, 9 % 10)).1
              (runPos 12 10 4 Direction.right (1 % 12, 9 % 10)).2 = Direction.char Direction.up
          rw [hgrid]
          decide)]
    rw [show stepPos 12 10 Direction.up (runPos 12 10 4 Direction.right (1 % 12, 9 % 10)) = (5, 8) by decide]
  have hC : run 7 { s with pc := (5, 8), dir := .up } =
      some { s with pc := (4, 2), dir := .left } := by
    rw [run_spaces_turn 5 8 6 { s with pc := (5, 8), dir := .up } Direction.up Direction.left
        (by norm_num) (by change s.stringMode = false; exact hsm) (by rfl)
        (by change SpacesRun s.grid Direction.up 5 8 6; rw [hgrid];
            intro k hk; interval_cases k <;> decide)
        (by
          change s.grid.get (runPos 12 10 6 Direction.up (5 % 12, 8 % 10)).1
              (runPos 12 10 6 Direction.up (5 % 12, 8 % 10)).2 = Direction.char Direction.left
          rw [hgrid]
          decide)]
    rw [show stepPos 12 10 Direction.left (runPos 12 10 6 Direction.up (5 % 12, 8 % 10)) = (4, 2) by decide]
  have hD : run 5 { s with pc := (4, 2), dir := .left } =
      some { s with pc := (0, 3), dir := .down } := by
    rw [run_spaces_turn 4 2 4 { s with pc := (4, 2), dir := .left } Direction.left Direction.down
        (by norm_num) (by change s.stringMode = false; exact hsm) (by rfl)
        (by change SpacesRun s.grid Direction.left 4 2 4; rw [hgrid];
            intro k hk; interval_cases k <;> decide)
        (by
          change s.grid.get (runPos 12 10 4 Direction.left (4 % 12, 2 % 10)).1
              (runPos 12 10 4 Direction.left (4 % 12, 2 % 10)).2 = Direction.char Direction.down
          rw [hgrid]
          decide)]
    rw [show stepPos 12 10 Direction.down (runPos 12 10 4 Direction.left (4 % 12, 2 % 10)) = (0, 3) by decide]
  have hAB : run (1 + 5) s = some { s with pc := (5, 8), dir := .up } := by
    exact run_append s { s with pc := (1, 9), dir := .right }
      (some { s with pc := (5, 8), dir := .up }) 1 5 hA hB
  have hABC : run ((1 + 5) + 7) s = some { s with pc := (4, 2), dir := .left } := by
    exact run_append s { s with pc := (5, 8), dir := .up }
      (some { s with pc := (4, 2), dir := .left }) (1 + 5) 7 hAB hC
  have hABCD : run (((1 + 5) + 7) + 5) s = some { s with pc := (0, 3), dir := .down } := by
    exact run_append s { s with pc := (4, 2), dir := .left }
      (some { s with pc := (0, 3), dir := .down }) ((1 + 5) + 7) 5 hABC hD
  rw [show 18 = ((1 + 5) + 7) + 5 by omega]
  exact hABCD

/-- The final interpreter stack is exactly the encoding of the final
    two-counter machine counters. -/
theorem loop_simulation :
    (run 127 (loopStart 3 0)).map (fun s => s.stack)
      = (CMInstr.run loopProgram 10 (CMInstr.startCM 3 0)).map
          (fun s => [Int.ofNat (encode s.c1 s.c2)]) := by
  decide

end Completeness

end LeanFunge
