/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanFunge.Core.Semantics
import LeanFunge.Theory.Completeness.PairEncoding
import LeanFunge.Theory.Completeness.TwoCounter
import LeanFunge.Theory.Run
import Mathlib.Data.Nat.Notation

/-!
# The Linear Simulation Fragment

The first generic simulation construction: a program with no branching — only
`inc` instructions followed by a final `halt` — is compiled to a single
playfield row `> 2* 3* ... @` where each `inc` becomes its two arithmetic
cells. Running right through the row applies each multiplication to the
encoded pair on the stack, so the interpreter simulates the two-counter
machine exactly.

This module contains the definitions (`linearRow`, `linearGrid`,
`linearStart`, `foldIncs`) and the run-level lemmas for the two-cell
increment segments. The branch-free simulation theorems live in
`LinearSimulation`.

## Main definitions

* `linearCells`: The cells of one branch-free instruction.
* `linearRowAux`: The cells of the whole program, recursively.
* `linearRow`: The playfield row of a branch-free program.
* `linearGrid`: The one-row playfield of a branch-free program.
* `linearStart`: The initial state of the branch-free simulation.
* `foldIncs`: Apply the first `j` instructions of a program as counter
  increments.

## Theorems

* `stepPos_right_no_wrap`: Moving right one cell inside the playfield does not
  wrap when the column stays in range.
* `step_push_two`: `2` pushes two.
* `step_push_three`: `3` pushes three.
* `run_mul_two`: Running right through the `2*` cells multiplies the stack top
  by two.
* `run_mul_three`: Running right through the `3*` cells multiplies the stack
  top by three.
-/

namespace LeanFunge

namespace Completeness

/-- The cells implementing a branch-free instruction: `2*` increments counter
    1, `3*` increments counter 2, and everything else contributes nothing (the
    trailing `halt` is the row's final `@`). -/
def linearCells : CMInstr → List Char
  | .inc c => if c.val = 0 then ['2', '*'] else ['3', '*']
  | _ => []

/-- The cells of the whole program, built recursively: the cells of each
    instruction in turn, then the terminating `@`. -/
def linearRowAux : CMProgram → List Char
  | [] => ['@']
  | i :: rest => linearCells i ++ linearRowAux rest

/-- The single playfield row of a branch-free program: the entry `>`, the
    arithmetic cells of each instruction, and the trailing `@`. -/
def linearRow (prog : CMProgram) : List Char :=
  '>' :: linearRowAux prog

/-- The one-row playfield of a branch-free program. -/
def linearGrid (prog : CMProgram) : Grid (linearRow prog).length 1 :=
  Grid.ofRows (linearRow prog).length 1 [linearRow prog]

/-- The initial state of the branch-free simulation: the encoded pair on the
    stack and the pointer at the entry `>`. -/
def linearStart (prog : CMProgram) (c1 c2 : ℕ) : State (linearRow prog).length 1 :=
  { State.init (linearGrid prog) with
    stack := [Int.ofNat (encode c1 c2)],
    pc := (0, 0) }

/-- Apply the first `j` instructions of a program to a state, interpreting
    each `inc` as its counter increment and ignoring everything else. -/
def foldIncs (prog : CMProgram) (j : ℕ) (s : CMState) : CMState :=
  match j with
  | 0 => s
  | j + 1 =>
      match prog.getD j .halt with
      | .inc c => CMInstr.incCounter c (foldIncs prog j s)
      | _ => foldIncs prog j s

/-- Moving right one cell inside the playfield does not wrap when the
    resulting column is still in range. -/
theorem stepPos_right_no_wrap (p w h : ℕ) (hp : p + 1 < w) :
    stepPos w h Direction.right (p, 0) = (p + 1, 0) := by
  unfold stepPos
  rw [Nat.mod_eq_of_lt hp]
  rw [Nat.zero_mod]

/-- `2` pushes two. -/
theorem step_push_two (s : State w h) (hm : s.stringMode = false)
    (hcell : s.grid.get s.pc.1 s.pc.2 = '2') :
    step s = some { s with stack := Stack.push s.stack 2, pc := stepPos w h s.dir s.pc } := by
  unfold step
  simp only [decodeChar, stepState, Stack.push, hm, hcell]

/-- `3` pushes three. -/
theorem step_push_three (s : State w h) (hm : s.stringMode = false)
    (hcell : s.grid.get s.pc.1 s.pc.2 = '3') :
    step s = some { s with stack := Stack.push s.stack 3, pc := stepPos w h s.dir s.pc } := by
  unfold step
  simp only [decodeChar, stepState, Stack.push, hm, hcell]

/-- Running right through the `2*` cells of an increment of counter 1
    multiplies the stack top by two. -/
theorem run_mul_two (s : State w h) (p : ℕ)
    (hsm : s.stringMode = false) (hdir : s.dir = Direction.right)
    (hpc : s.pc = (p, 0)) (hno : p + 2 < w)
    (hc : s.grid.get p 0 = '2') (hm : s.grid.get (p + 1) 0 = '*') :
    run 2 s = some { s with
      stack := Stack.applyBinary (· * ·) (Stack.push s.stack 2),
      pc := (p + 2, 0) } := by
  have hstep1 : step s =
      some { s with stack := Stack.push s.stack 2, pc := (p + 1, 0) } := by
    unfold step
    have hdec : decodeChar '2' = .push 2 := by
      unfold decodeChar
      rfl
    simp only [hsm, hc, hpc, hdec, stepState, Stack.push]
    rw [hdir, stepPos_right_no_wrap p w h (by omega)]
  have hrun1 : run 1 s = some { s with stack := Stack.push s.stack 2, pc := (p + 1, 0) } := by
    rw [show run 1 s = step s by rfl]
    exact hstep1
  have hstep2 : step { s with stack := Stack.push s.stack 2, pc := (p + 1, 0) } =
      some { s with
        stack := Stack.applyBinary (· * ·) (Stack.push s.stack 2),
        pc := (p + 2, 0) } := by
    unfold step
    have hdec : decodeChar '*' = .mul := by
      unfold decodeChar
      rfl
    simp only [hsm, hdec, stepState, Stack.applyBinary, Stack.push, hm]
    rw [hdir, stepPos_right_no_wrap (p + 1) w h (by omega)]
  have hrun2 : run 2 s =
      some { s with
        stack := Stack.applyBinary (· * ·) (Stack.push s.stack 2),
        pc := (p + 2, 0) } := by
    rw [show run 2 s = run (1 + 1) s by rfl]
    exact run_append s { s with stack := Stack.push s.stack 2, pc := (p + 1, 0) }
      (some { s with
        stack := Stack.applyBinary (· * ·) (Stack.push s.stack 2),
        pc := (p + 2, 0) }) 1 1 hrun1 hstep2
  exact hrun2

/-- Running right through the `3*` cells of an increment of counter 2
    multiplies the stack top by three. -/
theorem run_mul_three (s : State w h) (p : ℕ)
    (hsm : s.stringMode = false) (hdir : s.dir = Direction.right)
    (hpc : s.pc = (p, 0)) (hno : p + 2 < w)
    (hc : s.grid.get p 0 = '3') (hm : s.grid.get (p + 1) 0 = '*') :
    run 2 s = some { s with
      stack := Stack.applyBinary (· * ·) (Stack.push s.stack 3),
      pc := (p + 2, 0) } := by
  have hstep1 : step s =
      some { s with stack := Stack.push s.stack 3, pc := (p + 1, 0) } := by
    unfold step
    have hdec : decodeChar '3' = .push 3 := by
      unfold decodeChar
      rfl
    simp only [hsm, hc, hpc, hdec, stepState, Stack.push]
    rw [hdir, stepPos_right_no_wrap p w h (by omega)]
  have hrun1 : run 1 s = some { s with stack := Stack.push s.stack 3, pc := (p + 1, 0) } := by
    rw [show run 1 s = step s by rfl]
    exact hstep1
  have hstep2 : step { s with stack := Stack.push s.stack 3, pc := (p + 1, 0) } =
      some { s with
        stack := Stack.applyBinary (· * ·) (Stack.push s.stack 3),
        pc := (p + 2, 0) } := by
    unfold step
    have hdec : decodeChar '*' = .mul := by
      unfold decodeChar
      rfl
    simp only [hsm, hdec, stepState, Stack.applyBinary, Stack.push, hm]
    rw [hdir, stepPos_right_no_wrap (p + 1) w h (by omega)]
  have hrun2 : run 2 s =
      some { s with
        stack := Stack.applyBinary (· * ·) (Stack.push s.stack 3),
        pc := (p + 2, 0) } := by
    rw [show run 2 s = run (1 + 1) s by rfl]
    exact run_append s { s with stack := Stack.push s.stack 3, pc := (p + 1, 0) }
      (some { s with
        stack := Stack.applyBinary (· * ·) (Stack.push s.stack 3),
        pc := (p + 2, 0) }) 1 1 hrun1 hstep2
  exact hrun2

end Completeness

end LeanFunge
