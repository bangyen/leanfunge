/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanFunge.Core.Semantics
import LeanFunge.Theory.Run
import LeanFunge.Theory.Step
import Mathlib.Data.Nat.Notation

/-!
# Straight-Line Routing

Routing the instruction pointer through a playfield corridor is the geometric
heart of the simulation construction: after a branch, the pointer must travel
along straight rows and columns of spaces to reach the next instruction block.
A cell of spaces is a no-op, so such a run moves the pointer by `runPos`
without touching the stack, the grid, the direction, string mode, the output,
or the input stream.

This module proves the run-level lemmas for these straight-line segments:
`run_spaces` moves the pointer `n` cells through a run of spaces, and
`run_spaces_v` composes a horizontal run with a `v` turn, the corridor pattern
used to drop the pointer into a target row.

## Main definitions

* `SpacesRun`: All cells on a straight path of `n` steps are spaces.

## Theorems

* `step_space`: A step at a space outside string mode moves the pointer and
  leaves every other component unchanged.
* `run_spaces`: Running any number of steps through a run of spaces moves the
  pointer by the corresponding position iterate and preserves the rest of the
  state.
* `run_spaces_v`: A run of spaces followed by a downward-turn cell leaves the
  pointer moving down at the cell below the turn.
-/

namespace LeanFunge

/-- All cells on the straight path of `n` steps in direction `d` from the
    reduced position `(x % w, y % h)` are spaces. -/
def SpacesRun (g : Grid w h) (d : Direction) (x y n : ℕ) : Prop :=
  ∀ k : ℕ, k < n →
    g.get (runPos w h k d (x % w, y % h)).1 (runPos w h k d (x % w, y % h)).2 = ' '

/-- A step at a space outside string mode moves the pointer and leaves every
    other component unchanged. -/
theorem step_space (s : State w h) (hsm : s.stringMode = false)
    (hcell : s.grid.get s.pc.1 s.pc.2 = ' ') :
    step s = some { s with pc := stepPos w h s.dir s.pc } := by
  unfold step
  have hdec : decodeChar ' ' = .nop := by
    unfold decodeChar
    rfl
  simp only [hsm, hcell, hdec, stepState]

/-- Running `n` steps through a run of spaces moves the pointer by `runPos`
    and preserves the stack, the grid, the direction, string mode, the output,
    and the input stream. -/
theorem run_spaces (x y n : ℕ) (s : State w h)
    (hpc : s.pc = (x % w, y % h))
    (hsm : s.stringMode = false)
    (hspaces : SpacesRun s.grid s.dir x y n) :
    run n s = some { s with pc := runPos w h n s.dir (x % w, y % h) } := by
  induction n with
  | zero =>
      rw [run]
      congr 1
      simp only [runPos, ← hpc]
  | succ n ih =>
      have hrun : run n s = some { s with pc := runPos w h n s.dir (x % w, y % h) } :=
        ih (fun k hk => hspaces k (Nat.lt_trans hk (Nat.lt_succ_self n)))
      rw [show run (n + 1) s = (run n s).bind step by rfl]
      rw [hrun]
      change step { s with pc := runPos w h n s.dir (x % w, y % h) }
        = some { s with pc := runPos w h (n + 1) s.dir (x % w, y % h) }
      refine step_space { s with pc := runPos w h n s.dir (x % w, y % h) } ?_ ?_
      · change s.stringMode = false
        exact hsm
      · exact hspaces n (Nat.lt_succ_self n)

/-- A run of spaces followed by a `v` turn leaves the pointer moving down at
    the cell below the `v`: the corridor pattern that drops the pointer into a
    target row. -/
theorem run_spaces_v (x y n : ℕ) (s : State w h)
    (hpc : s.pc = (x % w, y % h))
    (hsm : s.stringMode = false)
    (hdir : s.dir = Direction.right)
    (hspaces : SpacesRun s.grid Direction.right x y n)
    (hv : s.grid.get (runPos w h n Direction.right (x % w, y % h)).1
        (runPos w h n Direction.right (x % w, y % h)).2 = 'v') :
    run (n + 1) s =
      some { s with
        dir := Direction.down,
        pc := stepPos w h Direction.down (runPos w h n Direction.right (x % w, y % h)) } := by
  rw [show run (n + 1) s = (run n s).bind step by rfl]
  rw [run_spaces x y n s hpc hsm (by simpa only [← hdir] using hspaces)]
  rw [hdir]
  rw [show (some { s with
        pc := runPos w h n Direction.right (x % w, y % h),
        dir := Direction.right }).bind step
      = step { s with
        pc := runPos w h n Direction.right (x % w, y % h),
        dir := Direction.right } by rfl]
  rw [step_dir_down]
  · change s.stringMode = false
    exact hsm
  · exact hv

end LeanFunge
