/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanFunge.Theory.Completeness.Routing
import Mathlib.Tactic.IntervalCases

/-!
# Straight-Line Routing Tests
-/

namespace LeanFunge.Tests

example (s : State w h) (hsm : s.stringMode = false)
    (hcell : s.grid.get s.pc.1 s.pc.2 = ' ') :
    step s = some { s with pc := stepPos w h s.dir s.pc } :=
  step_space s hsm hcell

example (x y n : ℕ) (s : State w h)
    (hpc : s.pc = (x % w, y % h))
    (hsm : s.stringMode = false)
    (hspaces : SpacesRun s.grid s.dir x y n) :
    run n s = some { s with pc := runPos w h n s.dir (x % w, y % h) } :=
  run_spaces x y n s hpc hsm hspaces

example (x y n : ℕ) (s : State w h)
    (hpc : s.pc = (x % w, y % h))
    (hsm : s.stringMode = false)
    (hdir : s.dir = Direction.right)
    (hspaces : SpacesRun s.grid Direction.right x y n)
    (hv : s.grid.get (runPos w h n Direction.right (x % w, y % h)).1
        (runPos w h n Direction.right (x % w, y % h)).2 = 'v') :
    run (n + 1) s =
      some { s with
        dir := Direction.down,
        pc := stepPos w h Direction.down (runPos w h n Direction.right (x % w, y % h)) } :=
  run_spaces_v x y n s hpc hsm hdir hspaces hv

/-- The corridor pattern on a concrete grid: three spaces then a `v` drop the
    pointer one row down, moving down at the cell below the `v`. -/
example :
    (run 4 { State.init (Grid.ofRows 8 3
        [String.toList "   v       ",
         String.toList "           ",
         String.toList "           "]) with
        pc := (0, 0), dir := .right }).map (fun s => (s.dir, s.pc))
      = some (Direction.down, (3, 1)) := by
  rw [run_spaces_v 0 0 3 _ (by rfl) (by rfl) (by rfl)
      (by intro k hk; interval_cases k <;> decide) (by rfl)]
  decide

end LeanFunge.Tests
