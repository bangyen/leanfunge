/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanFunge.Theory.Direction

/-!
# Direction Tests
-/

namespace LeanFunge.Tests

open LeanFunge

example : stepPos 80 25 Direction.right (79, 0) = (0, 0) := by
  simpa only [] using (stepPos_right_from_last (w := 80) (h := 25) (y := 0))

example : stepPos 80 25 Direction.left (0, 0) = (79, 0) := by
  simpa only [] using (stepPos_left_from_zero (w := 80) (h := 25) (y := 0))

example : stepPos 80 25 Direction.down (0, 24) = (0, 0) := by
  simpa only [] using (stepPos_down_from_last (w := 80) (h := 25) (x := 0))

example : stepPos 80 25 Direction.up (0, 0) = (0, 24) := by
  simpa only [] using (stepPos_up_from_zero (w := 80) (h := 25) (x := 0))

example : runPos 80 25 10 Direction.right (3, 0) = (13, 0) := by
  simpa only [Nat.reduceAdd] using (runPos_right (w := 80) (h := 25) (k := 10) (x := 3) (y := 0))

example : runPos 80 25 80 Direction.right (3, 0) = (3, 0) := by
  simpa only [Nat.reduceAdd, Nat.mod_self] using
    (runPos_right (w := 80) (h := 25) (k := 80) (x := 3) (y := 0))

example : runPos 80 25 10 Direction.down (3, 0) = (3, 10) := by
  decide

example : runPos 80 25 30 Direction.up (3, 0) = (3, 20) := by
  decide

example : runPos 80 25 30 Direction.left (3, 0) = (53, 0) := by
  decide

end LeanFunge.Tests
