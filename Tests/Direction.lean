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

end LeanFunge.Tests
