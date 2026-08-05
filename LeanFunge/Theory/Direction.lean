/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanFunge.Core.Direction
import Mathlib.Data.Nat.Notation

/-!
# Toroidal Wrapping

## Theorems

* `stepPos_right_from_last`: Moving right from the last column wraps to 0.
* `stepPos_left_from_zero`: Moving left from column 0 wraps to the last column.
* `stepPos_down_from_last`: Moving down from the last row wraps to 0.
* `stepPos_up_from_zero`: Moving up from row 0 wraps to the last row.
* `runPos_right`: Iterating rightward steps lands at the modular column.
-/

namespace LeanFunge

/-- Moving right from the last column wraps to column 0. -/
theorem stepPos_right_from_last {w h : ℕ} [NeZero w] (y : ℕ) :
    stepPos w h Direction.right (w - 1, y) = (0, y % h) := by
  unfold stepPos
  rw [Nat.sub_add_cancel (Nat.succ_le_of_lt (Nat.pos_of_neZero w)), Nat.mod_self]

/-- Moving left from column 0 wraps to the last column. -/
theorem stepPos_left_from_zero {w h : ℕ} [NeZero w] (y : ℕ) :
    stepPos w h Direction.left (0, y) = (w - 1, y % h) := by
  unfold stepPos
  have hlt : w - 1 < w := Nat.sub_lt (Nat.pos_of_neZero w) (by decide)
  simp only [Nat.zero_add, Nat.mod_eq_of_lt hlt]

/-- Moving down from the last row wraps to row 0. -/
theorem stepPos_down_from_last {w h : ℕ} [NeZero h] (x : ℕ) :
    stepPos w h Direction.down (x, h - 1) = (x % w, 0) := by
  unfold stepPos
  rw [Nat.sub_add_cancel (Nat.succ_le_of_lt (Nat.pos_of_neZero h)), Nat.mod_self]

/-- Moving up from row 0 wraps to the last row. -/
theorem stepPos_up_from_zero {w h : ℕ} [NeZero h] (x : ℕ) :
    stepPos w h Direction.up (x, 0) = (x % w, h - 1) := by
  unfold stepPos
  have hlt : h - 1 < h := Nat.sub_lt (Nat.pos_of_neZero h) (by decide)
  simp only [Nat.zero_add, Nat.mod_eq_of_lt hlt]

/-- Iterating rightward steps from a reduced column lands at the modular
    offset: after `k` steps the column is `(x + k) % w`. -/
theorem runPos_right (w h k x y : ℕ) :
    runPos w h k Direction.right (x % w, y % h) = ((x + k) % w, y % h) := by
  induction k with
  | zero =>
      simp only [runPos]
      rw [Nat.add_zero]
  | succ k ih =>
      simp only [runPos, ih, stepPos]
      have hx : ((x + k) % w + 1) % w = (x + (k + 1)) % w := by
        rw [← Nat.add_assoc]
        conv =>
          lhs
          rw [Nat.add_mod]
          rw [Nat.mod_mod]
        conv =>
          rhs
          rw [Nat.add_mod]
      have hy : (y % h) % h = y % h := Nat.mod_mod _ _
      rw [hx, hy]

end LeanFunge
