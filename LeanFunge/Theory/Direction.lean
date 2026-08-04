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

/-- Clockwise rotation commutes with a rightward step when it does not wrap. -/
theorem stepPos_rotateCW_right (x y : ℕ) (hx : x + 1 < w) (hy : y < h) :
    stepPos h w Direction.down (h - 1 - y, x) = (h - 1 - y, x + 1) := by
  unfold stepPos
  have hy' : h - 1 - y < h := by omega
  simp [Nat.mod_eq_of_lt hy', Nat.mod_eq_of_lt hx]

/-- Clockwise rotation commutes with a leftward step when it does not wrap. -/
theorem stepPos_rotateCW_left (x y : ℕ) (hx : 0 < x) (hxw : x < w) (hy : y < h) :
    stepPos h w Direction.up (h - 1 - y, x) = (h - 1 - y, x - 1) := by
  unfold stepPos
  have hy' : h - 1 - y < h := by omega
  have hx' : x - 1 < w := by omega
  have hsum : x + w - 1 = w + (x - 1) := by omega
  rw [hsum]
  simp [Nat.mod_eq_of_lt hy', Nat.mod_eq_of_lt hx']

/-- Clockwise rotation commutes with a downward step when it does not wrap. -/
theorem stepPos_rotateCW_down (x y : ℕ) (hx : x < w) (hy : y + 1 < h) :
    stepPos h w Direction.left (h - 1 - y, x) = (h - 2 - y, x) := by
  unfold stepPos
  have hy' : h - 2 - y < h := by omega
  have hsum : h - 1 - y + h - 1 = h + (h - 2 - y) := by omega
  rw [hsum]
  simp [Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy']

/-- Clockwise rotation commutes with an upward step when it does not wrap. -/
theorem stepPos_rotateCW_up (x y : ℕ) (hx : x < w) (hy : 0 < y) (hyh : y < h) :
    stepPos h w Direction.right (h - 1 - y, x) = (h - y, x) := by
  unfold stepPos
  have hsum : h - 1 - y + 1 = h - y := by omega
  have hy' : h - y < h := by omega
  rw [hsum]
  simp [Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy']

end LeanFunge
