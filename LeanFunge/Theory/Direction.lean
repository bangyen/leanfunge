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
* `runPos_down`: Iterating downward steps lands at the modular row.
* `stepPos_lt`: Moving the pointer always lands inside the playfield.
* `runPos_up`: Iterating upward steps lands at the modular row.
* `runPos_left`: Iterating leftward steps lands at the modular column.
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

/-- Iterating downward steps from a reduced row lands at the modular offset:
    after `k` steps the row is `(y + k) % h`. -/
theorem runPos_down (w h k x y : ℕ) :
    runPos w h k Direction.down (x % w, y % h) = (x % w, (y + k) % h) := by
  induction k with
  | zero =>
      simp only [runPos]
      rw [Nat.add_zero]
  | succ k ih =>
      simp only [runPos, ih, stepPos]
      have hy : ((y + k) % h + 1) % h = (y + (k + 1)) % h := by
        rw [← Nat.add_assoc]
        conv =>
          lhs
          rw [Nat.add_mod]
          rw [Nat.mod_mod]
        conv =>
          rhs
          rw [Nat.add_mod]
      have hx : (x % w) % w = x % w := Nat.mod_mod _ _
      rw [hy, hx]

/-- Iterating upward steps from a reduced row lands at the modular offset:
    each step adds `h - 1` modulo `h`. -/
theorem runPos_up {w h : ℕ} [NeZero h] (k x y : ℕ) :
    runPos w h k Direction.up (x % w, y % h) = (x % w, (y + k * (h - 1)) % h) := by
  have hpos : 0 < h := Nat.pos_of_neZero h
  induction k with
  | zero =>
      simp only [runPos]
      rw [Nat.zero_mul, Nat.add_zero]
  | succ k ih =>
      simp only [runPos, ih, stepPos]
      have hy : ((y + k * (h - 1)) % h + (h - 1)) % h = (y + (k + 1) * (h - 1)) % h := by
        rw [Nat.add_mul, Nat.one_mul]
        rw [← Nat.add_assoc]
        conv =>
          rhs
          rw [Nat.add_mod]
          rw [Nat.mod_eq_of_lt (show h - 1 < h by omega)]
      have hx : (x % w) % w = x % w := Nat.mod_mod _ _
      have hsub : (y + k * (h - 1)) % h + h - 1 = (y + k * (h - 1)) % h + (h - 1) := by
        rw [Nat.add_sub_assoc (show 1 ≤ h by omega)]
      rw [hsub, hx, hy]

/-- Iterating leftward steps from a reduced column lands at the modular offset:
    each step adds `w - 1` modulo `w`. -/
theorem runPos_left {w h : ℕ} [NeZero w] (k x y : ℕ) :
    runPos w h k Direction.left (x % w, y % h) = ((x + k * (w - 1)) % w, y % h) := by
  have hpos : 0 < w := Nat.pos_of_neZero w
  induction k with
  | zero =>
      simp only [runPos]
      rw [Nat.zero_mul, Nat.add_zero]
  | succ k ih =>
      simp only [runPos, ih, stepPos]
      have hx : ((x + k * (w - 1)) % w + (w - 1)) % w = (x + (k + 1) * (w - 1)) % w := by
        rw [Nat.add_mul, Nat.one_mul]
        rw [← Nat.add_assoc]
        conv =>
          rhs
          rw [Nat.add_mod]
          rw [Nat.mod_eq_of_lt (show w - 1 < w by omega)]
      have hy : (y % h) % h = y % h := Nat.mod_mod _ _
      have hsub : (x + k * (w - 1)) % w + w - 1 = (x + k * (w - 1)) % w + (w - 1) := by
        rw [Nat.add_sub_assoc (show 1 ≤ w by omega)]
      rw [hsub, hy, hx]

/-- Moving the pointer always lands inside the playfield: every direction
    reduces the coordinate modulo the playfield size. -/
theorem stepPos_lt (hw : 0 < w) (hh : 0 < h) (d : Direction) (p : ℕ × ℕ) :
    (stepPos w h d p).1 < w ∧ (stepPos w h d p).2 < h := by
  cases d <;>
    exact ⟨Nat.mod_lt _ hw, Nat.mod_lt _ hh⟩

end LeanFunge
