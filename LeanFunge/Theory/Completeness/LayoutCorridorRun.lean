/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanFunge.Theory.Completeness.LayoutCells
import LeanFunge.Theory.Completeness.LayoutCorridor
import LeanFunge.Theory.Completeness.LayoutCorridorRow
import LeanFunge.Theory.Direction
import Mathlib.Tactic

/-!
# The Corridor Run Machinery

The modular position arithmetic for straight runs inside the playfield, the
turn and drop cell lookups of a jump edge, and the direction-independent step
facts used to compose a corridor run.

## Theorems

* `mod_step_up`: `(b + k * (n - 1)) % n = b - k` for an up-run staying in range.
* `runPos_up_pos`, `runPos_right_pos`, `runPos_left_pos`, `runPos_down_pos`: Iterated steps inside the playfield land at the un-wrapped position.
* `stepPos_left_pos`: A left step inside the playfield does not wrap.
* `corridor_turn`: The turn cell of a jump edge points toward the target.
* `corridor_drop`: The drop cell of a jump edge is a `v`.
-/

namespace LeanFunge

namespace Completeness

/-- `(b + k * (n - 1)) % n = b - k`: stepping `k` cells upward (adding `n - 1`
    each time) lands at `b - k` when the result stays above zero. -/
theorem mod_step_up (b k n : ℕ) (hk : k ≤ b) (hb : b - k < n) :
    (b + k * (n - 1)) % n = b - k := by
  have hb' : b = (b - k) + k := by omega
  have hmul : k * n = k * (n - 1) + k := by
    calc
      k * n = k * ((n - 1) + 1) := by congr; omega
      _ = k * (n - 1) + k * 1 := Nat.mul_add k (n - 1) 1
      _ = k * (n - 1) + k := by rw [Nat.mul_one]
  have hz : b + k * (n - 1) = (b - k) + k * n := by
    calc
      b + k * (n - 1) = ((b - k) + k) + k * (n - 1) := by omega
      _ = (b - k) + k * n := by omega
  rw [hz]
  rw [Nat.add_mul_mod_self_right]
  rw [Nat.mod_eq_of_lt hb]

/-- Iterated up steps inside the playfield land at the reduced row. -/
lemma runPos_up_pos (w h : ℕ) (x y k : ℕ) (hx : x < w) (hk : k ≤ y) (hy : y < h) :
    runPos w h k Direction.up (x % w, y % h) = (x, y - k) := by
  have hmod : ∀ r : ℕ, 1 ≤ r → r ≤ h → (r + h - 1) % h = r - 1 := by
    intro r hr1 hrh
    by_cases hrlt : r < h
    · have hz : r + h - 1 = (r - 1) + h := by omega
      rw [hz, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega : r - 1 < h)]
    · have hr : r = h := by omega
      subst r
      have hz : h + h - 1 = (h - 1) + h := by omega
      rw [hz, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega : h - 1 < h)]
  induction k with
  | zero =>
      simp only [runPos]
      congr
      · exact Nat.mod_eq_of_lt hx
      · exact Nat.mod_eq_of_lt hy
  | succ k ih =>
      have hih : runPos w h k Direction.up (x % w, y % h) = (x, y - k) := ih (by omega)
      have hstep : stepPos w h Direction.up (x, y - k) = (x, y - k - 1) := by
        unfold stepPos
        rw [Nat.mod_eq_of_lt hx]
        rw [hmod (y - k) (by omega) (by omega)]
      calc
        runPos w h (k + 1) Direction.up (x % w, y % h)
            = stepPos w h Direction.up (runPos w h k Direction.up (x % w, y % h)) := by simp only [runPos]
        _ = stepPos w h Direction.up (x, y - k) := by rw [hih]
        _ = (x, y - k - 1) := hstep
        _ = (x, y - (k + 1)) := by simp only [Nat.sub_sub]

/-- Iterated right steps inside the playfield land at the offset column. -/
lemma runPos_right_pos (w h : ℕ) (x y k : ℕ) (hx : x + k < w) (hy : y < h) :
    runPos w h k Direction.right (x % w, y % h) = (x + k, y) := by
  rw [runPos_right]
  congr
  · rw [Nat.mod_eq_of_lt hx]
  · rw [Nat.mod_eq_of_lt hy]

/-- Iterated left steps inside the playfield land at the reduced column. -/
lemma runPos_left_pos (w h : ℕ) (x y k : ℕ) (hy : y < h) (hk : k ≤ x) (hx : x < w) :
    runPos w h k Direction.left (x % w, y % h) = (x - k, y) := by
  have hmod : ∀ r : ℕ, 1 ≤ r → r ≤ w → (r + w - 1) % w = r - 1 := by
    intro r hr1 hrw
    by_cases hrlt : r < w
    · have hz : r + w - 1 = (r - 1) + w := by omega
      rw [hz, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega : r - 1 < w)]
    · have hr : r = w := by omega
      subst r
      have hz : w + w - 1 = (w - 1) + w := by omega
      rw [hz, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega : w - 1 < w)]
  induction k with
  | zero =>
      simp only [runPos]
      congr
      · exact Nat.mod_eq_of_lt hx
      · exact Nat.mod_eq_of_lt hy
  | succ k ih =>
      have hih : runPos w h k Direction.left (x % w, y % h) = (x - k, y) := ih (by omega)
      have hstep : stepPos w h Direction.left (x - k, y) = (x - k - 1, y) := by
        unfold stepPos
        rw [Nat.mod_eq_of_lt hy]
        rw [hmod (x - k) (by omega) (by omega)]
      calc
        runPos w h (k + 1) Direction.left (x % w, y % h)
            = stepPos w h Direction.left (runPos w h k Direction.left (x % w, y % h)) := by simp only [runPos]
        _ = stepPos w h Direction.left (x - k, y) := by rw [hih]
        _ = (x - k - 1, y) := hstep
        _ = (x - (k + 1), y) := by simp only [Nat.sub_sub]

/-- Iterated down steps inside the playfield land at the offset row. -/
lemma runPos_down_pos (w h : ℕ) (x y k : ℕ) (hx : x < w) (hb : y + k < h) :
    runPos w h k Direction.down (x % w, y % h) = (x, y + k) := by
  rw [runPos_down]
  congr
  · rw [Nat.mod_eq_of_lt hx]
  · rw [Nat.mod_eq_of_lt hb]

/-- A left step inside the playfield does not wrap. -/
lemma stepPos_left_pos (w h : ℕ) (p y : ℕ) (hp0 : 0 < p) (hp : p < w) (hy : y < h) :
    stepPos w h Direction.left (p, y) = (p - 1, y) := by
  unfold stepPos
  have hmod : (p + w - 1) % w = p - 1 := by
    have hz : p + w - 1 = (p - 1) + w := by omega
    rw [hz]
    rw [Nat.add_mod_right]
    rw [Nat.mod_eq_of_lt (by omega)]
  rw [hmod, Nat.mod_eq_of_lt hy]

/-- The turn cell of a jump edge on its header row points toward the target. -/
theorem corridor_turn (prog : CMProgram) (i k : ℕ) (c : Fin 2)
    (hget : prog.getD i .halt = .decz c k ∨ prog.getD i .halt = .jump k) :
    corridorRowAt prog (branchColumn prog i) i
      = if entryColumn prog k ≥ branchColumn prog i then '>' else '<' := by
  rcases hget with hget | hget
  · have hCeq : branchColumn prog i = entryColumn prog i + 4 := by
      rw [branchColumn, hget]
      norm_num [blockWidth]
    unfold corridorRowAt
    rw [hget]
    simp [hCeq]
  · have hCeq : branchColumn prog i = entryColumn prog i + 1 := by
      rw [branchColumn, hget]
      norm_num [blockWidth]
    unfold corridorRowAt
    rw [hget]
    simp [hCeq]

/-- The drop cell of a jump edge on its header row is a `v`. -/
theorem corridor_drop (prog : CMProgram) (i k : ℕ) (c : Fin 2)
    (hget : prog.getD i .halt = .decz c k ∨ prog.getD i .halt = .jump k)
    (hCneK : branchColumn prog i ≠ entryColumn prog k) :
    corridorRowAt prog (entryColumn prog k) i = 'v' := by
  rcases hget with hget | hget
  · unfold corridorRowAt
    rw [hget]
    have hne : entryColumn prog k ≠ entryColumn prog i + 4 := by
      intro h
      exact hCneK (by
        rw [branchColumn, hget]
        norm_num [blockWidth]
        exact h.symm)
    simp [hne]
  · unfold corridorRowAt
    rw [hget]
    have hne : entryColumn prog k ≠ entryColumn prog i + 1 := by
      intro h
      exact hCneK (by
        rw [branchColumn, hget]
        norm_num [blockWidth]
        exact h.symm)
    simp [hne]

end Completeness

end LeanFunge
