/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanFunge.Core.Grid
import Mathlib.Data.Nat.Notation

/-!
# Playfield Algebra

## Theorems

* `get_put_self`: Reading a cell immediately after writing returns the value.
* `put_put`: Writing twice is the same as writing only the last value.
* `get_put_other`: Writing to one cell does not disturb distinct cells.
-/

namespace LeanFunge
namespace Grid

/-- Reading a cell immediately after writing returns the value. -/
theorem get_put_self (g : Grid w h) (x y : ℕ) (c : Char) :
    Grid.get (Grid.put g x y c) x y = c := by
  unfold Grid.get Grid.put
  change (if (x % w) = x % w ∧ (y % h) = y % h then c else g.cells (y % h) (x % w)) = c
  exact dif_pos ⟨rfl, rfl⟩

/-- Writing twice is the same as writing only the last value. -/
theorem put_put (g : Grid w h) (x y : ℕ) (c1 c2 : Char) :
    Grid.put (Grid.put g x y c1) x y c2 = Grid.put g x y c2 := by
  apply congrArg (fun f : ℕ → ℕ → Char => ({ cells := f } : Grid w h))
  funext yy xx
  let p : Prop := xx = x % w ∧ yy = y % h
  change (if p then c2 else (if p then c1 else g.cells yy xx)) =
    (if p then c2 else g.cells yy xx)
  by_cases hc : p
  · have h1 : (if p then c2 else (if p then c1 else g.cells yy xx)) = c2 := dif_pos hc
    have h2 : (if p then c2 else g.cells yy xx) = c2 := dif_pos hc
    exact h1.trans h2.symm
  · have h1 : (if p then c2 else (if p then c1 else g.cells yy xx)) = g.cells yy xx :=
      (dif_neg hc).trans (dif_neg hc)
    have h2 : (if p then c2 else g.cells yy xx) = g.cells yy xx := dif_neg hc
    exact h1.trans h2.symm

/-- Writing to one cell does not disturb distinct cells. -/
theorem get_put_other (g : Grid w h) (x1 y1 x2 y2 : ℕ) (c : Char)
    (hdist : x1 % w ≠ x2 % w ∨ y1 % h ≠ y2 % h) :
    Grid.get (Grid.put g x2 y2 c) x1 y1 = Grid.get g x1 y1 := by
  unfold Grid.get Grid.put
  let q : Prop := x1 % w = x2 % w ∧ y1 % h = y2 % h
  change (if q then c else g.cells (y1 % h) (x1 % w)) = g.cells (y1 % h) (x1 % w)
  by_cases hx : x1 % w = x2 % w
  · have hy : y1 % h ≠ y2 % h := by
      intro hEq
      rcases hdist with h | h
      · exact h hx
      · exact h hEq
    have hne : ¬ q := by
      intro hAnd
      exact hy hAnd.2
    exact dif_neg hne
  · have hne : ¬ q := by
      intro hAnd
      exact hx hAnd.1
    exact dif_neg hne

/-- Leading-space padding preserves each original cell at its shifted
    coordinate, before the new toroidal boundary. -/
theorem get_prependSpace_succ (g : Grid w h) (x y : ℕ) (hx : x < w) :
    (Grid.prependSpace g).get (x + 1) y = g.get x y := by
  unfold Grid.get Grid.prependSpace
  dsimp
  have hmod : (x + 1) % (w + 1) = x + 1 :=
    Nat.mod_eq_of_lt (Nat.succ_lt_succ hx)
  rw [hmod]
  simp [Grid.get]

/-- Arbitrary leading-space padding preserves each original cell at its
    translated coordinate, before the new toroidal boundary. -/
theorem get_prependSpaces_add (g : Grid w h) (k x y : ℕ) (hx : x < w) :
    (Grid.prependSpaces g k).get (x + k) y = g.get x y := by
  unfold Grid.get Grid.prependSpaces
  dsimp
  have hmod : (x + k) % (w + k) = x + k :=
    Nat.mod_eq_of_lt (Nat.add_lt_add_right hx k)
  rw [hmod]
  have hnot : ¬ x + k < k := by omega
  simp [hnot, Grid.get]

/-- A clockwise rotation maps an old raw cell `(x, y)` to `(h - 1 - y, x)`. -/
theorem rotateCW_cell (g : Grid w h) (x y : ℕ) (hy : y < h) :
    (Grid.rotateCW g).cells x (h - 1 - y) = g.cells y x := by
  unfold Grid.rotateCW
  dsimp
  have hcoord : h - 1 - (h - 1 - y) = y := by omega
  rw [hcoord]

end Grid
end LeanFunge
