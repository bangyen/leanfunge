/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import Batteries.Data.Char.Basic
import LeanFunge.Core.Grid
import Mathlib.Data.List.GetD
import Mathlib.Data.Nat.Notation

/-!
# Playfield Algebra

## Theorems

* `get_put_self`: Reading a cell immediately after writing returns the value.
* `put_put`: Writing twice is the same as writing only the last value.
* `get_put_other`: Writing to one cell does not disturb distinct cells.
* `put_get_roundtrip`: A value written by `p` is read back by `g`.
* `put_get_wrapped`: `put` writes the wrapped cell, and `get` at the wrapped
  coordinates reads it back.
* `ofRows_cells_out_of_rows`: Missing rows are spaces.
* `ofRows_cells_out_of_col`: Missing cells in a row are spaces.
* `get_eq_get_mod`: Reading a cell ignores any out-of-range coordinates.
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

/-- The cell written by `p` holds the character `Char.ofNat (Int.toNat v)`, and
    `g` reading it back recovers the value `v` for a valid non-negative code:
    the interpreter's `p`/`g` round-trip. -/
theorem put_get_roundtrip {w h : ℕ} (g : Grid w h) (y x v : Int)
    (hvalid : (Int.toNat v).isValidChar) (hv : 0 ≤ v) :
    Int.ofNat
        ((Grid.put g (Int.toNat x) (Int.toNat y) (Char.ofNat (Int.toNat v))).get (Int.toNat x)
            (Int.toNat y)).toNat = v := by
  have hcode :
      (Grid.put g (Int.toNat x) (Int.toNat y) (Char.ofNat (Int.toNat v))).get (Int.toNat x)
        (Int.toNat y) = Char.ofNat (Int.toNat v) :=
    Grid.get_put_self g (Int.toNat x) (Int.toNat y) (Char.ofNat (Int.toNat v))
  rw [hcode]
  rw [Char.toNat_ofNat (Int.toNat v), if_pos hvalid]
  change (Int.toNat v : Int) = v
  rw [Int.ofNat_toNat v]
  omega

/-- `put` writes the wrapped cell: `get` at the wrapped coordinates reads the
    stored value. -/
theorem put_get_wrapped (g : Grid w h) (x y : ℕ) (c : Char) :
    Grid.get (Grid.put g x y c) (x % w) (y % h) = c := by
  unfold Grid.get Grid.put
  have hx : (x % w) % w = x % w := Nat.mod_mod _ _
  have hy : (y % h) % h = y % h := Nat.mod_mod _ _
  rw [hx, hy]
  change (if (x % w) = x % w ∧ (y % h) = y % h then c else g.cells (y % h) (x % w)) = c
  exact dif_pos ⟨rfl, rfl⟩

/-- A playfield built by `ofRows` treats rows beyond the given list as spaces. -/
theorem ofRows_cells_out_of_rows (rows : List (List Char)) (hy : rows.length ≤ y) :
    (Grid.ofRows w h rows).cells y x = ' ' := by
  unfold Grid.ofRows
  change (rows.getD y []).getD x ' ' = ' '
  have h1 : rows.getD y [] = [] :=
    List.getD_eq_default (l := rows) (n := y) (d := []) hy
  rw [h1]
  rfl

/-- A playfield built by `ofRows` treats cells beyond a row's width as spaces. -/
theorem ofRows_cells_out_of_col (row : List Char) (hx : row.length ≤ x) :
    (List.getD row x ' ' : Char) = ' ' := by
  exact List.getD_eq_default (l := row) (n := x) (d := ' ') hx

end Grid

/-- Reading a cell ignores any out-of-range part of the coordinates: the
    playfield is a torus, so a pointer outside the grid still reads the
    wrapped cell. -/
theorem get_eq_get_mod (g : Grid w h) (x y : ℕ) :
    g.get x y = g.get (x % w) (y % h) := by
  unfold Grid.get
  simp only [Nat.mod_mod]

end LeanFunge
