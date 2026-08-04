/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import Mathlib.Data.Nat.Notation

/-!
# The Playfield

## Main definitions

* `Grid`: A `w`×`h` playfield of characters.
* `Grid.get`: Read the cell at wrapped coordinates.
* `Grid.put`: Write a character at wrapped coordinates.
* `Grid.space`: The all-space playfield.
* `Grid.ofRows`: Build a playfield from a list of rows.
-/

namespace LeanFunge

/-- A playfield: an infinite function of cells, with accessors that reduce
    coordinates modulo the `w`×`h` size. -/
structure Grid (w h : ℕ) where
  /-- The raw cell function, indexed by row then column. -/
  cells : ℕ → ℕ → Char

namespace Grid

/-- Read the cell at `(x, y)`, wrapping into the `w`×`h` playfield. -/
def get (g : Grid w h) (x y : ℕ) : Char :=
  g.cells (y % h) (x % w)

/-- Write a character at `(x, y)` (wrapped). -/
def put (g : Grid w h) (x y : ℕ) (c : Char) : Grid w h :=
  { cells := fun yy xx => if xx = x % w ∧ yy = y % h then c else g.cells yy xx }

/-- The all-space playfield. -/
def space (w h : ℕ) : Grid w h :=
  { cells := fun _ _ => ' ' }

/-- Build a playfield from a list of rows; missing cells are spaces. -/
def ofRows (w h : ℕ) (rows : List (List Char)) : Grid w h :=
  { cells := fun y x => (rows.getD y []).getD x ' ' }

/-- Add a leading space column, shifting the original playfield right by one
    cell. -/
def prependSpace (g : Grid w h) : Grid (w + 1) h :=
  { cells := fun y x => if x = 0 then ' ' else g.get (x - 1) y }

/-- Add `k` leading space columns, shifting the original playfield right by
    `k` cells. -/
def prependSpaces (g : Grid w h) (k : ℕ) : Grid (w + k) h :=
  { cells := fun y x => if x < k then ' ' else g.get (x - k) y }

/-- Rotate a playfield clockwise at the raw-cell level. The `w`×`h` grid
    becomes `h`×`w`. -/
def rotateCW (g : Grid w h) : Grid h w :=
  { cells := fun y x => g.cells (h - 1 - x) y }

end Grid

end LeanFunge
