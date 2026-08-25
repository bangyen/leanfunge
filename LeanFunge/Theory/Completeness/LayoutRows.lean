/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanFunge.Theory.Completeness.LayoutCells

/-!
# The Generated Playfield as Text

`playfieldOf` builds a `Grid`, whose `cells` field is a *function*
`ℕ → ℕ → Char`. A function type is not `Primcodable`, so no statement quantifying
over grids can be the domain of a `ComputablePred` (see `UNDECIDABILITY.md`).

This module supplies the text form. `playfieldRowsOf` emits the same playfield
as a `List (List Char)` — a `Primcodable` type — and `ofRows_playfieldRowsOf`
proves the two agree *as grids*, not merely pointwise on `get`. Literal grid
equality is what lets the simulation theorems transport by rewriting, with no
bisimulation layer in between.

The construction leans on `playfieldOf_get_eq_lastCellAt`: every cell of the
generated playfield is the last cell placed at that position, so emitting rows
that read `lastCellAt` over the exact `playfieldHeight × playfieldWidth` extent
reproduces the grid by construction.

## Main definitions

* `playfieldRowsOf`: The generated playfield as a list of rows.

## Theorems

* `playfieldRowsOf_length`: The row count is the playfield height.
* `playfieldRowsOf_row_length`: Every row has the playfield width.
* `playfieldOf_cells`: The raw cell function is the last-placed cell in range.
* `ofRows_playfieldRowsOf`: The text form rebuilds the generated playfield.
-/

namespace LeanFunge

namespace Completeness

open Grid

/-- The generated playfield as a list of rows, each of width
    `playfieldWidth prog`, with `playfieldHeight prog` rows. -/
def playfieldRowsOf (prog : CMProgram) : List (List Char) :=
  (List.range (playfieldHeight prog)).map fun y =>
    (List.range (playfieldWidth prog)).map fun x =>
      lastCellAt (playfieldWidth prog) (playfieldHeight prog) ' ' (playfieldCells prog) x y

/-- The generated playfield has one row per playfield row. -/
@[simp]
theorem playfieldRowsOf_length (prog : CMProgram) :
    (playfieldRowsOf prog).length = playfieldHeight prog := by
  simp [playfieldRowsOf]

/-- Every generated row spans the playfield width. -/
theorem playfieldRowsOf_row_length (prog : CMProgram) (row : List Char)
    (hrow : row ∈ playfieldRowsOf prog) : row.length = playfieldWidth prog := by
  unfold playfieldRowsOf at hrow
  rcases List.mem_map.1 hrow with ⟨y, -, rfl⟩
  simp

/-- The row at `y`, inside the playfield, is the mapped range of that row. -/
theorem playfieldRowsOf_getD_row (prog : CMProgram) (y : ℕ)
    (hy : y < playfieldHeight prog) :
    (playfieldRowsOf prog).getD y []
      = (List.range (playfieldWidth prog)).map fun x =>
          lastCellAt (playfieldWidth prog) (playfieldHeight prog) ' '
            (playfieldCells prog) x y := by
  unfold playfieldRowsOf
  rw [List.getD_eq_getElem?_getD]
  simp only [List.getElem?_map, List.getElem?_range, hy, Option.map_some, Option.getD_some]

/-- Every row of the text form is at most the playfield width, including the
    empty padding row past the last. -/
theorem playfieldRowsOf_getD_length (prog : CMProgram) (y : ℕ) :
    ((playfieldRowsOf prog).getD y []).length ≤ playfieldWidth prog := by
  unfold playfieldRowsOf
  by_cases hy : y < playfieldHeight prog
  · rw [List.getD_eq_getElem?_getD]
    simp only [List.getElem?_map, List.getElem?_range, hy, Option.map_some, Option.getD_some]
    simp
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp; omega)]
    simp

/-- Past the playfield width, the text form reads a space. -/
theorem playfieldRowsOf_getD_out_width (prog : CMProgram) (x y : ℕ)
    (hx : ¬ x < playfieldWidth prog) :
    ((playfieldRowsOf prog).getD y []).getD x ' ' = ' ' := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none]
  · rfl
  · exact le_trans (playfieldRowsOf_getD_length prog y) (Nat.not_lt.1 hx)

/-- A nonempty program has positive width. -/
theorem playfieldWidth_pos (prog : CMProgram) (hne : prog ≠ []) :
    0 < playfieldWidth prog := by
  have hlen : 0 < prog.length := List.length_pos_of_ne_nil hne
  unfold playfieldWidth
  calc 0 = entryColumn prog 0 := rfl
    _ < entryColumn prog prog.length := entryColumn_strict_mono prog hlen

/-- A nonempty program has positive height. -/
theorem playfieldHeight_pos (prog : CMProgram) (hne : prog ≠ []) :
    0 < playfieldHeight prog := by
  have hlen : 0 < prog.length := List.length_pos_of_ne_nil hne
  exact lt_of_lt_of_le hlen (blockRow_ge_length prog prog.length)

/-- Folding puts, read at raw coordinates in range, is the last-cell lookup.
    The `get`-level twin is `foldl_put_get`; this is the `cells`-level form the
    grid equality needs. -/
theorem foldl_put_cells (g : Grid w h) (cells : List ((ℕ × ℕ) × Char))
    (x y : ℕ) (hx : x < w) (hy : y < h) :
    (cells.foldl (fun g cell => Grid.put g cell.1.1 cell.1.2 cell.2) g).cells y x
      = lastCellAt w h (g.cells y x) cells x y := by
  induction cells generalizing g with
  | nil => rfl
  | cons cell cells ih =>
      rw [List.foldl_cons, ih]
      unfold lastCellAt
      rw [List.foldl_cons]
      congr 1
      show (Grid.put g cell.1.1 cell.1.2 cell.2).cells y x = _
      unfold Grid.put
      simp only [Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy]
      by_cases hc : cell.1.1 % w = x ∧ cell.1.2 % h = y
      · simp only [hc.1, hc.2, and_self, if_true]
      · have hne : ¬ (x = cell.1.1 % w ∧ y = cell.1.2 % h) := by
          rintro ⟨rfl, rfl⟩; exact hc ⟨rfl, rfl⟩
        simp only [hne, hc, if_false]

/-- Outside the playfield extent, a fold of puts leaves the cell untouched:
    every put lands at a coordinate already reduced modulo the size. -/
theorem foldl_put_cells_out (g : Grid w h) (cells : List ((ℕ × ℕ) × Char))
    (x y : ℕ) (hout : ¬ (x < w ∧ y < h)) (hw : 0 < w) (hh : 0 < h) :
    (cells.foldl (fun g cell => Grid.put g cell.1.1 cell.1.2 cell.2) g).cells y x
      = g.cells y x := by
  induction cells generalizing g with
  | nil => rfl
  | cons cell cells ih =>
      rw [List.foldl_cons, ih]
      show (Grid.put g cell.1.1 cell.1.2 cell.2).cells y x = _
      unfold Grid.put
      have hne : ¬ (x = cell.1.1 % w ∧ y = cell.1.2 % h) := by
        rintro ⟨rfl, rfl⟩
        exact hout ⟨Nat.mod_lt _ hw, Nat.mod_lt _ hh⟩
      simp only [hne, if_false]

/-- The raw cell function of the generated playfield is the last-placed cell,
    at any position inside the playfield. -/
theorem playfieldOf_cells (prog : CMProgram) (x y : ℕ)
    (hx : x < playfieldWidth prog) (hy : y < playfieldHeight prog) :
    (playfieldOf prog).cells y x
      = lastCellAt (playfieldWidth prog) (playfieldHeight prog) ' '
          (playfieldCells prog) x y := by
  rw [show playfieldOf prog
      = (playfieldCells prog).foldl (fun g cell => Grid.put g cell.1.1 cell.1.2 cell.2)
          (Grid.space (playfieldWidth prog) (playfieldHeight prog)) by
        unfold playfieldOf
        exact foldl_bind_put prog (Grid.space (playfieldWidth prog) (playfieldHeight prog))]
  rw [foldl_put_cells _ _ _ _ hx hy]
  rfl

/-- Outside the playfield extent, the generated playfield is all spaces. -/
theorem playfieldOf_cells_out (prog : CMProgram) (x y : ℕ)
    (hout : ¬ (x < playfieldWidth prog ∧ y < playfieldHeight prog))
    (hne : prog ≠ []) :
    (playfieldOf prog).cells y x = ' ' := by
  rw [show playfieldOf prog
      = (playfieldCells prog).foldl (fun g cell => Grid.put g cell.1.1 cell.1.2 cell.2)
          (Grid.space (playfieldWidth prog) (playfieldHeight prog)) by
        unfold playfieldOf
        exact foldl_bind_put prog (Grid.space (playfieldWidth prog) (playfieldHeight prog))]
  rw [foldl_put_cells_out _ _ _ _ hout (playfieldWidth_pos prog hne)
    (playfieldHeight_pos prog hne)]
  rfl

/-- The text form rebuilds the generated playfield, as a grid. -/
theorem ofRows_playfieldRowsOf (prog : CMProgram) (hne : prog ≠ []) :
    Grid.ofRows (playfieldWidth prog) (playfieldHeight prog) (playfieldRowsOf prog)
      = playfieldOf prog := by
  have hcells : ∀ y x,
      (Grid.ofRows (playfieldWidth prog) (playfieldHeight prog)
        (playfieldRowsOf prog)).cells y x = (playfieldOf prog).cells y x := by
    intro y x
    by_cases hy : y < playfieldHeight prog
    · by_cases hx : x < playfieldWidth prog
      · -- both in range: the row map collapses and matches the lookup
        rw [playfieldOf_cells prog x y hx hy]
        change ((playfieldRowsOf prog).getD y []).getD x ' ' = _
        rw [playfieldRowsOf_getD_row prog y hy, List.getD_eq_getElem?_getD]
        simp only [List.getElem?_map, List.getElem?_range, hx, Option.map_some,
          Option.getD_some]
      · -- past the row width: `getD` pads with a space, and no cell is placed
        rw [playfieldOf_cells_out prog x y (by tauto) hne]
        exact playfieldRowsOf_getD_out_width prog x y hx
    · -- past the last row: `getD` yields the empty row, itself padded
      rw [playfieldOf_cells_out prog x y (by tauto) hne]
      change ((playfieldRowsOf prog).getD y []).getD x ' ' = _
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none ?len]
      · rfl
      · rw [List.getD_eq_getElem?_getD,
          List.getElem?_eq_none (by rw [playfieldRowsOf_length]; exact Nat.not_lt.1 hy)]
        simp
  cases hg : playfieldOf prog with
  | mk cg =>
    cases hr : Grid.ofRows (playfieldWidth prog) (playfieldHeight prog)
        (playfieldRowsOf prog) with
    | mk cr =>
      congr 1
      funext y x
      have hyx := hcells y x
      rw [hg, hr] at hyx
      exact hyx

end Completeness

end LeanFunge
