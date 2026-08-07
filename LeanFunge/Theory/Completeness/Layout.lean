/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanFunge.Core.Semantics
import LeanFunge.Theory.Completeness.PairEncoding
import LeanFunge.Theory.Completeness.Routing
import LeanFunge.Theory.Completeness.TwoCounter
import Mathlib.Data.Nat.Notation
import Mathlib.Tactic.Ring

/-!
# The Block Layout Geometry

The layout of a two-counter machine as a playfield: each instruction is a
horizontal block at the intersection of an entry column and a block row.

* A header of one corridor row per block sits above the blocks; block `i`
  occupies the column range `[entryColumn prog i, entryColumn prog (i + 1))`
  and the rows `[blockRow prog i, blockRow prog (i + 1))`, and its jump
  corridor lives on header row `i`.
* The entry `>` of block `i` sits at `(entryColumn prog i, blockRow prog i)`,
  and the fall-through from block `i` drops down column
  `entryColumn prog (i + 1)` to the next block's entry.
* The `decz` branch is one column left of the next entry, so the entry
  columns stay clean for jump drops: no drop passes through a `|`.

This module defines the per-instruction geometry constants and proves the
well-formedness of the layout: the entry columns and block rows are strictly
increasing.

## Main definitions

* `blockWidth`: The column width of an instruction's block.
* `blockHeight`: The row height of an instruction's block.
* `entryColumn`: The entry column of a block.
* `blockRow`: The top row of a block.
* `playfieldWidth`, `playfieldHeight`: The generated playfield dimensions.
* `blockCellList`: The cells of a block, positioned by the layout.
* `corridorCells`: The jump corridor cells for a jump edge.
* `playfieldOf`: Generate the playfield of a program.
* `layoutProgram`: A concrete program for the placement check.

## Theorems

* `blockWidth_pos`: A block is at least one column wide.
* `blockHeight_pos`: A block is at least one row tall.
* `entryColumn_succ`: The entry columns chain by the block widths.
* `blockRow_succ`: The block rows chain by the block heights.
* `entryColumn_strict_mono`: The entry columns are strictly increasing.
* `blockRow_strict_mono`: The block rows are strictly increasing.
* `layout_entry`: The generated playfield places the first entry.
* `layout_decz_branch`: The generated playfield places the branch cell.
* `layout_jog`: The generated playfield places the decrement jog.
* `layout_halt`: The generated playfield places the halt.
-/

namespace LeanFunge

namespace Completeness

/-- The column width of an instruction's block: `inc` occupies three columns
    (data plus the fall-through `v`), `decz` five (data, the branch, and the
    decrement jog), and `jump`/`halt` two. -/
def blockWidth : CMInstr → ℕ
  | .inc _ => 3
  | .decz _ _ => 5
  | .jump _ => 2
  | .halt => 2

/-- The row height of an instruction's block: `decz` needs room for the
    decrement cells and the jog back to the entry column, the others one row
    plus a gap. -/
def blockHeight : CMInstr → ℕ
  | .inc _ => 2
  | .decz _ _ => 5
  | .jump _ => 2
  | .halt => 2

/-- The entry column of block `i`: the sum of the widths of the preceding
    blocks. -/
def entryColumn (prog : CMProgram) : ℕ → ℕ
  | 0 => 0
  | i + 1 => entryColumn prog i + blockWidth (prog.getD i .halt)

/-- The top row of block `i`: the header (one corridor row per block) plus
    the sum of the heights of the preceding blocks. -/
def blockRow (prog : CMProgram) : ℕ → ℕ
  | 0 => prog.length
  | i + 1 => blockRow prog i + blockHeight (prog.getD i .halt)

/-- A block is at least one column wide. -/
theorem blockWidth_pos (instr : CMInstr) : 1 ≤ blockWidth instr := by
  cases instr <;> norm_num [blockWidth]

/-- A block is at least one row tall. -/
theorem blockHeight_pos (instr : CMInstr) : 1 ≤ blockHeight instr := by
  cases instr <;> norm_num [blockHeight]

/-- The entry columns chain by the block widths. -/
theorem entryColumn_succ (prog : CMProgram) (i : ℕ) :
    entryColumn prog (i + 1) = entryColumn prog i + blockWidth (prog.getD i .halt) := by
  rfl

/-- The block rows chain by the block heights. -/
theorem blockRow_succ (prog : CMProgram) (i : ℕ) :
    blockRow prog (i + 1) = blockRow prog i + blockHeight (prog.getD i .halt) := by
  rfl

/-- The entry columns are strictly increasing. -/
theorem entryColumn_strict_mono (prog : CMProgram) {i j : ℕ} (h : i < j) :
    entryColumn prog i < entryColumn prog j := by
  induction j with
  | zero => omega
  | succ j ih =>
      by_cases hij : i < j
      · have h1 : entryColumn prog i < entryColumn prog j := ih hij
        have h2 : entryColumn prog j < entryColumn prog (j + 1) := by
          rw [entryColumn_succ]
          have hw : 1 ≤ blockWidth (prog.getD j .halt) := blockWidth_pos _
          omega
        omega
      · have heq : i = j := by omega
        subst i
        rw [entryColumn_succ]
        have hw : 1 ≤ blockWidth (prog.getD j .halt) := blockWidth_pos _
        omega

/-- The block rows are strictly increasing. -/
theorem blockRow_strict_mono (prog : CMProgram) {i j : ℕ} (h : i < j) :
    blockRow prog i < blockRow prog j := by
  induction j with
  | zero => omega
  | succ j ih =>
      by_cases hij : i < j
      · have h1 : blockRow prog i < blockRow prog j := ih hij
        have h2 : blockRow prog j < blockRow prog (j + 1) := by
          rw [blockRow_succ]
          have hh : 1 ≤ blockHeight (prog.getD j .halt) := blockHeight_pos _
          omega
        omega
      · have heq : i = j := by omega
        subst i
        rw [blockRow_succ]
        have hh : 1 ≤ blockHeight (prog.getD j .halt) := blockHeight_pos _
        omega

/-- The width of the generated playfield: the last entry column. -/
def playfieldWidth (prog : CMProgram) : ℕ :=
  entryColumn prog prog.length

/-- The height of the generated playfield: the last block row. -/
def playfieldHeight (prog : CMProgram) : ℕ :=
  blockRow prog prog.length

/-- The jump corridor of a jump edge: a turn at the source's up column and a
    drop at the target's entry column, on the source's dedicated corridor row
    in the header. -/
def corridorCells (prog : CMProgram) (i k : ℕ) : List ((ℕ × ℕ) × Char) :=
  let D := entryColumn prog i
  let Dk := entryColumn prog k
  let C := D + blockWidth (prog.getD i .halt) - 1
  let turn := if Dk ≥ C then '>' else '<'
  [((C, i), turn), ((Dk, i), 'v')]

/-- The cells of block `i`, positioned by the entry column and block row. -/
def blockCellList (prog : CMProgram) (i : ℕ) : List ((ℕ × ℕ) × Char) :=
  let D := entryColumn prog i
  let y := blockRow prog i
  match prog.getD i .halt with
  | .inc 0 => [((D, y), '>'), ((D + 1, y), '2'), ((D + 2, y), '*'), ((D + 3, y), 'v')]
  | .inc 1 => [((D, y), '>'), ((D + 1, y), '3'), ((D + 2, y), '*'), ((D + 3, y), 'v')]
  | .decz 0 k => [((D, y), '>'), ((D + 1, y), ':'), ((D + 2, y), '2'), ((D + 3, y), '%'),
                 ((D + 4, y), '|'), ((D + 4, y + 1), '2'), ((D + 4, y + 2), '/'),
                 ((D + 4, y + 3), '>'), ((D + 5, y + 3), 'v')] ++ corridorCells prog i k
  | .decz 1 k => [((D, y), '>'), ((D + 1, y), ':'), ((D + 2, y), '3'), ((D + 3, y), '%'),
                 ((D + 4, y), '|'), ((D + 4, y + 1), '3'), ((D + 4, y + 2), '/'),
                 ((D + 4, y + 3), '>'), ((D + 5, y + 3), 'v')] ++ corridorCells prog i k
  | .jump k => [((D, y), '>'), ((D + 1, y), '^')] ++ corridorCells prog i k
  | .halt => [((D, y), '>'), ((D + 1, y), '@')]

/-- Generate the playfield of a program: place every block's cells over the
    all-space grid. -/
def playfieldOf (prog : CMProgram) : Grid (playfieldWidth prog) (playfieldHeight prog) :=
  ((List.range prog.length).foldl
    (fun g i => (blockCellList prog i).foldl
      (fun g cell => Grid.put g cell.1.1 cell.1.2 cell.2) g))
    (Grid.space (playfieldWidth prog) (playfieldHeight prog))

/-- A concrete program for the placement check. -/
def layoutProgram : CMProgram :=
  [.inc 1, .decz 0 3, .inc 0, .halt]

/-- The generated playfield places the first entry. -/
theorem layout_entry : (playfieldOf layoutProgram).get 0 4 = '>' := by
  decide

/-- The generated playfield places the branch cell. -/
theorem layout_decz_branch : (playfieldOf layoutProgram).get 7 6 = '|' := by
  decide

/-- The generated playfield places the decrement jog. -/
theorem layout_jog : (playfieldOf layoutProgram).get 8 9 = 'v' := by
  decide

/-- The generated playfield places the halt. -/
theorem layout_halt : (playfieldOf layoutProgram).get 12 13 = '@' := by
  decide

end Completeness

end LeanFunge
