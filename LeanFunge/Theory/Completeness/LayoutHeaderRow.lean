/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanFunge.Theory.Completeness.LayoutCellRange
import LeanFunge.Theory.Completeness.LayoutCells
import Mathlib.Tactic

/-!
# Other Blocks Do Not Touch a Header Cell

The only cells on a header row are a block's corridor turn and drop. This module proves that every other block misses a header cell: a block other than `y` places no cell on row `y`, so the header readback skips it.

## Theorems

* `blockCellList_row_ne_header`: Every cell of a block other than `y` has a row other than `y`.
* `lastCellAt_block_after_header`: A later block does not touch a header cell.
* `lastCellAt_flatMap_before_header`: An earlier block does not touch a header cell.
-/

namespace LeanFunge

namespace Completeness

/-- Every cell of a block other than `y` has a row other than `y`. -/
theorem blockCellList_row_ne_header (prog : CMProgram) (j y : ℕ) (hjy : j ≠ y) (hy : y < prog.length)
    (c : (ℕ × ℕ) × Char) (hc : c ∈ blockCellList prog j) :
    c.1.2 ≠ y := by
  rw [blockCellList_eq] at hc
  simp only [List.mem_append] at hc
  rcases hc with hc | hc
  · have hrange := blockBodyCells_row_range (prog.getD j .halt) (entryColumn prog j) (blockRow prog j) c hc
    have hge := blockRow_ge_length prog j
    omega
  · rcases blockCorridorCells_mem prog j (prog.getD j .halt) c hc with ⟨k, hk, hck⟩
    simp only [corridorCells, List.mem_cons, List.not_mem_nil, or_false] at hck
    rcases hck with hck | hck <;> simp [hck] <;> omega -- no_squeeze: header row skip

/-- A later block does not touch a header cell. -/
theorem lastCellAt_block_after_header (prog : CMProgram) (y k x : ℕ) (hyk : y < k)
    (hk : k < prog.length) (hy : y < prog.length) (hH : y < playfieldHeight prog) (init : Char) :
    lastCellAt (playfieldWidth prog) (playfieldHeight prog) init (blockCellList prog k) x y = init := by
  apply lastCellAt_skip_row (w := playfieldWidth prog) (h := playfieldHeight prog) init (blockCellList prog k) x y hH
  · intro c hc
    rw [blockCellList_eq] at hc
    simp only [List.mem_append] at hc
    rcases hc with hc | hc
    · have hrange := blockBodyCells_row_range (prog.getD k .halt) (entryColumn prog k) (blockRow prog k) c hc
      have hle : blockRow prog k + blockHeight (prog.getD k .halt) ≤ playfieldHeight prog := by
        rw [playfieldHeight]
        exact blockRow_range_le prog k prog.length hk
      omega
    · rcases blockCorridorCells_mem prog k (prog.getD k .halt) c hc with ⟨j, hj, hck⟩
      have hcorr := corridorCells_row_lt prog k j hk c hck
      have hn : prog.length ≤ playfieldHeight prog := by
        rw [playfieldHeight]
        exact blockRow_ge_length prog prog.length
      omega
  · intro c hc
    exact blockCellList_row_ne_header (prog := prog) (j := k) (y := y) (hjy := by omega) (hy := hy) c hc

/-- An earlier block does not touch a header cell. -/
theorem lastCellAt_flatMap_before_header (prog : CMProgram) (y x : ℕ) (hy : y < prog.length)
    (hH : y < playfieldHeight prog) :
    lastCellAt (playfieldWidth prog) (playfieldHeight prog) ' '
      (List.flatMap (fun j => blockCellList prog j) (List.range y)) x y = ' ' := by
  apply lastCellAt_skip_row (w := playfieldWidth prog) (h := playfieldHeight prog) ' '
    (List.flatMap (fun j => blockCellList prog j) (List.range y)) x y hH
  · intro c hc
    rcases (List.mem_flatMap.mp hc) with ⟨j, hj, hcj⟩
    have hjlt : j < y := List.mem_range.mp hj
    rw [blockCellList_eq] at hcj
    simp only [List.mem_append] at hcj
    rcases hcj with hcj | hcj
    · have hrange := blockBodyCells_row_range (prog.getD j .halt) (entryColumn prog j) (blockRow prog j) c hcj
      have hle : blockRow prog j + blockHeight (prog.getD j .halt) ≤ playfieldHeight prog := by
        rw [playfieldHeight]
        exact blockRow_range_le prog j prog.length (by omega)
      omega
    · rcases blockCorridorCells_mem prog j (prog.getD j .halt) c hcj with ⟨k, hk, hck⟩
      have hcorr := corridorCells_row_lt prog j k (by omega) c hck
      have hn : prog.length ≤ playfieldHeight prog := by
        rw [playfieldHeight]
        exact blockRow_ge_length prog prog.length
      omega
  · intro c hc
    rcases (List.mem_flatMap.mp hc) with ⟨j, hj, hcj⟩
    have hjlt : j < y := List.mem_range.mp hj
    exact blockCellList_row_ne_header (prog := prog) (j := j) (y := y)
      (hjy := by omega) (hy := hy) (c := c) (hc := hcj)

end Completeness

end LeanFunge
