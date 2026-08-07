/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanFunge.Theory.Completeness.LayoutCellRange
import Mathlib.Tactic

/-!
# The Cell Lookup of a Block's Row Range

Putting the row-range separation together with the last-cell lookup, any cell within a block's row range reads back exactly the block's body cell: earlier blocks, later blocks, and the header corridors all miss the position.

## Main definitions

* (none)

## Theorems

* `lastCellAt_body`: The body of a block reads back its cell at an offset, within the playfield.
* `lastCellAt_block_after`: A later block does not touch a cell in the block's row range.
* `lastCellAt_flatMap_before`: An earlier block does not touch a cell in the block's row range.
* `lastCellAt_block_i`: The block reads back its body cell at an offset.
* `playfield_block_get`: A cell within a block's row range is the block's body cell.
-/

namespace LeanFunge

namespace Completeness

theorem lastCellAt_body {w h : ℕ} (instr : CMInstr) (D y dx dy : ℕ)
    (hdx : dx ≤ blockWidth instr) (hdy : dy < blockHeight instr)
    (hW : D + blockWidth instr < w) (hH : y + blockHeight instr < h) :
    lastCellAt w h ' ' (blockBodyCells instr D y) (D + dx) (y + dy) = blockBodyAt instr dx dy := by
  have hmodx : ∀ i : ℕ, i ≤ blockWidth instr → (D + i) % w = D + i := by
    intro i hi
    rw [Nat.mod_eq_of_lt]
    omega
  have hmody : ∀ i : ℕ, i < blockHeight instr → (y + i) % h = y + i := by
    intro i hi
    rw [Nat.mod_eq_of_lt]
    omega
  have hdxm : (D + dx) % w = D + dx := by
    rw [Nat.mod_eq_of_lt]
    omega
  have hdym : (y + dy) % h = y + dy := by
    rw [Nat.mod_eq_of_lt]
    omega
  have h0y : y % h = y := by
    rw [Nat.mod_eq_of_lt]
    omega
  have hD : D % w = D := by
    rw [Nat.mod_eq_of_lt]
    omega
  cases instr with
  | inc c0 =>
      fin_cases c0
      · simp only [blockWidth, blockHeight] at hdx hdy
        interval_cases dx <;> interval_cases dy <;> simp [blockBodyCells, blockBodyAt, lastCellAt, -- no_squeeze
            blockWidth, blockHeight, hmodx, hmody, hdxm, hdym, h0y, hD]
      · simp only [blockWidth, blockHeight] at hdx hdy
        interval_cases dx <;> interval_cases dy <;> simp [blockBodyCells, blockBodyAt, lastCellAt, -- no_squeeze
            blockWidth, blockHeight, hmodx, hmody, hdxm, hdym, h0y, hD]
  | decz c0 _ =>
      fin_cases c0
      · simp only [blockWidth, blockHeight] at hdx hdy
        interval_cases dx <;> interval_cases dy <;> simp [blockBodyCells, blockBodyAt, lastCellAt, -- no_squeeze
            blockWidth, blockHeight, hmodx, hmody, hdxm, hdym, h0y, hD]
      · simp only [blockWidth, blockHeight] at hdx hdy
        interval_cases dx <;> interval_cases dy <;> simp [blockBodyCells, blockBodyAt, lastCellAt, -- no_squeeze
            blockWidth, blockHeight, hmodx, hmody, hdxm, hdym, h0y, hD]
  | jump _ =>
      simp only [blockWidth, blockHeight] at hdx hdy
      interval_cases dx <;> interval_cases dy <;> simp [blockBodyCells, blockBodyAt, lastCellAt, -- no_squeeze
          blockWidth, blockHeight, hmodx, hmody, hdxm, hdym, h0y, hD]
  | halt =>
      simp only [blockWidth, blockHeight] at hdx hdy
      interval_cases dx <;> interval_cases dy <;> simp [blockBodyCells, blockBodyAt, lastCellAt, -- no_squeeze
          blockWidth, blockHeight, hmodx, hmody, hdxm, hdym, h0y, hD]

/-- A block after `i` does not touch a cell in block `i`'s row range. -/
theorem lastCellAt_block_after (prog : CMProgram) (i j dx dy : ℕ) (hij : i < j)
    (hj : j < prog.length) (hdy : dy < blockHeight (prog.getD i .halt))
    (hH : blockRow prog i + dy < playfieldHeight prog) (init : Char) :
    lastCellAt (playfieldWidth prog) (playfieldHeight prog) init (blockCellList prog j)
      (entryColumn prog i + dx) (blockRow prog i + dy) = init := by
  apply lastCellAt_skip_row (w := playfieldWidth prog) (h := playfieldHeight prog) init
    (blockCellList prog j) (entryColumn prog i + dx) (blockRow prog i + dy) hH
  · intro c hc
    rw [blockCellList_eq] at hc
    simp only [List.mem_append] at hc
    rcases hc with hc | hc
    · have hrange := blockBodyCells_row_range (prog.getD j .halt) (entryColumn prog j) (blockRow prog j) c hc
      have hle : blockRow prog j + blockHeight (prog.getD j .halt) ≤ playfieldHeight prog := by
        rw [playfieldHeight]
        exact blockRow_range_le prog j prog.length hj
      omega
    · rcases blockCorridorCells_mem prog j (prog.getD j .halt) c hc with ⟨k, hk, hck⟩
      have hcorr := corridorCells_row_lt prog j k (by omega) c hck
      have hn : prog.length ≤ playfieldHeight prog := by
        rw [playfieldHeight]
        exact blockRow_ge_length prog prog.length
      omega
  · intro c hc
    rw [blockCellList_eq] at hc
    simp only [List.mem_append] at hc
    rcases hc with hc | hc
    · have hrange := blockBodyCells_row_range (prog.getD j .halt) (entryColumn prog j) (blockRow prog j) c hc
      have hle := blockRow_range_le prog i j hij
      omega
    · rcases blockCorridorCells_mem prog j (prog.getD j .halt) c hc with ⟨k, hk, hck⟩
      have hcorr := corridorCells_row_lt prog j k (by omega) c hck
      have hge := blockRow_ge_length prog i
      omega

/-- A block before `i` does not touch a cell in block `i`'s row range. -/
theorem lastCellAt_flatMap_before (prog : CMProgram) (i : ℕ) (hi : i < prog.length)
    (dx dy : ℕ) (hH : blockRow prog i + dy < playfieldHeight prog) :
    lastCellAt (playfieldWidth prog) (playfieldHeight prog) ' '
      (List.flatMap (fun j => blockCellList prog j) (List.range i))
      (entryColumn prog i + dx) (blockRow prog i + dy) = ' ' := by
  apply lastCellAt_skip_row (w := playfieldWidth prog) (h := playfieldHeight prog) ' '
    (List.flatMap (fun j => blockCellList prog j) (List.range i))
    (entryColumn prog i + dx) (blockRow prog i + dy) hH
  · intro c hc
    rcases (List.mem_flatMap.mp hc) with ⟨j, hj, hcj⟩
    have hjlt : j < i := List.mem_range.mp hj
    have hb := blockCellList_row_before prog i j hjlt hi c hcj
    have hyl : blockRow prog i < playfieldHeight prog := by
      rw [playfieldHeight]
      exact blockRow_strict_mono prog hi
    omega
  · intro c hc
    rcases (List.mem_flatMap.mp hc) with ⟨j, hj, hcj⟩
    have hjlt : j < i := List.mem_range.mp hj
    have hb := blockCellList_row_before prog i j hjlt hi c hcj
    omega

/-- Block `i` reads back its body cell at an offset. -/
theorem lastCellAt_block_i (prog : CMProgram) (i : ℕ) (hi : i < prog.length)
    (dx dy : ℕ) (hdx : dx ≤ blockWidth (prog.getD i .halt))
    (hdy : dy < blockHeight (prog.getD i .halt))
    (hW : entryColumn prog i + blockWidth (prog.getD i .halt) < playfieldWidth prog)
    (hH0 : blockRow prog i + blockHeight (prog.getD i .halt) < playfieldHeight prog)
    (hH : blockRow prog i + dy < playfieldHeight prog) :
    lastCellAt (playfieldWidth prog) (playfieldHeight prog) ' ' (blockCellList prog i)
      (entryColumn prog i + dx) (blockRow prog i + dy)
      = blockBodyAt (prog.getD i .halt) dx dy := by
  rw [blockCellList_eq]
  rw [lastCellAt_append]
  rw [lastCellAt_body (prog.getD i .halt) (entryColumn prog i) (blockRow prog i) dx dy hdx hdy hW hH0]
  have hskip : lastCellAt (playfieldWidth prog) (playfieldHeight prog) (blockBodyAt (prog.getD i .halt) dx dy)
      (blockCorridorCells prog i (prog.getD i .halt)) (entryColumn prog i + dx) (blockRow prog i + dy)
      = blockBodyAt (prog.getD i .halt) dx dy := by
    apply lastCellAt_skip_row (w := playfieldWidth prog) (h := playfieldHeight prog)
      (blockBodyAt (prog.getD i .halt) dx dy) (blockCorridorCells prog i (prog.getD i .halt))
      (entryColumn prog i + dx) (blockRow prog i + dy) hH
    · intro c hc
      rcases blockCorridorCells_mem prog i (prog.getD i .halt) c hc with ⟨k, hk, hck⟩
      have hcorr := corridorCells_row_lt prog i k hi c hck
      have hn : prog.length ≤ playfieldHeight prog := by
        rw [playfieldHeight]
        exact blockRow_ge_length prog prog.length
      omega
    · intro c hc
      rcases blockCorridorCells_mem prog i (prog.getD i .halt) c hc with ⟨k, hk, hck⟩
      have hcorr := corridorCells_row_lt prog i k hi c hck
      have hge : prog.length ≤ blockRow prog i := blockRow_ge_length prog i
      omega
  rw [hskip]

/-- A cell within a block's row range is the block's body cell. -/
theorem playfield_block_get (prog : CMProgram) (i : ℕ) (hi1 : i + 1 < prog.length)
    (dx dy : ℕ) (hdx : dx ≤ blockWidth (prog.getD i .halt))
    (hdy : dy < blockHeight (prog.getD i .halt)) :
    (playfieldOf prog).get (entryColumn prog i + dx) (blockRow prog i + dy)
      = blockBodyAt (prog.getD i .halt) dx dy := by
  let pw := playfieldWidth prog
  let ph := playfieldHeight prog
  have hW : entryColumn prog i + blockWidth (prog.getD i .halt) < playfieldWidth prog := by
    rw [playfieldWidth]
    rw [← entryColumn_succ]
    exact entryColumn_strict_mono prog hi1
  have hx : entryColumn prog i + dx < playfieldWidth prog := by
    omega
  have hH0 : blockRow prog i + blockHeight (prog.getD i .halt) < playfieldHeight prog := by
    rw [playfieldHeight]
    rw [← blockRow_succ]
    exact blockRow_strict_mono prog hi1
  have hH : blockRow prog i + dy < playfieldHeight prog := by
    omega
  rw [playfieldOf_get_eq_lastCellAt]
  unfold playfieldCells
  have hmain : ∀ k : ℕ, i < k → k ≤ prog.length →
      lastCellAt pw ph ' ' (List.flatMap (fun j => blockCellList prog j) (List.range k))
        (entryColumn prog i + dx) (blockRow prog i + dy)
        = blockBodyAt (prog.getD i .halt) dx dy := by
    intro k hik hkn
    induction k with
    | zero => omega
    | succ k ih =>
        by_cases hik' : i < k
        · have hprev := ih hik' (by omega)
          rw [flatMap_range_succ, lastCellAt_append, hprev]
          exact lastCellAt_block_after prog i k dx dy (by omega) (by omega) hdy hH
              (blockBodyAt (prog.getD i .halt) dx dy)
        · have heq : i = k := by omega
          subst i
          rw [flatMap_range_succ, lastCellAt_append]
          rw [lastCellAt_flatMap_before prog k (by omega) dx dy hH]
          exact lastCellAt_block_i prog k (by omega) dx dy hdx hdy hW hH0 hH
  have hres := hmain prog.length (by omega) (by rfl)
  rw [hres]

end Completeness

end LeanFunge
