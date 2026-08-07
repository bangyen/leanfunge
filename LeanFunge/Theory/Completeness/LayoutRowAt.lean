/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanFunge.Theory.Completeness.LayoutCorridor
import LeanFunge.Theory.Completeness.LayoutCellMain
import LeanFunge.Theory.Completeness.LayoutCellRange
import Mathlib.Tactic

/-!
# The Block Lookup at Any Column

The generated playfield reads back a block's body cell at any column offset: within the body it is the body cell, and beyond the block's width it is a space. These lemmas generalize the cell lookup beyond a block's column span, which the corridor routing uses to show that path cells are spaces.

## Main definitions

* (none)

## Theorems

* `lastCellAt_body_out`: A body readback beyond the block's width is a space.
* `lastCellAt_body_any`: A body readback at any column is the body cell or a space.
* `lastCellAt_block_i_any`: Block `i` reads back its body cell at any column offset.
* `playfield_row_at`: A cell in a block's row range is the block's body cell, at any column.
-/

namespace LeanFunge

namespace Completeness

/-- A body readback beyond the block's width is a space. -/
theorem lastCellAt_body_out {w h : ℕ} (instr : CMInstr) (D y dx dy : ℕ)
    (hout : blockWidth instr < dx) (hdy : dy < blockHeight instr)
    (hW : D + blockWidth instr < w) (hH : y + blockHeight instr < h)
    (hx : D + dx < w) (hy : y + dy < h) :
    lastCellAt w h ' ' (blockBodyCells instr D y) (D + dx) (y + dy) = ' ' := by
  cases instr with
  | inc c0 =>
      fin_cases c0 <;> (simp only [blockWidth] at hW hout; simp only [blockHeight] at hH hdy)
      <;> (have hD : D % w = D := by rw [Nat.mod_eq_of_lt]; omega
           have hD0 : (D + 0) % w = D + 0 := by rw [Nat.mod_eq_of_lt]; omega
           have hD1 : (D + 1) % w = D + 1 := by rw [Nat.mod_eq_of_lt]; omega
           have hD2 : (D + 2) % w = D + 2 := by rw [Nat.mod_eq_of_lt]; omega
           have hD3 : (D + 3) % w = D + 3 := by rw [Nat.mod_eq_of_lt]; omega
           have hDx : (D + dx) % w = D + dx := by rw [Nat.mod_eq_of_lt]; omega
           have hy' : y % h = y := by rw [Nat.mod_eq_of_lt]; omega
           have hY0 : (y + 0) % h = y + 0 := by rw [Nat.mod_eq_of_lt]; omega
           have hYq : (y + dy) % h = y + dy := by rw [Nat.mod_eq_of_lt]; omega
           simp only [lastCellAt, blockBodyCells, List.foldl_cons, List.foldl_nil,
             hD, hD0, hD1, hD2, hD3, hDx, hy', hY0, hYq, add_left_cancel_iff]
           split_ifs <;> first | rfl | omega)
  | decz c0 _ =>
      fin_cases c0 <;> (simp only [blockWidth] at hW hout; simp only [blockHeight] at hH hdy)
      <;> (have hD : D % w = D := by rw [Nat.mod_eq_of_lt]; omega
           have hD0 : (D + 0) % w = D + 0 := by rw [Nat.mod_eq_of_lt]; omega
           have hD1 : (D + 1) % w = D + 1 := by rw [Nat.mod_eq_of_lt]; omega
           have hD2 : (D + 2) % w = D + 2 := by rw [Nat.mod_eq_of_lt]; omega
           have hD3 : (D + 3) % w = D + 3 := by rw [Nat.mod_eq_of_lt]; omega
           have hD4 : (D + 4) % w = D + 4 := by rw [Nat.mod_eq_of_lt]; omega
           have hD5 : (D + 5) % w = D + 5 := by rw [Nat.mod_eq_of_lt]; omega
           have hDx : (D + dx) % w = D + dx := by rw [Nat.mod_eq_of_lt]; omega
           have hy' : y % h = y := by rw [Nat.mod_eq_of_lt]; omega
           have hY0 : (y + 0) % h = y + 0 := by rw [Nat.mod_eq_of_lt]; omega
           have hY1 : (y + 1) % h = y + 1 := by rw [Nat.mod_eq_of_lt]; omega
           have hY2 : (y + 2) % h = y + 2 := by rw [Nat.mod_eq_of_lt]; omega
           have hY3 : (y + 3) % h = y + 3 := by rw [Nat.mod_eq_of_lt]; omega
           have hYq : (y + dy) % h = y + dy := by rw [Nat.mod_eq_of_lt]; omega
           simp only [lastCellAt, blockBodyCells, List.foldl_cons, List.foldl_nil,
             hD, hD0, hD1, hD2, hD3, hD4, hD5, hDx, hy', hY0, hY1, hY2, hY3, hYq, add_left_cancel_iff]
           split_ifs <;> first | rfl | omega)
  | jump _ =>
      simp only [blockWidth] at hW hout
      simp only [blockHeight] at hH hdy
      have hD : D % w = D := by rw [Nat.mod_eq_of_lt]; omega
      have hD0 : (D + 0) % w = D + 0 := by rw [Nat.mod_eq_of_lt]; omega
      have hD1 : (D + 1) % w = D + 1 := by rw [Nat.mod_eq_of_lt]; omega
      have hDx : (D + dx) % w = D + dx := by rw [Nat.mod_eq_of_lt]; omega
      have hy' : y % h = y := by rw [Nat.mod_eq_of_lt]; omega
      have hY0 : (y + 0) % h = y + 0 := by rw [Nat.mod_eq_of_lt]; omega
      have hYq : (y + dy) % h = y + dy := by rw [Nat.mod_eq_of_lt]; omega
      simp only [lastCellAt, blockBodyCells, List.foldl_cons, List.foldl_nil,
        hD, hD0, hD1, hDx, hy', hY0, hYq, add_left_cancel_iff]
      split_ifs <;> first | rfl | omega
  | halt =>
      simp only [blockWidth] at hW hout
      simp only [blockHeight] at hH hdy
      have hD : D % w = D := by rw [Nat.mod_eq_of_lt]; omega
      have hD0 : (D + 0) % w = D + 0 := by rw [Nat.mod_eq_of_lt]; omega
      have hD1 : (D + 1) % w = D + 1 := by rw [Nat.mod_eq_of_lt]; omega
      have hDx : (D + dx) % w = D + dx := by rw [Nat.mod_eq_of_lt]; omega
      have hy' : y % h = y := by rw [Nat.mod_eq_of_lt]; omega
      have hY0 : (y + 0) % h = y + 0 := by rw [Nat.mod_eq_of_lt]; omega
      have hYq : (y + dy) % h = y + dy := by rw [Nat.mod_eq_of_lt]; omega
      simp only [lastCellAt, blockBodyCells, List.foldl_cons, List.foldl_nil,
        hD, hD0, hD1, hDx, hy', hY0, hYq, add_left_cancel_iff]
      split_ifs <;> first | rfl | omega

/-- A body readback at any column is the body cell or a space. -/
theorem lastCellAt_body_any {w h : ℕ} (instr : CMInstr) (D y dx dy : ℕ)
    (hdy : dy < blockHeight instr)
    (hW : D + blockWidth instr < w) (hH : y + blockHeight instr < h)
    (hx : D + dx < w) (hy : y + dy < h) :
    lastCellAt w h ' ' (blockBodyCells instr D y) (D + dx) (y + dy) = blockBodyAt instr dx dy := by
  by_cases hle : dx ≤ blockWidth instr
  · exact lastCellAt_body instr D y dx dy hle hdy hW hH
  · have hout : blockWidth instr < dx := by omega
    rw [blockBodyAt_out instr dx dy hout]
    exact lastCellAt_body_out instr D y dx dy hout hdy hW hH hx hy

/-- Block `i` reads back its body cell at any column offset. -/
theorem lastCellAt_block_i_any (prog : CMProgram) (i : ℕ) (hi : i < prog.length)
    (dx dy : ℕ) (hdy : dy < blockHeight (prog.getD i .halt))
    (hW : entryColumn prog i + blockWidth (prog.getD i .halt) < playfieldWidth prog)
    (hH0 : blockRow prog i + blockHeight (prog.getD i .halt) < playfieldHeight prog)
    (hx : entryColumn prog i + dx < playfieldWidth prog)
    (hH : blockRow prog i + dy < playfieldHeight prog) :
    lastCellAt (playfieldWidth prog) (playfieldHeight prog) ' ' (blockCellList prog i)
      (entryColumn prog i + dx) (blockRow prog i + dy)
      = blockBodyAt (prog.getD i .halt) dx dy := by
  rw [blockCellList_eq]
  rw [lastCellAt_append]
  rw [lastCellAt_body_any (prog.getD i .halt) (entryColumn prog i) (blockRow prog i) dx dy hdy hW hH0 hx hH]
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

/-- A cell in a block's row range is the block's body cell, at any column. -/
theorem playfield_row_at (prog : CMProgram) (i : ℕ) (hi1 : i + 1 < prog.length)
    (dx dy : ℕ) (hdy : dy < blockHeight (prog.getD i .halt))
    (hx : entryColumn prog i + dx < playfieldWidth prog) :
    (playfieldOf prog).get (entryColumn prog i + dx) (blockRow prog i + dy)
      = blockBodyAt (prog.getD i .halt) dx dy := by
  let pw := playfieldWidth prog
  let ph := playfieldHeight prog
  have hW : entryColumn prog i + blockWidth (prog.getD i .halt) < playfieldWidth prog := by
    rw [playfieldWidth]
    rw [← entryColumn_succ]
    exact entryColumn_strict_mono prog hi1
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
          exact lastCellAt_block_i_any prog k (by omega) dx dy hdy hW hH0 hx hH
  have hres := hmain prog.length (by omega) (by rfl)
  rw [hres]

end Completeness

end LeanFunge
