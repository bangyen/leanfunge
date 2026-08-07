/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanFunge.Theory.Completeness.LayoutCells
import Mathlib.Tactic

/-!
# The Block Row Ranges on the Generated Playfield

Every placed cell sits in a predictable row: a block's body cells lie within its own row range, its corridor cells lie on its header row, and the block row ranges are strictly increasing. These lemmas bound the rows of every cell and are the separation facts behind the cell lookup.

## Main definitions

* (none)

## Theorems

* `blockBodyCells_row_range`: The body cells of a block sit in its row range.
* `corridorCells_row_lt`: The corridor cells of a block sit on its header row.
* `blockRow_ge_length`: Every block row is at or below the header.
* `blockRow_range_le`: The end of a block's row range is at or below a later block's row.
* `getD_option`: The option read reads the same value as the list read.
* `blockCorridorCells_mem`: A corridor cell of a block lies in that block's jump corridor.
* `blockCellList_row_before`: Every cell of a preceding block sits strictly above the block's row.
-/

namespace LeanFunge

namespace Completeness

theorem blockBodyCells_row_range (instr : CMInstr) (D y : ℕ)
    (c : (ℕ × ℕ) × Char) (hc : c ∈ blockBodyCells instr D y) :
    y ≤ c.1.2 ∧ c.1.2 < y + blockHeight instr := by
  cases instr with
  | inc _ =>
      simp only [blockBodyCells, List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with hc | hc | hc | hc <;> subst c <;> simp only [blockHeight, Prod.fst, Prod.snd] <;> omega
  | decz _ _ =>
      simp only [blockBodyCells, List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with hc | hc | hc | hc | hc | hc | hc | hc | hc <;> subst c <;> simp only [blockHeight, Prod.fst, Prod.snd] <;> omega
  | jump _ =>
      simp only [blockBodyCells, List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with hc | hc <;> subst c <;> simp only [blockHeight, Prod.fst, Prod.snd] <;> omega
  | halt =>
      simp only [blockBodyCells, List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with hc | hc <;> subst c <;> simp only [blockHeight, Prod.fst, Prod.snd] <;> omega

/-- The corridor cells of a block sit on its header row. -/
theorem corridorCells_row_lt (prog : CMProgram) (i k : ℕ) (hi : i < prog.length)
    (c : (ℕ × ℕ) × Char) (hc : c ∈ corridorCells prog i k) :
    c.1.2 < prog.length := by
  simp only [corridorCells, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with hc | hc <;> subst c <;> exact hi

/-- Every block row is at or below the header. -/
theorem blockRow_ge_length (prog : CMProgram) (i : ℕ) :
    prog.length ≤ blockRow prog i := by
  by_cases hi : 0 < i
  · exact le_of_lt (blockRow_strict_mono prog hi)
  · have : i = 0 := by omega
    subst i
    rfl

/-- The end of a block's row range is at or below a later block's row. -/
theorem blockRow_range_le (prog : CMProgram) (i j : ℕ) (hij : i < j) :
    blockRow prog i + blockHeight (prog.getD i .halt) ≤ blockRow prog j := by
  have hmono : blockRow prog (i + 1) ≤ blockRow prog j := by
    by_cases h : i + 1 < j
    · exact le_of_lt (blockRow_strict_mono prog h)
    · have h : i + 1 = j := by omega
      rw [h]
  rwa [blockRow_succ] at hmono

/-- The option `getD` reads the same value as `List.getD`. -/
theorem getD_option {α : Type} (l : List α) (i : ℕ) (d : α) :
    (l[i]?).getD d = l.getD i d := by
  rfl

/-- A corridor cell of a block lies in that block's jump corridor. -/
theorem blockCorridorCells_mem (prog : CMProgram) (i : ℕ) (instr : CMInstr)
    (c : (ℕ × ℕ) × Char) (hc : c ∈ blockCorridorCells prog i instr) :
    ∃ k : ℕ, (instr = .decz 0 k ∨ instr = .decz 1 k ∨ instr = .jump k) ∧
      c ∈ corridorCells prog i k := by
  unfold blockCorridorCells at hc
  cases instr with
  | inc _ => cases hc
  | decz c0 k =>
      fin_cases c0
      · exact ⟨k, Or.inl rfl, hc⟩
      · exact ⟨k, Or.inr (Or.inl rfl), hc⟩
  | jump k => exact ⟨k, Or.inr (Or.inr rfl), hc⟩
  | halt => cases hc

/-- Every cell of block `j` sits strictly above block `i`'s row when `j < i`. -/
theorem blockCellList_row_before (prog : CMProgram) (i j : ℕ) (hji : j < i)
    (hi : i < prog.length)
    (c : (ℕ × ℕ) × Char) (hc : c ∈ blockCellList prog j) :
    c.1.2 < blockRow prog i := by
  rw [blockCellList_eq] at hc
  simp only [List.mem_append] at hc
  rcases hc with hc | hc
  · have hrange := blockBodyCells_row_range (prog.getD j .halt) (entryColumn prog j) (blockRow prog j) c hc
    have hle := blockRow_range_le prog j i hji
    omega
  · have hm := blockCorridorCells_mem prog j (prog.getD j .halt) c hc
    rcases hm with ⟨k, hk, hck⟩
    have hcorr := corridorCells_row_lt prog j k (by omega) c hck
    have h0 : prog.length ≤ blockRow prog j := blockRow_ge_length prog j
    have hj : blockRow prog j < blockRow prog i := blockRow_strict_mono prog hji
    omega

end Completeness

end LeanFunge
