/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanFunge.Theory.Completeness.Layout
import LeanFunge.Theory.Completeness.Routing
import LeanFunge.Theory.Run.Relational
import LeanFunge.Theory.Step
import Mathlib.Tactic
/-!
# The Generated Playfield Cell Lookup

The generated playfield places exactly the block bodies and the jump corridors. This
module defines the placed cells and the last-cell lookup over them: a run of puts reads
back the last placed cell, and the playfield readback equals the lookup over the
flattened placed cells.

Every placed cell sits in a predictable row: a block's body cells lie within its own
row range, its corridor cells lie on its header row, and the block row ranges are
strictly increasing. These lemmas bound the rows of every cell and are the separation
facts behind the cell lookup.

Putting the row-range separation together with the last-cell lookup, any cell within a
block's row range reads back exactly the block's body cell: earlier blocks, later
blocks, and the header corridors all miss the position.

## Definitions

* `blockBodyCells`: The cells of a block's body, positioned.

* `blockBodyAt`: The block body cell at an offset, or a space.

* `blockCorridorCells`: The corridor cells of a block's jump edge, or none.

* `playfieldCells`: The flattened list of all placed cells, in fold order.

* `lastCellAt`: The value of the last placed cell at a position, or the initial value.

* (none)

## Theorems

* `blockCellList_eq`: The block cell list splits into the body and the corridor.

* `put_get`: A put reads back its cell and leaves other cells unchanged.

* `foldl_bind_put`: Folding the blocks one at a time equals folding the flattened cells.

* `foldl_put_get`: A run of puts reads back the last placed cell.

* `playfieldOf_get_eq_lastCellAt`: The playfield readback equals the last cell lookup
  over the flattened cells.

* `lastCellAt_skip_row`: A run of cells whose rows miss the lookup row does not change the lookup.

* `lastCellAt_append`: The lookup over a concatenation composes the accumulators.

* `flatMap_range_succ`: A flat map over a successor range splits off the last block.

* `blockBodyCells_row_range`: The body cells of a block sit in its row range.

* `corridorCells_row_lt`: The corridor cells of a block sit on its header row.

* `blockRow_ge_length`: Every block row is at or below the header.

* `blockRow_range_le`: The end of a block's row range is at or below a later block's row.

* `getD_option`: The option read reads the same value as the list read.

* `blockCorridorCells_mem`: A corridor cell of a block lies in that block's jump corridor.

* `blockCellList_row_before`: Every cell of a preceding block sits strictly above the block's row.

* `lastCellAt_body`: The body of a block reads back its cell at an offset, within the playfield.

* `lastCellAt_block_after`: A later block does not touch a cell in the block's row range.

* `lastCellAt_flatMap_before`: An earlier block does not touch a cell in the block's row range.

* `lastCellAt_block_i`: The block reads back its body cell at an offset.

* `playfield_block_get`: A cell within a block's row range is the block's body cell.

-/
namespace LeanFunge

namespace Completeness

/-- The cells of a block's body, positioned by the entry column and row. -/
def blockBodyCells (instr : CMInstr) (D y : ℕ) : List ((ℕ × ℕ) × Char) :=
  match instr with
  | .inc c => [((D, y), '>'), ((D + 1, y), counterDigit c), ((D + 2, y), '*'), ((D + 3, y), 'v')]
  | .decz c _ => [((D, y), '>'), ((D + 1, y), ':'), ((D + 2, y), counterDigit c), ((D + 3, y), '%'),
                 ((D + 4, y), '|'), ((D + 4, y + 1), counterDigit c), ((D + 4, y + 2), '/'),
                 ((D + 4, y + 3), '>'), ((D + 5, y + 3), 'v')]
  | .jump _ => [((D, y), '>'), ((D + 1, y), '^')]
  | .halt => [((D, y), '>'), ((D + 1, y), '@')]

/-- The block body cell at an offset, or a space. -/
def blockBodyAt (instr : CMInstr) (dx dy : ℕ) : Char :=
  match instr with
  | .inc c =>
      if dx = 0 ∧ dy = 0 then '>' else
      if dx = 1 ∧ dy = 0 then counterDigit c else
      if dx = 2 ∧ dy = 0 then '*' else
      if dx = 3 ∧ dy = 0 then 'v' else ' '
  | .decz c _ =>
      if dx = 0 ∧ dy = 0 then '>' else
      if dx = 1 ∧ dy = 0 then ':' else
      if dx = 2 ∧ dy = 0 then counterDigit c else
      if dx = 3 ∧ dy = 0 then '%' else
      if dx = 4 ∧ dy = 0 then '|' else
      if dx = 4 ∧ dy = 1 then counterDigit c else
      if dx = 4 ∧ dy = 2 then '/' else
      if dx = 4 ∧ dy = 3 then '>' else
      if dx = 5 ∧ dy = 3 then 'v' else ' '
  | .jump _ =>
      if dx = 0 ∧ dy = 0 then '>' else
      if dx = 1 ∧ dy = 0 then '^' else ' '
  | .halt =>
      if dx = 0 ∧ dy = 0 then '>' else
      if dx = 1 ∧ dy = 0 then '@' else ' '

/-- The corridor cells of block `i`'s jump edge, or none. -/
def blockCorridorCells (prog : CMProgram) (i : ℕ) (instr : CMInstr) : List ((ℕ × ℕ) × Char) :=
  match instr with
  | .decz _ k => corridorCells prog i k
  | .jump k => corridorCells prog i k
  | _ => []

/-- `blockCellList` splits into the body and the corridor. -/
theorem blockCellList_eq (prog : CMProgram) (i : ℕ) :
    blockCellList prog i
      = blockBodyCells (prog.getD i .halt) (entryColumn prog i) (blockRow prog i)
        ++ blockCorridorCells prog i (prog.getD i .halt) := by
  unfold blockCellList
  cases prog.getD i .halt <;> rfl

/-- The flattened list of all placed cells, in fold order. -/
def playfieldCells (prog : CMProgram) : List ((ℕ × ℕ) × Char) :=
  List.flatMap (fun i => blockCellList prog i) (List.range prog.length)

/-- The value of the last placed cell at a position, or the initial value. -/
def lastCellAt (w h : ℕ) (init : Char) (cells : List ((ℕ × ℕ) × Char)) (x y : ℕ) : Char :=
  cells.foldl
    (fun acc cell => if cell.1.1 % w = x % w ∧ cell.1.2 % h = y % h then cell.2 else acc)
    init

/-- A put reads back its cell and leaves other cells unchanged. -/
theorem Grid.put_get (g : Grid w h) (px py x y : ℕ) (c : Char) :
    (Grid.put g px py c).get x y = if px % w = x % w ∧ py % h = y % h then c else g.get x y := by
  unfold Grid.put Grid.get
  by_cases h : px % w = x % w ∧ py % h = y % h
  · simp only [h]
  · simp only [h, eq_comm, if_false]

/-- Folding the blocks one at a time equals folding the flattened cells. -/
theorem foldl_bind_put (prog : CMProgram)
    (g0 : Grid (playfieldWidth prog) (playfieldHeight prog)) :
    (List.range prog.length).foldl
        (fun g i =>
          (blockCellList prog i).foldl (fun g cell => Grid.put g cell.1.1 cell.1.2 cell.2) g)
        g0
      = (playfieldCells prog).foldl (fun g cell => Grid.put g cell.1.1 cell.1.2 cell.2) g0 := by
  unfold playfieldCells
  induction List.range prog.length generalizing g0 with
  | nil => rfl
  | cons x xs ih =>
      rw [List.foldl_cons]
      rw [List.flatMap_cons, List.foldl_append]
      exact ih ((blockCellList prog x).foldl (fun g cell => Grid.put g cell.1.1 cell.1.2 cell.2) g0)

/-- A run of puts reads back the last placed cell. -/
theorem foldl_put_get (g : Grid w h) (cells : List ((ℕ × ℕ) × Char)) (x y : ℕ) :
    (cells.foldl (fun g cell => Grid.put g cell.1.1 cell.1.2 cell.2) g).get x y
      = lastCellAt w h (g.get x y) cells x y := by
  induction cells generalizing g with
  | nil => rfl
  | cons cell cells ih =>
      rw [List.foldl_cons]
      rw [ih]
      unfold lastCellAt
      rw [List.foldl_cons]
      congr
      rw [Grid.put_get]

/-- The playfield readback equals the last-cell lookup over the flattened
    cells. -/
theorem playfieldOf_get_eq_lastCellAt (prog : CMProgram) (x y : ℕ) :
    (playfieldOf prog).get x y
      = lastCellAt (playfieldWidth prog) (playfieldHeight prog) ' ' (playfieldCells prog) x y := by
  rw [show playfieldOf prog
      = (playfieldCells prog).foldl (fun g cell => Grid.put g cell.1.1 cell.1.2 cell.2)
          (Grid.space (playfieldWidth prog) (playfieldHeight prog)) by
        unfold playfieldOf
        exact foldl_bind_put prog (Grid.space (playfieldWidth prog) (playfieldHeight prog))]
  rw [foldl_put_get]
  rfl

/-- A cell whose row misses the lookup row does not change the lookup. -/
theorem lastCellAt_skip_row (w h : ℕ) (init : Char) (cells : List ((ℕ × ℕ) × Char))
    (x y : ℕ) (hy : y < h)
    (hrow : ∀ c : (ℕ × ℕ) × Char, c ∈ cells → c.1.2 < h)
    (hdiff : ∀ c : (ℕ × ℕ) × Char, c ∈ cells → c.1.2 ≠ y) :
    lastCellAt w h init cells x y = init := by
  induction cells generalizing init with
  | nil => rfl
  | cons cell cells ih =>
      unfold lastCellAt
      rw [List.foldl_cons]
      have hnot : ¬(cell.1.1 % w = x % w ∧ cell.1.2 % h = y % h) := by
        intro hm
        have hy' : cell.1.2 % h = y % h := hm.2
        have hrowc : cell.1.2 < h := hrow cell (by exact List.mem_cons_self)
        have hmod : cell.1.2 % h = cell.1.2 := Nat.mod_eq_of_lt hrowc
        rw [hmod] at hy'
        rw [Nat.mod_eq_of_lt hy] at hy'
        exact hdiff cell (by exact List.mem_cons_self) hy'
      simp only [hnot, if_false]
      exact ih init (by intro c hc; exact hrow c (by exact List.mem_cons.mpr (Or.inr hc)))
                     (by intro c hc; exact hdiff c (by exact List.mem_cons.mpr (Or.inr hc)))

theorem lastCellAt_append (w h : ℕ) (init : Char) (l1 l2 : List ((ℕ × ℕ) × Char)) (x y : ℕ) :
    lastCellAt w h init (l1 ++ l2) x y = lastCellAt w h (lastCellAt w h init l1 x y) l2 x y := by
  simp only [lastCellAt, List.foldl_append]

/-- `flatMap` over a successor range splits off the last block. -/
theorem flatMap_range_succ {β : Type} (f : ℕ → List β) (k : ℕ) :
    List.flatMap f (List.range (k + 1)) = List.flatMap f (List.range k) ++ f k := by
  rw [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil]

theorem blockBodyCells_row_range (instr : CMInstr) (D y : ℕ)
    (c : (ℕ × ℕ) × Char) (hc : c ∈ blockBodyCells instr D y) :
    y ≤ c.1.2 ∧ c.1.2 < y + blockHeight instr := by
  cases instr with
  | inc _ =>
      simp only [blockBodyCells, List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with hc | hc | hc | hc <;> subst c <;> simp only [blockHeight] <;> omega
  | decz _ _ =>
      simp only [blockBodyCells, List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with hc | hc | hc | hc | hc | hc | hc | hc | hc <;> subst c <;>
        simp only [blockHeight] <;> omega
  | jump _ =>
      simp only [blockBodyCells, List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with hc | hc <;> subst c <;> simp only [blockHeight] <;> omega
  | halt =>
      simp only [blockBodyCells, List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with hc | hc <;> subst c <;> simp only [blockHeight] <;> omega

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
  · have hrange := blockBodyCells_row_range (prog.getD j .halt) (entryColumn prog j)
      (blockRow prog j) c hc
    have hle := blockRow_range_le prog j i hji
    omega
  · have hm := blockCorridorCells_mem prog j (prog.getD j .halt) c hc
    rcases hm with ⟨k, hk, hck⟩
    have hcorr := corridorCells_row_lt prog j k (by omega) c hck
    have h0 : prog.length ≤ blockRow prog j := blockRow_ge_length prog j
    have hj : blockRow prog j < blockRow prog i := blockRow_strict_mono prog hji
    omega

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
        interval_cases dx <;> interval_cases dy <;>
          simp [blockBodyCells, blockBodyAt, lastCellAt, -- no_squeeze
            blockWidth, blockHeight, hmodx, hmody, h0y, hD]
      · simp only [blockWidth, blockHeight] at hdx hdy
        interval_cases dx <;> interval_cases dy <;>
          simp [blockBodyCells, blockBodyAt, lastCellAt, -- no_squeeze
            blockWidth, blockHeight, hmodx, hmody, h0y, hD]
  | decz c0 _ =>
      fin_cases c0
      · simp only [blockWidth, blockHeight] at hdx hdy
        interval_cases dx <;> interval_cases dy <;>
          simp [blockBodyCells, blockBodyAt, lastCellAt, -- no_squeeze
            blockWidth, blockHeight, hmodx, hmody, h0y, hD]
      · simp only [blockWidth, blockHeight] at hdx hdy
        interval_cases dx <;> interval_cases dy <;>
          simp [blockBodyCells, blockBodyAt, lastCellAt, -- no_squeeze
            blockWidth, blockHeight, hmodx, hmody, h0y, hD]
  | jump _ =>
      simp only [blockWidth, blockHeight] at hdx hdy
      interval_cases dx <;> interval_cases dy <;>
        simp [blockBodyCells, blockBodyAt, lastCellAt, -- no_squeeze
          blockWidth, blockHeight, hmodx, hmody, h0y, hD]
  | halt =>
      simp only [blockWidth, blockHeight] at hdx hdy
      interval_cases dx <;> interval_cases dy <;>
        simp [blockBodyCells, blockBodyAt, lastCellAt, -- no_squeeze
          blockWidth, blockHeight, hmodx, hmody, h0y, hD]

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
    · have hrange := blockBodyCells_row_range (prog.getD j .halt) (entryColumn prog j)
        (blockRow prog j) c hc
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
    · have hrange := blockBodyCells_row_range (prog.getD j .halt) (entryColumn prog j)
        (blockRow prog j) c hc
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
  rw [lastCellAt_body (prog.getD i .halt) (entryColumn prog i) (blockRow prog i) dx dy hdx hdy
    hW hH0]
  have hskip : lastCellAt (playfieldWidth prog) (playfieldHeight prog)
      (blockBodyAt (prog.getD i .halt) dx dy) (blockCorridorCells prog i (prog.getD i .halt))
      (entryColumn prog i + dx) (blockRow prog i + dy)
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
