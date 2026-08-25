/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanFunge.Theory.Completeness.LayoutBlock
import LeanFunge.Theory.Completeness.LayoutCells
import LeanFunge.Theory.Completeness.Routing
import LeanFunge.Theory.Run.Relational
import LeanFunge.Theory.Step
import Mathlib.Tactic
/-!
# The Corridor Routing Foundations

A jump edge routes the pointer up its branch column to the header, across

the corridor row, and down to the target block. This module proves the drop

foundations: a run that drops down through cells that are spaces or `v`s (a

drop passes the exit `v` of the preceding block), the single-step version of

that drop, and the fact that a block body holds no cell beyond its width.

The generated playfield reads back a block's body cell at any column offset: within the body it is
the body cell, and beyond the block's width it is a space. These lemmas generalize the cell lookup
beyond a block's column span, which the corridor routing uses to show that path cells are spaces.

The only cells on a header row are a block's corridor turn and drop. This module proves that every
other block misses a header cell: a block other than `y` places no cell on row `y`, so the header
readback skips it.

The only cells on a header row are a block's corridor turn and drop. This module proves that lookup:
a run of cells in a header row reads back the corridor's turn or drop, or a space, so the corridor
routing can show its turn and drop cells sit where expected.

After a block executes, the pointer must travel to the next block. For the

fall-through case, every block's exit `v` sits at the next entry column on the

block's bottom row, and the cell below it is a space, so one step down drops

the pointer onto the next block's `>`. This module proves the generic

fall-through drop for arbitrary programs; the jump corridor routing lives

here as well once the up-turn-drop geometry is proven.

A jump edge's branch column is one column before the next entry, so it holds no

block cell at all: the corridor's up column is clean. This module proves the

row-finding and cell lookups that show the up segment of a corridor is a run

of spaces.

## Definitions

* `corridorRowAt`: The cell a corridor row places at a column, or a space.

* (none)

* `branchColumn`: The branch column of a block.

## Theorems

* `step_down_cell`: A step through a space or a `v` while going down keeps

  the pointer down.

* `run_down`: Running down through spaces and `v`s keeps the pointer down.

* `blockBodyAt_out`: A block body has no cell beyond its width.

* `lastCellAt_body_out`: A body readback beyond the block's width is a space.

* `lastCellAt_body_any`: A body readback at any column is the body cell or a space.

* `lastCellAt_block_i_any`: Block `i` reads back its body cell at any column offset.

* `playfield_row_at`: A cell in a block's row range is the block's body cell, at any column.

* `blockCellList_row_ne_header`: Every cell of a block other than `y` has a row other than `y`.

* `lastCellAt_block_after_header`: A later block does not touch a header cell.

* `lastCellAt_flatMap_before_header`: An earlier block does not touch a header cell.

* `entryColumn_mono`: The entry columns are non-decreasing.

* `entryColumn_lt_of_lt`: A smaller entry column has a smaller index.

* `lastCellAt_block_header`: Block `y` reads back its corridor cell on the header row.

* `playfield_header_get`: A header-row cell is the corridor's turn or drop.

* `blockBodyAt_corner`: The bottom-right corner of a block's body is a space.

* `fallthrough_drop`: One step down from a block's bottom row reaches the

  next block's entry.

* `blockRow_find`: Every row in the block region lies in a block's row range.

* `blockBodyAt_exit_or_space`: The cells on a block's exit column are a `v` or a space.

* `corridorUp_cell`: The cells on the branch column above a block are spaces.
* `branchColumn_two`: The branch column is clear of the boot columns.
-/

namespace LeanFunge

namespace Completeness

/-- The cell that header row `y` places at column `x`: the corridor turn at
    the branch column, the drop `v` at the target's entry column, or a
    space. -/
def corridorRowAt (prog : CMProgram) (x y : ℕ) : Char :=
  match prog.getD y .halt with
  | .decz _ k =>
      let C := entryColumn prog y + 4
      if x = C then (if entryColumn prog k ≥ C then '>' else '<')
      else if x = entryColumn prog k then 'v' else ' '
  | .jump k =>
      let C := entryColumn prog y + 1
      if x = C then (if entryColumn prog k ≥ C then '>' else '<')
      else if x = entryColumn prog k then 'v' else ' '
  | _ => ' '

/-- A step through a space or a `v` while going down keeps the pointer down. -/
theorem step_down_cell (s : State w h) (hsm : s.stringMode = false) (hdir : s.dir = .down)
    (hcell : s.grid.get s.pc.1 s.pc.2 = ' ' ∨ s.grid.get s.pc.1 s.pc.2 = 'v') :
    step s = some { s with pc := stepPos w h .down s.pc } := by
  rcases hcell with hsp | hv
  · rw [step_space s hsm hsp]
    rw [hdir]
  · rw [step_dir_down s hsm hv]
    rw [hdir]

/-- Running down through spaces and `v`s keeps the pointer down. -/
theorem run_down (s : State w h) (n : ℕ) (x y : ℕ)
    (hsm : s.stringMode = false) (hpc : s.pc = (x % w, y % h))
    (hdir : s.dir = .down)
    (hdown : ∀ k : ℕ, k < n →
      s.grid.get (runPos w h k .down (x % w, y % h)).1 (runPos w h k .down (x % w, y % h)).2 = ' '
        ∨ s.grid.get (runPos w h k .down (x % w, y % h)).1
          (runPos w h k .down (x % w, y % h)).2 = 'v') :
    run n s = some { s with pc := runPos w h n .down (x % w, y % h) } := by
  induction n with
  | zero =>
      rw [run]
      congr
      simp only [runPos, ← hpc]
  | succ n ih =>
      have hrun : run n s = some { s with pc := runPos w h n .down (x % w, y % h) } :=
        ih (fun k hk => hdown k (Nat.lt_trans hk (Nat.lt_succ_self n)))
      rw [show run (n + 1) s = (run n s).bind step by rfl]
      rw [hrun]
      change step { s with pc := runPos w h n .down (x % w, y % h) }
        = some { s with pc := runPos w h (n + 1) .down (x % w, y % h) }
      have hp : s.grid.get (runPos w h n .down (x % w, y % h)).1
        (runPos w h n .down (x % w, y % h)).2 = ' '
          ∨ s.grid.get (runPos w h n .down (x % w, y % h)).1
            (runPos w h n .down (x % w, y % h)).2 = 'v' :=
        hdown n (Nat.lt_succ_self n)
      rcases hp with hsp | hv
      · rw [show step { s with pc := runPos w h n .down (x % w, y % h) }
            = some { s with pc := runPos w h (n + 1) .down (x % w, y % h) } by
          unfold step
          have hdec : decodeChar ' ' = .nop := by unfold decodeChar; rfl
          simp only [hsm, hsp, hdec, stepState]
          rw [hdir]
          rfl]
      · rw [show step { s with pc := runPos w h n .down (x % w, y % h) }
            = some { s with pc := runPos w h (n + 1) .down (x % w, y % h) } by
          unfold step
          have hdec : decodeChar 'v' = .down := by unfold decodeChar; rfl
          simp only [hsm, hv, hdec, stepState]
          rw [hdir]
          rfl]

/-- A block body has no cell beyond its width. -/
theorem blockBodyAt_out (instr : CMInstr) (dx dy : ℕ) (hdx : blockWidth instr < dx) :
    blockBodyAt instr dx dy = ' ' := by
  cases instr with
  | inc c0 => fin_cases c0 <;> simp only [blockBodyAt, blockWidth] at hdx ⊢ <;> split_ifs
    <;> first | rfl | omega
  | decz c0 _ => fin_cases c0 <;> simp only [blockBodyAt, blockWidth] at hdx ⊢ <;> split_ifs
    <;> first | rfl | omega
  | jump _ => simp only [blockBodyAt, blockWidth] at hdx ⊢; split_ifs <;> first | rfl | omega
  | halt => simp only [blockBodyAt, blockWidth] at hdx ⊢; split_ifs <;> first | rfl | omega

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
             hD, hD1, hD2, hD3, hDx, hy', hYq, add_left_cancel_iff]
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
             hD, hD1, hD2, hD3, hD4, hD5, hDx, hy', hY1, hY2, hY3, hYq, add_left_cancel_iff]
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
        hD, hD1, hDx, hy', hYq, add_left_cancel_iff]
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
        hD, hD1, hDx, hy', hYq, add_left_cancel_iff]
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
  rw [lastCellAt_body_any (prog.getD i .halt) (entryColumn prog i) (blockRow prog i) dx dy
    hdy hW hH0 hx hH]
  have hskip : lastCellAt (playfieldWidth prog) (playfieldHeight prog)
      (blockBodyAt (prog.getD i .halt) dx dy)
      (blockCorridorCells prog i (prog.getD i .halt)) (entryColumn prog i + dx)
      (blockRow prog i + dy)
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
  rw [lastCellAt_skip_boot prog _ _ _ hH (by
    have hge : prog.length ≤ blockRow prog i := blockRow_ge_length prog i
    omega)]
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

/-- Every cell of a block other than `y` has a row other than `y`. -/
theorem blockCellList_row_ne_header (prog : CMProgram) (j y : ℕ) (hjy : j ≠ y)
    (hy : y < prog.length)
    (c : (ℕ × ℕ) × Char) (hc : c ∈ blockCellList prog j) :
    c.1.2 ≠ y := by
  rw [blockCellList_eq] at hc
  simp only [List.mem_append] at hc
  rcases hc with hc | hc
  · have hrange := blockBodyCells_row_range (prog.getD j .halt) (entryColumn prog j)
      (blockRow prog j) c hc
    have hge := blockRow_ge_length prog j
    omega
  · rcases blockCorridorCells_mem prog j (prog.getD j .halt) c hc with ⟨k, hk, hck⟩
    simp only [corridorCells, List.mem_cons, List.not_mem_nil, or_false] at hck
    rcases hck with hck | hck <;> simp only [
      hck, List.getD_eq_getElem?_getD, ge_iff_le, tsub_le_iff_right, ↓Char.isValue, ne_eq] <;> omega

/-- A later block does not touch a header cell. -/
theorem lastCellAt_block_after_header (prog : CMProgram) (y k x : ℕ) (hyk : y < k)
    (hk : k < prog.length) (hy : y < prog.length) (hH : y < playfieldHeight prog) (init : Char) :
    lastCellAt (playfieldWidth prog) (playfieldHeight prog) init (blockCellList prog k) x y
      = init := by
  apply lastCellAt_skip_row (w := playfieldWidth prog) (h := playfieldHeight prog) init
    (blockCellList prog k) x y hH
  · intro c hc
    rw [blockCellList_eq] at hc
    simp only [List.mem_append] at hc
    rcases hc with hc | hc
    · have hrange := blockBodyCells_row_range (prog.getD k .halt) (entryColumn prog k)
        (blockRow prog k) c hc
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
    exact blockCellList_row_ne_header (prog := prog) (j := k) (y := y)
      (hjy := by omega) (hy := hy) c hc

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
    · have hrange := blockBodyCells_row_range (prog.getD j .halt) (entryColumn prog j)
        (blockRow prog j) c hcj
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

/-- The entry columns are non-decreasing. -/
theorem entryColumn_mono (prog : CMProgram) (i j : ℕ) (hij : i ≤ j) :
    entryColumn prog i ≤ entryColumn prog j := by
  by_cases h : i < j
  · exact le_of_lt (entryColumn_strict_mono prog h)
  · have : i = j := by omega
    subst i
    rfl

/-- A smaller entry column has a smaller index. -/
theorem entryColumn_lt_of_lt (prog : CMProgram) {i j : ℕ}
    (h : entryColumn prog i < entryColumn prog j) :
    i < j := by
  by_contra h'
  have : j ≤ i := by omega
  have hmono : entryColumn prog j ≤ entryColumn prog i := entryColumn_mono prog j i this
  omega

/-- Block `y` reads back its corridor cell on the header row. -/
theorem lastCellAt_block_header (prog : CMProgram) (y x : ℕ) (hy : y < prog.length)
    (ht : ∀ c : Fin 2, ∀ k : ℕ,
      (prog.getD y .halt = .decz c k ∨ prog.getD y .halt = .jump k) → k < prog.length)
    (hx : x < playfieldWidth prog) (hH : y < playfieldHeight prog) :
    lastCellAt (playfieldWidth prog) (playfieldHeight prog) ' ' (blockCellList prog y) x y
      = corridorRowAt prog x y := by
  rw [blockCellList_eq]
  rw [lastCellAt_append]
  have hskipBody : lastCellAt (playfieldWidth prog) (playfieldHeight prog) ' '
      (blockBodyCells (prog.getD y .halt) (entryColumn prog y) (blockRow prog y)) x y = ' ' := by
    apply lastCellAt_skip_row (w := playfieldWidth prog) (h := playfieldHeight prog) ' '
      (blockBodyCells (prog.getD y .halt) (entryColumn prog y) (blockRow prog y)) x y hH
    · intro c hc
      have hrange := blockBodyCells_row_range (prog.getD y .halt) (entryColumn prog y)
        (blockRow prog y) c hc
      have hle : blockRow prog y + blockHeight (prog.getD y .halt) ≤ playfieldHeight prog := by
        rw [playfieldHeight]
        exact blockRow_range_le prog y prog.length hy
      omega
    · intro c hc
      have hrange := blockBodyCells_row_range (prog.getD y .halt) (entryColumn prog y)
        (blockRow prog y) c hc
      have hge := blockRow_ge_length prog y
      rcases hrange with ⟨hr1, hr2⟩
      omega
  rw [hskipBody]
  have hC : entryColumn prog y + blockWidth (prog.getD y .halt) - 1 < playfieldWidth prog := by
    have hmono : entryColumn prog (y + 1) ≤ playfieldWidth prog := by
      rw [playfieldWidth]
      by_cases h : y + 1 < prog.length
      · exact le_of_lt (entryColumn_strict_mono prog h)
      · have hy' : y + 1 = prog.length := by omega
        rw [hy']
    have hw : 1 ≤ blockWidth (prog.getD y .halt) := blockWidth_pos _
    rw [entryColumn_succ] at hmono
    omega
  cases hget : prog.getD y .halt with
  | decz c k =>
      have hk : k < prog.length := ht c k (Or.inl hget)
      have hDk : entryColumn prog k < playfieldWidth prog := by
        rw [playfieldWidth]
        exact entryColumn_strict_mono prog hk
      rw [hget] at hC
      simp only [blockWidth] at hC
      simp only [hget, blockCorridorCells, corridorRowAt, corridorCells, lastCellAt,
        List.foldl_cons, List.foldl_nil, blockWidth]
      rw [Nat.mod_eq_of_lt hC]
      rw [Nat.mod_eq_of_lt hDk]
      rw [Nat.mod_eq_of_lt hx]
      by_cases hxE : x = entryColumn prog k
      · have hne : entryColumn prog y + 4 ≠ entryColumn prog k := by
          intro h
          -- entryColumn k = entryColumn y + 4 is between entryColumn y and entryColumn (y+1)
          have h1 : entryColumn prog y < entryColumn prog y + 4 := by omega
          have h2 : entryColumn prog y + 4 < entryColumn prog (y + 1) := by
            rw [entryColumn_succ]
            rw [hget]
            norm_num [blockWidth]
          have hk1 : y < k :=
            entryColumn_lt_of_lt (prog := prog) (i := y) (j := k) (by omega)
          have hk2 : k < y + 1 :=
            entryColumn_lt_of_lt (prog := prog) (i := k) (j := y + 1) (by omega)
          omega
        have hxC : x ≠ entryColumn prog y + 4 := by
          intro hx'
          have : entryColumn prog k = entryColumn prog y + 4 := by omega
          exact hne this.symm
        simp only [hxE, and_self, ↓reduceIte, ↓Char.isValue, eq_comm, ge_iff_le,
          right_eq_ite_iff]
        all_goals intro h; exfalso; omega
      · simp only [
        hxE, eq_comm, and_true, ↓reduceIte, Nat.add_one_sub_one, ge_iff_le, ↓Char.isValue]
  | jump k =>
      have hk : k < prog.length := ht 0 k (Or.inr hget)
      have hDk : entryColumn prog k < playfieldWidth prog := by
        rw [playfieldWidth]
        exact entryColumn_strict_mono prog hk
      rw [hget] at hC
      simp only [blockWidth] at hC
      simp only [hget, blockCorridorCells, corridorRowAt, corridorCells, lastCellAt,
        List.foldl_cons, List.foldl_nil, blockWidth]
      rw [Nat.mod_eq_of_lt hC]
      rw [Nat.mod_eq_of_lt hDk]
      rw [Nat.mod_eq_of_lt hx]
      by_cases hxE : x = entryColumn prog k
      · have hne : entryColumn prog y + 1 ≠ entryColumn prog k := by
          intro h
          have h1 : entryColumn prog y < entryColumn prog y + 1 := by omega
          have h2 : entryColumn prog y + 1 < entryColumn prog (y + 1) := by
            rw [entryColumn_succ]
            rw [hget]
            norm_num [blockWidth]
          have hk1 : y < k :=
            entryColumn_lt_of_lt (prog := prog) (i := y) (j := k) (by omega)
          have hk2 : k < y + 1 :=
            entryColumn_lt_of_lt (prog := prog) (i := k) (j := y + 1) (by omega)
          omega
        have hxC : x ≠ entryColumn prog y + 1 := by
          intro hx'
          have : entryColumn prog k = entryColumn prog y + 1 := by omega
          exact hne this.symm
        simp only [hxE, and_self, ↓reduceIte, ↓Char.isValue, eq_comm, ge_iff_le,
          Order.add_one_le_iff, right_eq_ite_iff]
        all_goals intro h; exfalso; omega
      · simp only [
        hxE, eq_comm, and_true, ↓reduceIte, Nat.add_one_sub_one, ge_iff_le, Order.add_one_le_iff,
        ↓Char.isValue]
  | inc c0 =>
      simp only [corridorRowAt]
      rw [hget]
      rfl
  | halt =>
      simp only [corridorRowAt]
      rw [hget]
      rfl

/-- A header-row cell is the corridor's turn or drop. -/
theorem playfield_header_get (prog : CMProgram) (x y : ℕ) (hy : y < prog.length)
    (ht : ∀ c : Fin 2, ∀ k : ℕ,
      (prog.getD y .halt = .decz c k ∨ prog.getD y .halt = .jump k) → k < prog.length)
    (hx : x < playfieldWidth prog) (hb : y = 0 → 2 ≤ x) :
    (playfieldOf prog).get x y = corridorRowAt prog x y := by
  let pw := playfieldWidth prog
  let ph := playfieldHeight prog
  have hH : y < playfieldHeight prog := by
    have hle : prog.length ≤ playfieldHeight prog := by
      rw [playfieldHeight]
      exact blockRow_ge_length prog prog.length
    omega
  rw [playfieldOf_get_eq_lastCellAt]
  unfold playfieldCells
  rw [lastCellAt_skip_boot_col prog _ _ _ hH hx hb]
  have hmain : ∀ k : ℕ, y < k → k ≤ prog.length →
      lastCellAt pw ph ' ' (List.flatMap (fun j => blockCellList prog j) (List.range k)) x y
        = corridorRowAt prog x y := by
    intro k hyk hkn
    induction k with
    | zero => omega
    | succ k ih =>
        by_cases hyk' : y < k
        · have hprev := ih hyk' (by omega)
          rw [flatMap_range_succ, lastCellAt_append, hprev]
          exact lastCellAt_block_after_header prog y k x hyk' (by omega) hy hH
            (corridorRowAt prog x y)
        · have heq : y = k := by omega
          subst y
          rw [flatMap_range_succ, lastCellAt_append]
          rw [lastCellAt_flatMap_before_header prog k x hy hH]
          exact lastCellAt_block_header prog k x hy ht hx hH
  have hres := hmain prog.length (by omega) (by rfl)
  rw [hres]

/-- The bottom-right corner of a block's body holds no cell. -/
theorem blockBodyAt_corner (instr : CMInstr) :
    blockBodyAt instr (blockWidth instr) (blockHeight instr - 1) = ' ' := by
  cases instr with
  | inc c0 => fin_cases c0 <;> rfl
  | decz c0 _ => fin_cases c0 <;> rfl
  | jump _ => rfl
  | halt => rfl

/-- One step down from a block's bottom row reaches the next block's entry. -/
theorem fallthrough_drop (prog : CMProgram) (i : ℕ) (hi1 : i + 1 < prog.length)
    (s : State (playfieldWidth prog) (playfieldHeight prog))
    (hsm : s.stringMode = false)
    (hpc : s.pc =
      (entryColumn prog (i + 1), blockRow prog i + (blockHeight (prog.getD i .halt) - 1)))
    (hdir : s.dir = .down) (hgrid : s.grid = playfieldOf prog) :
    run 1 s = some { s with
      pc := (entryColumn prog (i + 1), blockRow prog (i + 1)),
      dir := .down } := by
  have hspace : (playfieldOf prog).get (entryColumn prog (i + 1))
      (blockRow prog i + (blockHeight (prog.getD i .halt) - 1)) = ' ' := by
    have hpb := playfield_block_get prog i hi1 (blockWidth (prog.getD i .halt))
        (blockHeight (prog.getD i .halt) - 1) (by rfl)
          (by have := blockHeight_pos (prog.getD i .halt); omega)
    rw [← entryColumn_succ] at hpb
    rw [blockBodyAt_corner] at hpb
    exact hpb
  have hW : entryColumn prog (i + 1) < playfieldWidth prog := by
    rw [playfieldWidth]
    exact entryColumn_strict_mono prog hi1
  have hH : blockRow prog i + blockHeight (prog.getD i .halt) < playfieldHeight prog := by
    rw [playfieldHeight]
    rw [← blockRow_succ]
    exact blockRow_strict_mono prog hi1
  have hhy : (blockRow prog i + (blockHeight (prog.getD i .halt) - 1)) + 1 <
    playfieldHeight prog := by
    have hb := blockHeight_pos (prog.getD i .halt)
    omega
  rw [show run 1 s = step s by rfl]
  rw [step_space s hsm (by rw [hpc, hgrid]; exact hspace)]
  rw [hdir, hpc, stepPos_down (playfieldWidth prog) (playfieldHeight prog)
      (entryColumn prog (i + 1))
      (blockRow prog i + (blockHeight (prog.getD i .halt) - 1)) hW hhy]
  have hpc' : (entryColumn prog (i + 1),
    (blockRow prog i + (blockHeight (prog.getD i .halt) - 1)) + 1)
      = (entryColumn prog (i + 1), blockRow prog (i + 1)) := by
    rw [blockRow_succ]
    apply Prod.ext
    · rfl
    · have hb := blockHeight_pos (prog.getD i .halt)
      omega
  rw [hpc']

/-- The branch column of block `i`: the corridor's up column, one column
    before the next entry. -/
abbrev branchColumn (prog : CMProgram) (i : ℕ) : ℕ :=
  entryColumn prog i + blockWidth (prog.getD i .halt) - 1

/-- The branch column is clear of the boot columns. Entry columns start at one
    and every block is at least two wide, so a branch column is at least two —
    which is what the header lookups need on row zero. -/
theorem branchColumn_two (prog : CMProgram) (i : ℕ) : 2 ≤ branchColumn prog i := by
  have hep := entryColumn_pos prog i
  have hbw := blockWidth_two (prog.getD i .halt)
  unfold branchColumn
  omega

/-- Every row of the block region lies in some block's row range. -/
theorem blockRow_find (prog : CMProgram) (r : ℕ) (hr0 : prog.length ≤ r)
    (hr : r < playfieldHeight prog) :
    ∃ j : ℕ, j < prog.length ∧ blockRow prog j ≤ r ∧ r < blockRow prog j + blockHeight
      (prog.getD j .halt) := by
  have hlen0 : 0 < prog.length := by
    by_contra h
    have hz : prog.length = 0 := by omega
    have h0 : playfieldHeight prog = 0 := by
      unfold playfieldHeight
      simp only [blockRow, hz]
    omega
  have hfirst : ∃ j : ℕ, j ≤ prog.length ∧ r < blockRow prog j := by
    refine ⟨prog.length, by rfl, ?_⟩
    simpa only [playfieldHeight] using hr
  set j := Nat.find hfirst
  have hjle : j ≤ prog.length := (Nat.find_spec hfirst).1
  have hjr : r < blockRow prog j := (Nat.find_spec hfirst).2
  have hjmin : ∀ j' : ℕ, j' < j → ¬(j' ≤ prog.length ∧ r < blockRow prog j') := by
    intro j' hj'
    by_contra hp
    have hle : Nat.find hfirst ≤ j' := Nat.find_min' hfirst hp
    have : j ≤ j' := by
      change Nat.find hfirst ≤ j'
      exact hle
    omega
  have hjpos : 0 < j := by
    by_contra h
    have hj0 : j = 0 := by omega
    have hjr0 : r < blockRow prog 0 := by simpa only [hj0] using hjr
    have hbr0 : blockRow prog 0 ≤ r := by
      unfold blockRow
      exact hr0
    omega
  have hjlt : j - 1 < prog.length := by
    omega
  have hbj1 : blockRow prog (j - 1) ≤ r := by
    by_contra h
    have hgt : r < blockRow prog (j - 1) := by omega
    have hc : ¬(j - 1 ≤ prog.length ∧ r < blockRow prog (j - 1)) := hjmin (j - 1) (by omega)
    exact hc ⟨by omega, hgt⟩
  refine ⟨j - 1, hjlt, hbj1, ?_⟩
  have hsucc : blockRow prog j = blockRow prog (j - 1) + blockHeight (prog.getD (j - 1) .halt) := by
    calc
      blockRow prog j = blockRow prog ((j - 1) + 1) := by
        congr
        omega
      _ = blockRow prog (j - 1) + blockHeight (prog.getD (j - 1) .halt)
        := blockRow_succ prog (j - 1)
  rw [hsucc] at hjr
  omega

/-- The cells on a block's exit column (offset `blockWidth`) are a `v` or a
    space. -/
theorem blockBodyAt_exit_or_space (instr : CMInstr) (dy : ℕ) (hdy : dy < blockHeight instr) :
    blockBodyAt instr (blockWidth instr) dy = ' ' ∨
      blockBodyAt instr (blockWidth instr) dy = 'v' := by
  cases instr with
  | inc c0 =>
      fin_cases c0 <;> by_cases h : dy = 0
        <;> simp only [
          blockBodyAt, blockWidth, h, OfNat.ofNat_ne_zero, and_true, ↓reduceIte, OfNat.ofNat_ne_one,
          Nat.succ_ne_self, and_self, ↓Char.isValue, Char.reduceEq, or_true, and_false, or_false]
  | decz c0 _ =>
      fin_cases c0 <;> by_cases h : dy = 3
        <;> simp only [
          blockBodyAt, blockWidth, h, OfNat.ofNat_ne_zero, and_self, ↓reduceIte, OfNat.ofNat_ne_one,
          Nat.reduceEqDiff, Nat.succ_ne_self, and_true, ↓Char.isValue, Char.reduceEq, or_true,
          false_and, and_false, or_false]
  | jump _ =>
      simp only [
        blockBodyAt, blockWidth, OfNat.ofNat_ne_zero, false_and, ↓reduceIte, OfNat.ofNat_ne_one,
        ↓Char.isValue, Char.reduceEq, or_false]
  | halt =>
      simp only [
        blockBodyAt, blockWidth, OfNat.ofNat_ne_zero, false_and, ↓reduceIte, OfNat.ofNat_ne_one,
        ↓Char.isValue, Char.reduceEq, or_false]

/-- The cells on the branch column of block `i`, strictly above the block,
    are spaces. -/
theorem corridorUp_cell (prog : CMProgram) (i r : ℕ) (hi : i < prog.length)
    (hwell : wellFormed prog) (hrow : i < r) (hr : r < blockRow prog i) :
    (playfieldOf prog).get (branchColumn prog i) r = ' ' := by
  let C := branchColumn prog i
  have hC : C = entryColumn prog i + blockWidth (prog.getD i .halt) - 1 := rfl
  have hwi1 : 1 ≤ blockWidth (prog.getD i .halt) := blockWidth_pos _
  have hwi2 : 2 ≤ blockWidth (prog.getD i .halt) := by
    cases prog.getD i .halt <;> norm_num [blockWidth]
  have hCW : C < playfieldWidth prog := by
    have hmono : entryColumn prog (i + 1) ≤ playfieldWidth prog := by
      rw [playfieldWidth]
      exact entryColumn_mono prog (i + 1) prog.length (by omega)
    rw [entryColumn_succ] at hmono
    rw [hC]
    omega
  have hCnotentry : ∀ t : ℕ, C ≠ entryColumn prog t := by
    intro t h
    have hCi : entryColumn prog i < C := by
      rw [hC]
      omega
    have h1 : entryColumn prog i < entryColumn prog t := by omega
    have h2 : entryColumn prog t < entryColumn prog (i + 1) := by
      rw [← h]
      rw [hC, entryColumn_succ]
      omega
    have hi1 : i < t := entryColumn_lt_of_lt (prog := prog) (i := i) (j := t) h1
    have hi2 : t < i + 1 := entryColumn_lt_of_lt (prog := prog) (i := t) (j := i + 1) h2
    omega
  by_cases hhead : r < prog.length
  · have hC2 : 2 ≤ C := branchColumn_two prog i
    have hcell := playfield_header_get prog C r (by omega)
      (fun c k hk => hwell r (by omega) c k hk) hCW (fun _ => hC2)
    rw [hcell]
    cases hget : prog.getD r .halt with
    | decz c k' =>
        have hCne : C ≠ entryColumn prog r + 4 := by
          intro h
          have hmono : entryColumn prog (i + 1) ≤ entryColumn prog r :=
            entryColumn_mono prog (i + 1) r (by omega)
          rw [entryColumn_succ] at hmono
          rw [hC] at h
          omega
        have hCne_k : C ≠ entryColumn prog k' := hCnotentry k'
        unfold corridorRowAt
        rw [hget]
        simp only [hCne, hCne_k, ↓reduceIte, ↓Char.isValue]
    | jump k' =>
        have hCne : C ≠ entryColumn prog r + 1 := by
          intro h
          have hmono : entryColumn prog (i + 1) ≤ entryColumn prog r :=
            entryColumn_mono prog (i + 1) r (by omega)
          rw [entryColumn_succ] at hmono
          rw [hC] at h
          omega
        have hCne_k : C ≠ entryColumn prog k' := hCnotentry k'
        unfold corridorRowAt
        rw [hget]
        simp only [hCne, hCne_k, ↓reduceIte, ↓Char.isValue]
    | inc c0 =>
        unfold corridorRowAt
        rw [hget]
    | halt =>
        unfold corridorRowAt
        rw [hget]
  · have hblk : prog.length ≤ r := by omega
    rcases blockRow_find prog r hblk (by
        have hle : blockRow prog i ≤ playfieldHeight prog := by
          rw [playfieldHeight]
          exact blockRow_mono prog (i := i) (j := prog.length) (by omega)
        omega) with ⟨j, hj, hbj0, hbj1⟩
    have hbj : blockRow prog j < blockRow prog i := by omega
    have hji : j < i := by
      by_contra h
      have : i ≤ j := by omega
      have hmono : blockRow prog i ≤ blockRow prog j := blockRow_mono prog this
      omega
    have hWj : entryColumn prog (j + 1) ≤ entryColumn prog i := by
      rw [entryColumn_succ]
      exact entryColumn_mono prog (j + 1) i (by omega)
    have hWj' : entryColumn prog j + blockWidth (prog.getD j .halt) ≤ entryColumn prog i := by
      rw [← entryColumn_succ]
      exact hWj
    have hdx : blockWidth (prog.getD j .halt) < C - entryColumn prog j := by
      rw [hC]
      omega
    have hDlC : entryColumn prog j < C := by
      have hmono : entryColumn prog j < entryColumn prog i := entryColumn_strict_mono prog hji
      have hCi : entryColumn prog i < C := by
        rw [hC]
        omega
      omega
    have hcell := playfield_row_at prog j (by omega)
      (C - entryColumn prog j) (r - blockRow prog j) (by omega) (by omega)
    have hc1 : entryColumn prog j + (C - entryColumn prog j) = C := by omega
    have hc2 : blockRow prog j + (r - blockRow prog j) = r := by omega
    rw [hc1, hc2] at hcell
    rw [blockBodyAt_out (prog.getD j .halt) (C - entryColumn prog j)
        (r - blockRow prog j) hdx] at hcell
    simpa only [↓Char.isValue] using hcell

end Completeness

end LeanFunge
