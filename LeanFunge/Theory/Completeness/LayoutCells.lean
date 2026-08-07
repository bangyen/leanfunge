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

The generated playfield places exactly the block bodies and the jump corridors. This module defines the placed cells and the last-cell lookup over them: a run of puts reads back the last placed cell, and the playfield readback equals the lookup over the flattened placed cells.

## Main definitions

* `blockBodyCells`: The cells of a block's body, positioned.
* `blockBodyAt`: The block body cell at an offset, or a space.
* `blockCorridorCells`: The corridor cells of a block's jump edge, or none.
* `playfieldCells`: The flattened list of all placed cells, in fold order.
* `lastCellAt`: The value of the last placed cell at a position, or the initial value.

## Theorems

* `blockCellList_eq`: The block cell list splits into the body and the corridor.
* `put_get`: A put reads back its cell and leaves other cells unchanged.
* `foldl_bind_put`: Folding the blocks one at a time equals folding the flattened cells.
* `foldl_put_get`: A run of puts reads back the last placed cell.
* `playfieldOf_get_eq_lastCellAt`: The playfield readback equals the last cell lookup over the flattened cells.
* `lastCellAt_skip_row`: A run of cells whose rows miss the lookup row does not change the lookup.
* `lastCellAt_append`: The lookup over a concatenation composes the accumulators.
* `flatMap_range_succ`: A flat map over a successor range splits off the last block.
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
  · simp only [h, eq_comm, and_comm, if_false]
  · simp only [h, eq_comm, and_comm, if_false]

/-- Folding the blocks one at a time equals folding the flattened cells. -/
theorem foldl_bind_put (prog : CMProgram)
    (g0 : Grid (playfieldWidth prog) (playfieldHeight prog)) :
    (List.range prog.length).foldl
        (fun g i => (blockCellList prog i).foldl (fun g cell => Grid.put g cell.1.1 cell.1.2 cell.2) g) g0
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

end Completeness

end LeanFunge
