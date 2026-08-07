/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanFunge.Theory.Completeness.LayoutCellMain
import LeanFunge.Theory.Completeness.LayoutCellRange
import LeanFunge.Theory.Completeness.LayoutCorridor
import LeanFunge.Theory.Completeness.LayoutHeaderRow
import LeanFunge.Theory.Completeness.LayoutRowAt
import Mathlib.Tactic

/-!
# The Header-Row Lookup

The only cells on a header row are a block's corridor turn and drop. This module proves that lookup: a run of cells in a header row reads back the corridor's turn or drop, or a space, so the corridor routing can show its turn and drop cells sit where expected.

## Main definitions

* (none)

## Theorems

* `entryColumn_mono`: The entry columns are non-decreasing.
* `entryColumn_lt_of_lt`: A smaller entry column has a smaller index.
* `lastCellAt_block_header`: Block `y` reads back its corridor cell on the header row.
* `playfield_header_get`: A header-row cell is the corridor's turn or drop.
-/

namespace LeanFunge

namespace Completeness

/-- The entry columns are non-decreasing. -/
theorem entryColumn_mono (prog : CMProgram) (i j : ℕ) (hij : i ≤ j) :
    entryColumn prog i ≤ entryColumn prog j := by
  by_cases h : i < j
  · exact le_of_lt (entryColumn_strict_mono prog h)
  · have : i = j := by omega
    subst i
    rfl

/-- A smaller entry column has a smaller index. -/
theorem entryColumn_lt_of_lt (prog : CMProgram) {i j : ℕ} (h : entryColumn prog i < entryColumn prog j) :
    i < j := by
  by_contra h'
  have : j ≤ i := by omega
  have hmono : entryColumn prog j ≤ entryColumn prog i := entryColumn_mono prog j i this
  omega

/-- Block `y` reads back its corridor cell on the header row. -/
theorem lastCellAt_block_header (prog : CMProgram) (y x : ℕ) (hy : y < prog.length)
    (ht : ∀ c : Fin 2, ∀ k : ℕ, (prog.getD y .halt = .decz c k ∨ prog.getD y .halt = .jump k) → k < prog.length)
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
      have hrange := blockBodyCells_row_range (prog.getD y .halt) (entryColumn prog y) (blockRow prog y) c hc
      have hle : blockRow prog y + blockHeight (prog.getD y .halt) ≤ playfieldHeight prog := by
        rw [playfieldHeight]
        exact blockRow_range_le prog y prog.length hy
      omega
    · intro c hc
      have hrange := blockBodyCells_row_range (prog.getD y .halt) (entryColumn prog y) (blockRow prog y) c hc
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
      simp only [hget, blockCorridorCells, corridorRowAt, corridorCells, lastCellAt, List.foldl_cons,
        List.foldl_nil, true_and, eq_self_iff_true, blockWidth]
      rw [Nat.mod_eq_of_lt hC]
      rw [Nat.mod_eq_of_lt hDk]
      rw [Nat.mod_eq_of_lt hx]
      by_cases hxE : x = entryColumn prog k
      · have hne : entryColumn prog y + 4 ≠ entryColumn prog k := by
          intro h
          -- entryColumn k = entryColumn y + 4 is strictly between entryColumn y and entryColumn (y+1)
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
        simp [hxE, hxC, eq_comm] -- no_squeeze: corridor readback
        all_goals intro h; exfalso; omega
      · simp [hxE, eq_comm] -- no_squeeze: corridor readback
        all_goals intro h; exfalso; omega
  | jump k =>
      have hk : k < prog.length := ht 0 k (Or.inr hget)
      have hDk : entryColumn prog k < playfieldWidth prog := by
        rw [playfieldWidth]
        exact entryColumn_strict_mono prog hk
      rw [hget] at hC
      simp only [blockWidth] at hC
      simp only [hget, blockCorridorCells, corridorRowAt, corridorCells, lastCellAt, List.foldl_cons,
        List.foldl_nil, true_and, eq_self_iff_true, blockWidth]
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
        simp [hxE, hxC, eq_comm] -- no_squeeze: corridor readback -- no_squeeze: corridor readback
        all_goals intro h; exfalso; omega
      · simp [hxE, eq_comm] -- no_squeeze: corridor readback
        all_goals intro h; exfalso; omega
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
    (ht : ∀ c : Fin 2, ∀ k : ℕ, (prog.getD y .halt = .decz c k ∨ prog.getD y .halt = .jump k) → k < prog.length)
    (hx : x < playfieldWidth prog) :
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
          exact lastCellAt_block_after_header prog y k x hyk' (by omega) hy hH (corridorRowAt prog x y)
        · have heq : y = k := by omega
          subst y
          rw [flatMap_range_succ, lastCellAt_append]
          rw [lastCellAt_flatMap_before_header prog k x hy hH]
          exact lastCellAt_block_header prog k x hy ht hx hH
  have hres := hmain prog.length (by omega) (by rfl)
  rw [hres]

end Completeness

end LeanFunge
