/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanFunge.Theory.Completeness.LayoutBlock
import LeanFunge.Theory.Completeness.LayoutCells
import LeanFunge.Theory.Completeness.LayoutCorridor
import LeanFunge.Theory.Completeness.LayoutHeader
import LeanFunge.Theory.Completeness.LayoutRowAt
import Mathlib.Tactic

/-!
# The Corridor Row Cleanliness

A jump edge's branch column is one column before the next entry, so it holds no
block cell at all: the corridor's up column is clean. This module proves the
row-finding and cell lookups that show the up segment of a corridor is a run
of spaces.

## Main definitions

* `branchColumn`: The branch column of a block.

## Theorems

* `blockRow_find`: Every row in the block region lies in a block's row range.
* `blockBodyAt_exit_or_space`: The cells on a block's exit column are a `v` or a space.
* `corridorUp_cell`: The cells on the branch column above a block are spaces.
-/

namespace LeanFunge

namespace Completeness

/-- The branch column of block `i`: the corridor's up column, one column
    before the next entry. -/
abbrev branchColumn (prog : CMProgram) (i : ℕ) : ℕ :=
  entryColumn prog i + blockWidth (prog.getD i .halt) - 1

/-- Every row of the block region lies in some block's row range. -/
theorem blockRow_find (prog : CMProgram) (r : ℕ) (hr0 : prog.length ≤ r)
    (hr : r < playfieldHeight prog) :
    ∃ j : ℕ, j < prog.length ∧ blockRow prog j ≤ r ∧ r < blockRow prog j + blockHeight (prog.getD j .halt) := by
  have hlen0 : 0 < prog.length := by
    by_contra h
    have hz : prog.length = 0 := by omega
    have h0 : playfieldHeight prog = 0 := by
      unfold playfieldHeight
      simpa [blockRow, hz] -- no_squeeze: corridor route
    omega
  have hfirst : ∃ j : ℕ, j ≤ prog.length ∧ r < blockRow prog j := by
    refine ⟨prog.length, by rfl, ?_⟩
    simpa [playfieldHeight] using hr -- no_squeeze: corridor route
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
    have hjr0 : r < blockRow prog 0 := by simpa [hj0] using hjr -- no_squeeze: corridor route
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
      _ = blockRow prog (j - 1) + blockHeight (prog.getD (j - 1) .halt) := blockRow_succ prog (j - 1)
  rw [hsucc] at hjr
  omega

/-- The cells on a block's exit column (offset `blockWidth`) are a `v` or a
    space. -/
theorem blockBodyAt_exit_or_space (instr : CMInstr) (dy : ℕ) (hdy : dy < blockHeight instr) :
    blockBodyAt instr (blockWidth instr) dy = ' ' ∨ blockBodyAt instr (blockWidth instr) dy = 'v' := by
  cases instr with
  | inc c0 =>
      fin_cases c0 <;> by_cases h : dy = 0 <;> simp [blockBodyAt, blockWidth, h] -- no_squeeze: corridor route
  | decz c0 _ =>
      fin_cases c0 <;> by_cases h : dy = 3 <;> simp [blockBodyAt, blockWidth, h] -- no_squeeze: corridor route
  | jump _ =>
      simp [blockBodyAt, blockWidth] -- no_squeeze: corridor route
  | halt =>
      simp [blockBodyAt, blockWidth] -- no_squeeze: corridor route

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
  · have hcell := playfield_header_get prog C r (by omega) (fun c k hk => hwell r (by omega) c k hk) hCW
    rw [hcell]
    cases hget : prog.getD r .halt with
    | decz c k' =>
        have hCne : C ≠ entryColumn prog r + 4 := by
          intro h
          have hmono : entryColumn prog (i + 1) ≤ entryColumn prog r := entryColumn_mono prog (i + 1) r (by omega)
          rw [entryColumn_succ] at hmono
          rw [hC] at h
          omega
        have hCne_k : C ≠ entryColumn prog k' := hCnotentry k'
        unfold corridorRowAt
        rw [hget]
        simp [hCne, hCne_k] -- no_squeeze: corridor route
    | jump k' =>
        have hCne : C ≠ entryColumn prog r + 1 := by
          intro h
          have hmono : entryColumn prog (i + 1) ≤ entryColumn prog r := entryColumn_mono prog (i + 1) r (by omega)
          rw [entryColumn_succ] at hmono
          rw [hC] at h
          omega
        have hCne_k : C ≠ entryColumn prog k' := hCnotentry k'
        unfold corridorRowAt
        rw [hget]
        simp [hCne, hCne_k] -- no_squeeze: corridor route
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
    rw [blockBodyAt_out (prog.getD j .halt) (C - entryColumn prog j) (r - blockRow prog j) hdx] at hcell
    simpa using hcell -- no_squeeze: corridor route

end Completeness

end LeanFunge
