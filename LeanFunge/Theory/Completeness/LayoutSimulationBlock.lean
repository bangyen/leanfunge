/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanFunge.Theory.Completeness.LayoutCellMain
import LeanFunge.Theory.Completeness.LayoutCells
import LeanFunge.Theory.Completeness.LayoutCellRange
import LeanFunge.Theory.Completeness.LayoutHeaderRow
import LeanFunge.Theory.Completeness.LayoutSimulation
import LeanFunge.Theory.Run.Relational
import LeanFunge.Theory.Step
import Mathlib.Tactic

/-!
# The Halt Block on the Generated Playfield

The `halt` block stops the machine wherever it sits, including as the last
block of the playfield, where the cell lookups need `≤` bounds instead of the
strict ones that hold for interior blocks.

## Theorems

* `playfield_halt_get`: The cells of a `halt` block read back its body.
* `haltBlockRun`: A `halt` block stops the machine.
-/

namespace LeanFunge

namespace Completeness

/-- The body readback of a `halt` block, at any in-range offset. -/
lemma lastCellAt_halt_body (w h D y dx dy : ℕ) (hdx : dx < 2) (hdy : dy < 2)
    (hD : D < w) (hD1 : D + 1 < w) (hy : y < h) (hy1 : y + 1 < h) :
    lastCellAt w h ' ' [((D, y), '>'), ((D + 1, y), '@')] (D + dx) (y + dy)
      = blockBodyAt .halt dx dy := by
  have hmodD : D % w = D := Nat.mod_eq_of_lt hD
  have hmodD1 : (D + 1) % w = D + 1 := Nat.mod_eq_of_lt hD1
  have hmodDx : (D + dx) % w = D + dx := Nat.mod_eq_of_lt (by omega)
  have hmodY : y % h = y := Nat.mod_eq_of_lt hy
  have hmodYdy : (y + dy) % h = y + dy := Nat.mod_eq_of_lt (by omega)
  interval_cases dx <;> interval_cases dy
  <;> simp [blockBodyAt, lastCellAt, hmodD, hmodD1, hmodDx, hmodY, hmodYdy] -- no_squeeze: halt body

/-- The cells of a `halt` block read back its body, at any block position. -/
theorem playfield_halt_get (prog : CMProgram) (i : ℕ) (hi : i < prog.length)
    (hhalt : prog.getD i .halt = .halt) (dx dy : ℕ) (hdx : dx < 2) (hdy : dy < 2) :
    (playfieldOf prog).get (entryColumn prog i + dx) (blockRow prog i + dy)
      = blockBodyAt .halt dx dy := by
  let pw := playfieldWidth prog
  let ph := playfieldHeight prog
  have hW : entryColumn prog i + 2 ≤ pw := by
    dsimp [pw]
    rw [playfieldWidth]
    have hmono : entryColumn prog (i + 1) ≤ entryColumn prog prog.length :=
      entryColumn_mono prog (i + 1) prog.length (by omega)
    rw [entryColumn_succ] at hmono
    rw [hhalt] at hmono
    norm_num [blockWidth] at hmono
    omega
  have hH0 : blockRow prog i + 2 ≤ ph := by
    dsimp [ph]
    rw [playfieldHeight]
    have hmono : blockRow prog (i + 1) ≤ blockRow prog prog.length :=
      blockRow_mono prog (i := i + 1) (j := prog.length) (by omega)
    rw [blockRow_succ] at hmono
    rw [hhalt] at hmono
    norm_num [blockHeight] at hmono
    omega
  have hH : blockRow prog i + dy < ph := by omega
  rw [playfieldOf_get_eq_lastCellAt]
  unfold playfieldCells
  have hmain : ∀ k : ℕ, i < k → k ≤ prog.length →
      lastCellAt pw ph ' ' (List.flatMap (fun j => blockCellList prog j) (List.range k))
        (entryColumn prog i + dx) (blockRow prog i + dy)
        = blockBodyAt .halt dx dy := by
    intro k hik hkn
    induction k with
    | zero => omega
    | succ k ih =>
        by_cases hik' : i < k
        · have hprev := ih hik' (by omega)
          rw [flatMap_range_succ, lastCellAt_append, hprev]
          have hdyb : dy < blockHeight (prog.getD i .halt) := by
            rw [hhalt]
            norm_num [blockHeight]
            exact hdy
          exact lastCellAt_block_after prog i k dx dy (by omega) (by omega) hdyb hH
              (blockBodyAt .halt dx dy)
        · have heq : i = k := by omega
          subst i
          rw [flatMap_range_succ, lastCellAt_append]
          rw [lastCellAt_flatMap_before prog k (by omega) dx dy (by omega)]
          have hbody : lastCellAt pw ph ' ' (blockCellList prog k)
              (entryColumn prog k + dx) (blockRow prog k + dy) = blockBodyAt .halt dx dy := by
            rw [blockCellList_eq, hhalt]
            simp only [blockCorridorCells]
            have hD : entryColumn prog k < pw := by omega
            have hD1 : entryColumn prog k + 1 < pw := by omega
            have hy : blockRow prog k < ph := by omega
            have hy1 : blockRow prog k + 1 < ph := by omega
            simpa [blockBodyCells] using (lastCellAt_halt_body pw ph (entryColumn prog k)
              (blockRow prog k) dx dy hdx hdy hD hD1 hy hy1)
          exact hbody
  have hres := hmain prog.length (by omega) (by rfl)
  rw [hres]

/-- A `halt` block stops the machine, wherever it sits. -/
theorem haltBlockRun (prog : CMProgram) (i : ℕ) (hi : i < prog.length)
    (hhalt : prog.getD i .halt = .halt)
    (s : State (playfieldWidth prog) (playfieldHeight prog))
    (hsm : s.stringMode = false) (hpc : s.pc = (entryColumn prog i, blockRow prog i))
    (hgrid : s.grid = playfieldOf prog) :
    run 2 s = none := by
  have hW : entryColumn prog i + 1 < playfieldWidth prog := by
    have hle : entryColumn prog i + 2 ≤ playfieldWidth prog := by
      rw [playfieldWidth]
      have hmono : entryColumn prog (i + 1) ≤ entryColumn prog prog.length :=
        entryColumn_mono prog (i + 1) prog.length (by omega)
      rw [entryColumn_succ] at hmono
      rw [hhalt] at hmono
      norm_num [blockWidth] at hmono
      omega
    omega
  have hH : blockRow prog i < playfieldHeight prog := by
    have hle : blockRow prog i + 2 ≤ playfieldHeight prog := by
      rw [playfieldHeight]
      have hmono : blockRow prog (i + 1) ≤ blockRow prog prog.length :=
        blockRow_mono prog (i := i + 1) (j := prog.length) (by omega)
      rw [blockRow_succ] at hmono
      rw [hhalt] at hmono
      norm_num [blockHeight] at hmono
      omega
    omega
  have hc0 : s.grid.get (entryColumn prog i) (blockRow prog i) = '>' := by
    rw [hgrid]
    have h := playfield_halt_get prog i hi hhalt 0 0 (by norm_num) (by norm_num)
    simpa only [blockBodyAt] using h
  have hc1 : s.grid.get (entryColumn prog i + 1) (blockRow prog i) = '@' := by
    rw [hgrid]
    have h := playfield_halt_get prog i hi hhalt 1 0 (by norm_num) (by norm_num)
    simpa only [blockBodyAt] using h
  have h1 : run 1 s = some { s with dir := .right, pc := (entryColumn prog i + 1, blockRow prog i) } := by
    rw [show run 1 s = step s by rfl]
    unfold step
    have hdec : decodeChar '>' = .right := by unfold decodeChar; rfl
    simp only [hsm, hpc, hc0, hdec, stepState]
    rw [stepPos_right (playfieldWidth prog) (playfieldHeight prog) (entryColumn prog i) (blockRow prog i) hW hH]
  have h2 : run 1 { s with dir := .right, pc := (entryColumn prog i + 1, blockRow prog i) } = none := by
    rw [show run 1 { s with dir := .right, pc := (entryColumn prog i + 1, blockRow prog i) } = step { s with dir := .right, pc := (entryColumn prog i + 1, blockRow prog i) } by rfl]
    unfold step
    have hdec : decodeChar '@' = .halt := by unfold decodeChar; rfl
    simp only [hsm, hc1, hdec, stepState]
  have h12 : run (1 + 1) s = none := by
    exact run_append s { s with dir := .right, pc := (entryColumn prog i + 1, blockRow prog i) } none 1 1 h1 h2
  rw [show 2 = 1 + 1 by omega]
  exact h12

end Completeness

end LeanFunge
