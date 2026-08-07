/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanFunge.Theory.Completeness.LayoutBlock
import LeanFunge.Theory.Completeness.LayoutCellMain
import LeanFunge.Theory.Step
import LeanFunge.Theory.Run.Relational
import Mathlib.Tactic

/-!
# The Jump and Halt Blocks on the Generated Playfield

A `jump` block of the generated playfield sends the pointer up its corridor column, and a `halt` block stops the machine, for arbitrary programs.

## Theorems

* `stepPos_up`: Moving up one cell does not wrap when the cell is inside the playfield.
* `jumpBlock_run`: A `jump` block sends the pointer up its corridor column.
* `haltBlock_run`: A `halt` block stops the machine.
-/

namespace LeanFunge

namespace Completeness

theorem stepPos_up (w h : ℕ) (p y : ℕ) (hp : p < w) (hy0 : 0 < y) (hy : y < h) :
    stepPos w h Direction.up (p, y) = (p, y - 1) := by
  unfold stepPos
  rw [Nat.mod_eq_of_lt hp]
  have hmod : (y + h - 1) % h = y - 1 := by
    have hsub : y + h - 1 = (y - 1) + h := by omega
    rw [hsub]
    have hyl : y - 1 < h := by omega
    rw [Nat.add_mod_right, Nat.mod_eq_of_lt hyl]
  rw [hmod]

/-- A `jump` block sends the pointer up its corridor column. -/
theorem jumpBlock_run (prog : CMProgram) (i : ℕ) (hi1 : i + 1 < prog.length)
    (hjump : prog.getD i .halt = .jump k)
    (s : State (playfieldWidth prog) (playfieldHeight prog))
    (hsm : s.stringMode = false) (hpc : s.pc = (entryColumn prog i, blockRow prog i))
    (hdir : s.dir = .right) (hgrid : s.grid = playfieldOf prog) :
    run 2 s = some { s with pc := (entryColumn prog i + 1, blockRow prog i - 1), dir := .up } := by
  have hW : entryColumn prog i + blockWidth (prog.getD i .halt) < playfieldWidth prog := by
    rw [playfieldWidth]
    rw [← entryColumn_succ]
    exact entryColumn_strict_mono prog hi1
  have hH : blockRow prog i + blockHeight (prog.getD i .halt) < playfieldHeight prog := by
    rw [playfieldHeight]
    rw [← blockRow_succ]
    exact blockRow_strict_mono prog hi1
  rw [hjump] at hW
  rw [hjump] at hH
  simp only [blockWidth] at hW
  simp only [blockHeight] at hH
  have hy0 : 0 < blockRow prog i := by
    have hle : prog.length ≤ blockRow prog i := blockRow_ge_length prog i
    omega
  have hc0 : s.grid.get (entryColumn prog i) (blockRow prog i) = '>' := by
    rw [hgrid]
    have hpb := playfield_block_get prog i hi1 0 0 (by exact Nat.zero_le _) (by exact blockHeight_pos _)
    rw [hjump] at hpb
    simpa only [blockBodyAt] using hpb
  have hc1 : s.grid.get (entryColumn prog i + 1) (blockRow prog i) = '^' := by
    rw [hgrid]
    have hpb := playfield_block_get prog i hi1 1 0 (by rw [hjump]; norm_num [blockWidth]) (by exact blockHeight_pos _)
    rw [hjump] at hpb
    simpa only [blockBodyAt] using hpb
  have h1 : run 1 s = some { s with pc := (entryColumn prog i + 1, blockRow prog i) } := by
    rw [show run 1 s = step s by rfl]
    unfold step
    have hdec : decodeChar '>' = .right := by unfold decodeChar; rfl
    simp only [hsm, hpc, hc0, hdec, stepState]
    rw [hdir, stepPos_right (playfieldWidth prog) (playfieldHeight prog) (entryColumn prog i) (blockRow prog i) (by omega) (by omega)]
  have h2 : run 1 { s with pc := (entryColumn prog i + 1, blockRow prog i) } =
      some { s with pc := (entryColumn prog i + 1, blockRow prog i - 1), dir := .up } := by
    rw [show run 1 { s with pc := (entryColumn prog i + 1, blockRow prog i) } = step { s with pc := (entryColumn prog i + 1, blockRow prog i) } by rfl]
    unfold step
    have hdec : decodeChar '^' = .up := by unfold decodeChar; rfl
    simp only [hsm, hc1, hdec, stepState]
    rw [stepPos_up (playfieldWidth prog) (playfieldHeight prog) (entryColumn prog i + 1) (blockRow prog i) (by omega) (by omega) (by omega)]
  have h12 : run (1 + 1) s = some { s with pc := (entryColumn prog i + 1, blockRow prog i - 1), dir := .up } := by
    exact run_append s { s with pc := (entryColumn prog i + 1, blockRow prog i) }
      (some { s with pc := (entryColumn prog i + 1, blockRow prog i - 1), dir := .up }) 1 1 h1 h2
  rw [show 2 = 1 + 1 by omega]
  rw [h12]

/-- A `halt` block stops the machine. -/
theorem haltBlock_run (prog : CMProgram) (i : ℕ) (hi1 : i + 1 < prog.length)
    (hhalt : prog.getD i .halt = .halt)
    (s : State (playfieldWidth prog) (playfieldHeight prog))
    (hsm : s.stringMode = false) (hpc : s.pc = (entryColumn prog i, blockRow prog i))
    (hdir : s.dir = .right) (hgrid : s.grid = playfieldOf prog) :
    run 2 s = none := by
  have hW : entryColumn prog i + blockWidth (prog.getD i .halt) < playfieldWidth prog := by
    rw [playfieldWidth]
    rw [← entryColumn_succ]
    exact entryColumn_strict_mono prog hi1
  have hH : blockRow prog i + blockHeight (prog.getD i .halt) < playfieldHeight prog := by
    rw [playfieldHeight]
    rw [← blockRow_succ]
    exact blockRow_strict_mono prog hi1
  rw [hhalt] at hW
  rw [hhalt] at hH
  simp only [blockWidth] at hW
  simp only [blockHeight] at hH
  have hc0 : s.grid.get (entryColumn prog i) (blockRow prog i) = '>' := by
    rw [hgrid]
    have hpb := playfield_block_get prog i hi1 0 0 (by exact Nat.zero_le _) (by exact blockHeight_pos _)
    rw [hhalt] at hpb
    simpa only [blockBodyAt] using hpb
  have hc1 : s.grid.get (entryColumn prog i + 1) (blockRow prog i) = '@' := by
    rw [hgrid]
    have hpb := playfield_block_get prog i hi1 1 0 (by rw [hhalt]; norm_num [blockWidth]) (by exact blockHeight_pos _)
    rw [hhalt] at hpb
    simpa only [blockBodyAt] using hpb
  have h1 : run 1 s = some { s with pc := (entryColumn prog i + 1, blockRow prog i) } := by
    rw [show run 1 s = step s by rfl]
    unfold step
    have hdec : decodeChar '>' = .right := by unfold decodeChar; rfl
    simp only [hsm, hpc, hc0, hdec, stepState]
    rw [hdir, stepPos_right (playfieldWidth prog) (playfieldHeight prog) (entryColumn prog i) (blockRow prog i) (by omega) (by omega)]
  have h2 : run 1 { s with pc := (entryColumn prog i + 1, blockRow prog i) } = none := by
    rw [show run 1 { s with pc := (entryColumn prog i + 1, blockRow prog i) } = step { s with pc := (entryColumn prog i + 1, blockRow prog i) } by rfl]
    unfold step
    have hdec : decodeChar '@' = .halt := by unfold decodeChar; rfl
    simp only [hsm, hc1, hdec, stepState]
  have h12 : run (1 + 1) s = none := by
    exact run_append s { s with pc := (entryColumn prog i + 1, blockRow prog i) } none 1 1 h1 h2
  rw [show 2 = 1 + 1 by omega]
  rw [h12]

end Completeness

end LeanFunge
