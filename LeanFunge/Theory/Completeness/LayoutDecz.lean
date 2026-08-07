/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanFunge.Theory.Completeness.LayoutBlock
import LeanFunge.Theory.Completeness.LayoutCellMain
import LeanFunge.Theory.Run.Relational
import LeanFunge.Theory.Step
import Mathlib.Tactic

/-!
# The `decz` Test on the Generated Playfield

The `decz` test cells `> : digit %` of a block on the generated playfield leave the encoded pair on the stack with the remainder on top at the branch cell, for arbitrary programs.

## Theorems

* `deczBlock_prefix`: The `> : digit %` cells leave `[n % digit, n]` at the branch cell.
-/

namespace LeanFunge

namespace Completeness

/-- The `decz` test cells leave the remainder on top of the encoded pair at
    the branch cell. -/
theorem deczBlock_prefix (prog : CMProgram) (i : ℕ) (hi1 : i + 1 < prog.length)
    (hdecz : prog.getD i .halt = .decz c k)
    (s : State (playfieldWidth prog) (playfieldHeight prog))
    (hsm : s.stringMode = false) (hpc : s.pc = (entryColumn prog i, blockRow prog i))
    (hstack : s.stack = [n]) (hgrid : s.grid = playfieldOf prog) :
    run 4 s = some { s with
      dir := .right,
      stack := [n % counterVal c, n],
      pc := (entryColumn prog i + 4, blockRow prog i) } := by
  have hW : entryColumn prog i + blockWidth (prog.getD i .halt) < playfieldWidth prog := by
    rw [playfieldWidth]
    rw [← entryColumn_succ]
    exact entryColumn_strict_mono prog hi1
  have hH : blockRow prog i + blockHeight (prog.getD i .halt) < playfieldHeight prog := by
    rw [playfieldHeight]
    rw [← blockRow_succ]
    exact blockRow_strict_mono prog hi1
  rw [hdecz] at hW
  rw [hdecz] at hH
  simp only [blockWidth] at hW
  simp only [blockHeight] at hH
  have hc0 : s.grid.get (entryColumn prog i) (blockRow prog i) = '>' := by
    rw [hgrid]
    have hpb := playfield_block_get prog i hi1 0 0 (by exact Nat.zero_le _) (by exact blockHeight_pos _)
    rw [hdecz] at hpb
    simpa only [blockBodyAt] using hpb
  have hc1 : s.grid.get (entryColumn prog i + 1) (blockRow prog i) = ':' := by
    rw [hgrid]
    have hpb := playfield_block_get prog i hi1 1 0 (by rw [hdecz]; norm_num [blockWidth]) (by exact blockHeight_pos _)
    rw [hdecz] at hpb
    simpa only [blockBodyAt] using hpb
  have hc2 : s.grid.get (entryColumn prog i + 2) (blockRow prog i) = counterDigit c := by
    rw [hgrid]
    have hpb := playfield_block_get prog i hi1 2 0 (by rw [hdecz]; norm_num [blockWidth]) (by exact blockHeight_pos _)
    rw [hdecz] at hpb
    simpa only [blockBodyAt] using hpb
  have hc3 : s.grid.get (entryColumn prog i + 3) (blockRow prog i) = '%' := by
    rw [hgrid]
    have hpb := playfield_block_get prog i hi1 3 0 (by rw [hdecz]; norm_num [blockWidth]) (by exact blockHeight_pos _)
    rw [hdecz] at hpb
    simpa only [blockBodyAt] using hpb
  have h1 : run 1 s = some { s with dir := .right, pc := (entryColumn prog i + 1, blockRow prog i) } := by
    rw [show run 1 s = step s by rfl]
    unfold step
    have hdec : decodeChar '>' = .right := by unfold decodeChar; rfl
    simp only [hsm, hpc, hc0, hdec, stepState]
    rw [stepPos_right (playfieldWidth prog) (playfieldHeight prog) (entryColumn prog i) (blockRow prog i) (by omega) (by omega)]
  have h2 : run 1 { s with dir := .right, pc := (entryColumn prog i + 1, blockRow prog i) } =
      some { s with dir := .right, stack := [n, n], pc := (entryColumn prog i + 2, blockRow prog i) } := by
    rw [show run 1 { s with dir := .right, pc := (entryColumn prog i + 1, blockRow prog i) } = step { s with dir := .right, pc := (entryColumn prog i + 1, blockRow prog i) } by rfl]
    unfold step
    have hdec : decodeChar ':' = .dup := by unfold decodeChar; rfl
    simp only [hsm, hc1, hdec, stepState, Stack.dup]
    rw [stepPos_right (playfieldWidth prog) (playfieldHeight prog) (entryColumn prog i + 1) (blockRow prog i) (by omega) (by omega)]
    simp only [hstack, Stack.dup]
  have h3 : run 1 { s with dir := .right, stack := [n, n], pc := (entryColumn prog i + 2, blockRow prog i) } =
      some { s with dir := .right, stack := [counterVal c, n, n], pc := (entryColumn prog i + 3, blockRow prog i) } := by
    rw [show run 1 { s with dir := .right, stack := [n, n], pc := (entryColumn prog i + 2, blockRow prog i) } = step { s with dir := .right, stack := [n, n], pc := (entryColumn prog i + 2, blockRow prog i) } by rfl]
    unfold step
    have hdec : decodeChar (counterDigit c) = .push (counterVal c) := by
      fin_cases c <;> rfl
    simp only [hsm, hc2, hdec, stepState, Stack.push]
    rw [stepPos_right (playfieldWidth prog) (playfieldHeight prog) (entryColumn prog i + 2) (blockRow prog i) (by omega) (by omega)]
  have h4 : run 1 { s with dir := .right, stack := [counterVal c, n, n], pc := (entryColumn prog i + 3, blockRow prog i) } =
      some { s with dir := .right, stack := [n % counterVal c, n], pc := (entryColumn prog i + 4, blockRow prog i) } := by
    rw [show run 1 { s with dir := .right, stack := [counterVal c, n, n], pc := (entryColumn prog i + 3, blockRow prog i) } = step { s with dir := .right, stack := [counterVal c, n, n], pc := (entryColumn prog i + 3, blockRow prog i) } by rfl]
    unfold step
    have hdec : decodeChar '%' = .mod := by unfold decodeChar; rfl
    simp only [hsm, hc3, hdec, stepState, Stack.applyBinary]
    rw [stepPos_right (playfieldWidth prog) (playfieldHeight prog) (entryColumn prog i + 3) (blockRow prog i) (by omega) (by omega)]
  have h12 : run (1 + 1) s = some { s with dir := .right, stack := [n, n], pc := (entryColumn prog i + 2, blockRow prog i) } := by
    exact run_append s { s with dir := .right, pc := (entryColumn prog i + 1, blockRow prog i) }
      (some { s with dir := .right, stack := [n, n], pc := (entryColumn prog i + 2, blockRow prog i) }) 1 1 h1 h2
  have h123 : run (1 + 1 + 1) s = some { s with dir := .right, stack := [counterVal c, n, n], pc := (entryColumn prog i + 3, blockRow prog i) } := by
    exact run_append s { s with dir := .right, stack := [n, n], pc := (entryColumn prog i + 2, blockRow prog i) }
      (some { s with dir := .right, stack := [counterVal c, n, n], pc := (entryColumn prog i + 3, blockRow prog i) }) (1 + 1) 1 h12 h3
  have h1234 : run (1 + 1 + 1 + 1) s =
      some { s with dir := .right, stack := [n % counterVal c, n], pc := (entryColumn prog i + 4, blockRow prog i) } := by
    exact run_append s { s with dir := .right, stack := [counterVal c, n, n], pc := (entryColumn prog i + 3, blockRow prog i) }
      (some { s with dir := .right, stack := [n % counterVal c, n], pc := (entryColumn prog i + 4, blockRow prog i) }) (1 + 1 + 1) 1 h123 h4
  rw [show 4 = 1 + 1 + 1 + 1 by omega]
  rw [h1234]

end Completeness

end LeanFunge
