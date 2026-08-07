/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanFunge.Theory.Completeness.LayoutBlock
import LeanFunge.Theory.Completeness.LayoutCellMain
import LeanFunge.Theory.Completeness.LayoutJumpBlock
import LeanFunge.Theory.Run.Relational
import LeanFunge.Theory.Step
import Mathlib.Tactic

/-!
# The `decz` Branches on the Generated Playfield

The `|` branch cell of a `decz` block sends the pointer down through the decrement cells `digit / > v` on an even encoding (counter positive), dividing the value and exiting down the fall-through column, or up the corridor column on an odd encoding (counter zero), with the value unchanged.

## Theorems

* `deczBlock_decrement`: On an even encoding the block divides the value and exits down the fall-through column.
* `deczBlock_jump`: On an odd encoding the block sends the pointer up the corridor column with the value unchanged.
-/

namespace LeanFunge

namespace Completeness

theorem deczBlock_decrement (prog : CMProgram) (i : ℕ) (hi1 : i + 1 < prog.length)
    (hdecz : prog.getD i .halt = .decz c k)
    (s : State (playfieldWidth prog) (playfieldHeight prog))
    (hsm : s.stringMode = false) (hpc : s.pc = (entryColumn prog i + 4, blockRow prog i))
    (hstack : s.stack = [n % counterVal c, n])
    (hgrid : s.grid = playfieldOf prog) (hz : n % counterVal c = 0) :
    run 5 s = some { s with
      stack := [n / counterVal c],
      pc := (entryColumn prog i + 5, blockRow prog i + 4),
      dir := .down } := by
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
  have hy0 : 0 < blockRow prog i := by
    have hle : prog.length ≤ blockRow prog i := blockRow_ge_length prog i
    omega
  have hc0 : s.grid.get (entryColumn prog i + 4) (blockRow prog i) = '|' := by
    rw [hgrid]
    have hpb := playfield_block_get prog i hi1 4 0 (by rw [hdecz]; norm_num [blockWidth]) (by exact blockHeight_pos _)
    rw [hdecz] at hpb
    simpa only [blockBodyAt] using hpb
  have hc1 : s.grid.get (entryColumn prog i + 4) (blockRow prog i + 1) = counterDigit c := by
    rw [hgrid]
    have hpb := playfield_block_get prog i hi1 4 1 (by rw [hdecz]; norm_num [blockWidth]) (by rw [hdecz]; norm_num [blockHeight])
    rw [hdecz] at hpb
    simpa only [blockBodyAt] using hpb
  have hc2 : s.grid.get (entryColumn prog i + 4) (blockRow prog i + 2) = '/' := by
    rw [hgrid]
    have hpb := playfield_block_get prog i hi1 4 2 (by rw [hdecz]; norm_num [blockWidth]) (by rw [hdecz]; norm_num [blockHeight])
    rw [hdecz] at hpb
    simpa only [blockBodyAt] using hpb
  have hc3 : s.grid.get (entryColumn prog i + 4) (blockRow prog i + 3) = '>' := by
    rw [hgrid]
    have hpb := playfield_block_get prog i hi1 4 3 (by rw [hdecz]; norm_num [blockWidth]) (by rw [hdecz]; norm_num [blockHeight])
    rw [hdecz] at hpb
    simpa only [blockBodyAt] using hpb
  have hc4 : s.grid.get (entryColumn prog i + 5) (blockRow prog i + 3) = 'v' := by
    rw [hgrid]
    have hpb := playfield_block_get prog i hi1 5 3 (by rw [hdecz]; norm_num [blockWidth]) (by rw [hdecz]; norm_num [blockHeight])
    rw [hdecz] at hpb
    simpa only [blockBodyAt] using hpb
  have h1 : run 1 s = some { s with stack := [n], pc := (entryColumn prog i + 4, blockRow prog i + 1), dir := .down } := by
    rw [show run 1 s = step s by rfl]
    rw [step_chooseV s hsm (by simpa only [hpc] using hc0) (n % counterVal c) [n] hstack]
    simp only [hpc, hz, if_pos]
    rw [stepPos_down (playfieldWidth prog) (playfieldHeight prog) (entryColumn prog i + 4) (blockRow prog i) (by omega) (by omega)]
  have h2 : run 1 { s with stack := [n], pc := (entryColumn prog i + 4, blockRow prog i + 1), dir := .down } =
      some { s with stack := [counterVal c, n], pc := (entryColumn prog i + 4, blockRow prog i + 2), dir := .down } := by
    rw [show run 1 { s with stack := [n], pc := (entryColumn prog i + 4, blockRow prog i + 1), dir := .down } = step { s with stack := [n], pc := (entryColumn prog i + 4, blockRow prog i + 1), dir := .down } by rfl]
    unfold step
    have hdec : decodeChar (counterDigit c) = .push (counterVal c) := by
      fin_cases c <;> rfl
    simp only [hsm, hc1, hdec, stepState, Stack.push]
    rw [stepPos_down (playfieldWidth prog) (playfieldHeight prog) (entryColumn prog i + 4) (blockRow prog i + 1) (by omega) (by omega)]
  have h3 : run 1 { s with stack := [counterVal c, n], pc := (entryColumn prog i + 4, blockRow prog i + 2), dir := .down } =
      some { s with stack := [n / counterVal c], pc := (entryColumn prog i + 4, blockRow prog i + 3), dir := .down } := by
    rw [show run 1 { s with stack := [counterVal c, n], pc := (entryColumn prog i + 4, blockRow prog i + 2), dir := .down } = step { s with stack := [counterVal c, n], pc := (entryColumn prog i + 4, blockRow prog i + 2), dir := .down } by rfl]
    unfold step
    have hdec : decodeChar '/' = .div := by unfold decodeChar; rfl
    simp only [hsm, hc2, hdec, stepState, Stack.applyBinary]
    rw [stepPos_down (playfieldWidth prog) (playfieldHeight prog) (entryColumn prog i + 4) (blockRow prog i + 2) (by omega) (by omega)]
  have h4 : run 1 { s with stack := [n / counterVal c], pc := (entryColumn prog i + 4, blockRow prog i + 3), dir := .down } =
      some { s with stack := [n / counterVal c], pc := (entryColumn prog i + 5, blockRow prog i + 3), dir := .right } := by
    rw [show run 1 { s with stack := [n / counterVal c], pc := (entryColumn prog i + 4, blockRow prog i + 3), dir := .down } = step { s with stack := [n / counterVal c], pc := (entryColumn prog i + 4, blockRow prog i + 3), dir := .down } by rfl]
    unfold step
    have hdec : decodeChar '>' = .right := by unfold decodeChar; rfl
    simp only [hsm, hc3, hdec, stepState]
    rw [stepPos_right (playfieldWidth prog) (playfieldHeight prog) (entryColumn prog i + 4) (blockRow prog i + 3) (by omega) (by omega)]
  have h5 : run 1 { s with stack := [n / counterVal c], pc := (entryColumn prog i + 5, blockRow prog i + 3), dir := .right } =
      some { s with stack := [n / counterVal c], pc := (entryColumn prog i + 5, blockRow prog i + 4), dir := .down } := by
    rw [show run 1 { s with stack := [n / counterVal c], pc := (entryColumn prog i + 5, blockRow prog i + 3), dir := .right } = step { s with stack := [n / counterVal c], pc := (entryColumn prog i + 5, blockRow prog i + 3), dir := .right } by rfl]
    unfold step
    have hdec : decodeChar 'v' = .down := by unfold decodeChar; rfl
    simp only [hsm, hc4, hdec, stepState]
    rw [stepPos_down (playfieldWidth prog) (playfieldHeight prog) (entryColumn prog i + 5) (blockRow prog i + 3) (by omega) (by omega)]
  have h12 : run (1 + 1) s = some { s with stack := [counterVal c, n], pc := (entryColumn prog i + 4, blockRow prog i + 2), dir := .down } := by
    exact run_append s { s with stack := [n], pc := (entryColumn prog i + 4, blockRow prog i + 1), dir := .down }
      (some { s with stack := [counterVal c, n], pc := (entryColumn prog i + 4, blockRow prog i + 2), dir := .down }) 1 1 h1 h2
  have h123 : run (1 + 1 + 1) s = some { s with stack := [n / counterVal c], pc := (entryColumn prog i + 4, blockRow prog i + 3), dir := .down } := by
    exact run_append s { s with stack := [counterVal c, n], pc := (entryColumn prog i + 4, blockRow prog i + 2), dir := .down }
      (some { s with stack := [n / counterVal c], pc := (entryColumn prog i + 4, blockRow prog i + 3), dir := .down }) (1 + 1) 1 h12 h3
  have h1234 : run (1 + 1 + 1 + 1) s = some { s with stack := [n / counterVal c], pc := (entryColumn prog i + 5, blockRow prog i + 3), dir := .right } := by
    exact run_append s { s with stack := [n / counterVal c], pc := (entryColumn prog i + 4, blockRow prog i + 3), dir := .down }
      (some { s with stack := [n / counterVal c], pc := (entryColumn prog i + 5, blockRow prog i + 3), dir := .right }) (1 + 1 + 1) 1 h123 h4
  have h12345 : run (1 + 1 + 1 + 1 + 1) s =
      some { s with stack := [n / counterVal c], pc := (entryColumn prog i + 5, blockRow prog i + 4), dir := .down } := by
    exact run_append s { s with stack := [n / counterVal c], pc := (entryColumn prog i + 5, blockRow prog i + 3), dir := .right }
      (some { s with stack := [n / counterVal c], pc := (entryColumn prog i + 5, blockRow prog i + 4), dir := .down }) (1 + 1 + 1 + 1) 1 h1234 h5
  rw [show 5 = 1 + 1 + 1 + 1 + 1 by omega]
  rw [h12345]

/-- On an odd encoding the `decz` block sends the pointer up the corridor
    column with the value unchanged. -/
theorem deczBlock_jump (prog : CMProgram) (i : ℕ) (hi1 : i + 1 < prog.length)
    (hdecz : prog.getD i .halt = .decz c k)
    (s : State (playfieldWidth prog) (playfieldHeight prog))
    (hsm : s.stringMode = false) (hpc : s.pc = (entryColumn prog i + 4, blockRow prog i))
    (hstack : s.stack = [n % counterVal c, n])
    (hgrid : s.grid = playfieldOf prog) (hnz : n % counterVal c ≠ 0) :
    run 1 s = some { s with
      stack := [n],
      pc := (entryColumn prog i + 4, blockRow prog i - 1),
      dir := .up } := by
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
  have hy0 : 0 < blockRow prog i := by
    have hle : prog.length ≤ blockRow prog i := blockRow_ge_length prog i
    omega
  have hc0 : s.grid.get (entryColumn prog i + 4) (blockRow prog i) = '|' := by
    rw [hgrid]
    have hpb := playfield_block_get prog i hi1 4 0 (by rw [hdecz]; norm_num [blockWidth]) (by exact blockHeight_pos _)
    rw [hdecz] at hpb
    simpa only [blockBodyAt] using hpb
  rw [show run 1 s = step s by rfl]
  rw [step_chooseV s hsm (by simpa only [hpc] using hc0) (n % counterVal c) [n] hstack]
  simp only [hpc, hnz, if_false]
  rw [stepPos_up (playfieldWidth prog) (playfieldHeight prog) (entryColumn prog i + 4) (blockRow prog i) (by omega) (by omega) (by omega)]

end Completeness

end LeanFunge
