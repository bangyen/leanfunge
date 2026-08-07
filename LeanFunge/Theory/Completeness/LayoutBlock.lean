/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanFunge.Theory.Completeness.LayoutCellMain
import LeanFunge.Theory.Completeness.Routing
import LeanFunge.Theory.Run.Relational
import LeanFunge.Theory.Step
import Mathlib.Tactic

/-!
# The Increment Block on the Generated Playfield

An `inc` block of the generated playfield executes its instruction: the body cells read back exactly the block's snippet, and the instruction pointer steps through them. Running from a block's entry multiplies the stack top by the counter digit and exits down the fall-through column, for arbitrary programs.

## Main definitions

* `counterVal`: The integer that an `inc`/`decz` block pushes or tests with.

## Theorems

* `stepPos_right`: Moving right one cell does not wrap when the cell is inside the playfield.
* `stepPos_down`: Moving down one cell does not wrap when the cell is inside the playfield.
* `incBlock_run`: An `inc` block multiplies the stack top by its counter digit and exits down.
-/

namespace LeanFunge

namespace Completeness

/-- The integer that an `inc`/`decz` block pushes or tests with: `2` for
    counter 1, `3` for counter 2. -/
def counterVal (c : Fin 2) : Int := if c = 0 then 2 else 3

/-- Moving right one cell does not wrap when the cell is inside the playfield. -/
theorem stepPos_right (w h : ℕ) (p y : ℕ) (hp : p + 1 < w) (hy : y < h) :
    stepPos w h Direction.right (p, y) = (p + 1, y) := by
  unfold stepPos
  rw [Nat.mod_eq_of_lt hp]
  rw [Nat.mod_eq_of_lt hy]

/-- Moving down one cell does not wrap when the cell is inside the playfield. -/
theorem stepPos_down (w h : ℕ) (p y : ℕ) (hp : p < w) (hy : y + 1 < h) :
    stepPos w h Direction.down (p, y) = (p, y + 1) := by
  unfold stepPos
  rw [Nat.mod_eq_of_lt hp]
  rw [Nat.mod_eq_of_lt hy]

/-- An `inc` block multiplies the stack top by its counter digit and exits
    down its fall-through column. -/
theorem incBlock_run (prog : CMProgram) (i : ℕ) (hi1 : i + 1 < prog.length)
    (hinc : prog.getD i .halt = .inc c)
    (s : State (playfieldWidth prog) (playfieldHeight prog))
    (hsm : s.stringMode = false) (hpc : s.pc = (entryColumn prog i, blockRow prog i))
    (hstack : s.stack = [n]) (hgrid : s.grid = playfieldOf prog) :
    run 4 s = some { s with
      stack := [n * counterVal c],
      pc := (entryColumn prog (i + 1), blockRow prog i + 1),
      dir := .down } := by
  have hW : entryColumn prog i + blockWidth (prog.getD i .halt) < playfieldWidth prog := by
    rw [playfieldWidth]
    rw [← entryColumn_succ]
    exact entryColumn_strict_mono prog hi1
  have hH : blockRow prog i + blockHeight (prog.getD i .halt) < playfieldHeight prog := by
    rw [playfieldHeight]
    rw [← blockRow_succ]
    exact blockRow_strict_mono prog hi1
  rw [hinc] at hW
  rw [hinc] at hH
  simp only [blockWidth] at hW
  simp only [blockHeight] at hH
  have hc0 : s.grid.get (entryColumn prog i) (blockRow prog i) = '>' := by
    rw [hgrid]
    have hpb := playfield_block_get prog i hi1 0 0 (by exact Nat.zero_le _) (by exact blockHeight_pos _)
    rw [hinc] at hpb
    simpa only [blockBodyAt] using hpb
  have hc1 : s.grid.get (entryColumn prog i + 1) (blockRow prog i) = counterDigit c := by
    rw [hgrid]
    have hpb := playfield_block_get prog i hi1 1 0 (by rw [hinc]; norm_num [blockWidth]) (by exact blockHeight_pos _)
    rw [hinc] at hpb
    simpa only [blockBodyAt] using hpb
  have hc2 : s.grid.get (entryColumn prog i + 2) (blockRow prog i) = '*' := by
    rw [hgrid]
    have hpb := playfield_block_get prog i hi1 2 0 (by rw [hinc]; norm_num [blockWidth]) (by exact blockHeight_pos _)
    rw [hinc] at hpb
    simpa only [blockBodyAt] using hpb
  have hc3 : s.grid.get (entryColumn prog i + 3) (blockRow prog i) = 'v' := by
    rw [hgrid]
    have hpb := playfield_block_get prog i hi1 3 0 (by rw [hinc]; norm_num [blockWidth]) (by exact blockHeight_pos _)
    rw [hinc] at hpb
    simpa only [blockBodyAt] using hpb
  have h1 : run 1 s = some { s with dir := .right, pc := (entryColumn prog i + 1, blockRow prog i) } := by
    rw [show run 1 s = step s by rfl]
    unfold step
    have hdec : decodeChar '>' = .right := by unfold decodeChar; rfl
    simp only [hsm, hpc, hc0, hdec, stepState]
    rw [stepPos_right (playfieldWidth prog) (playfieldHeight prog) (entryColumn prog i) (blockRow prog i) (by omega) (by omega)]
  have h2 : run 1 { s with dir := .right, pc := (entryColumn prog i + 1, blockRow prog i) } =
      some { s with dir := .right, stack := [counterVal c, n], pc := (entryColumn prog i + 2, blockRow prog i) } := by
    rw [show run 1 { s with dir := .right, pc := (entryColumn prog i + 1, blockRow prog i) } = step { s with dir := .right, pc := (entryColumn prog i + 1, blockRow prog i) } by rfl]
    unfold step
    have hdec : decodeChar (counterDigit c) = .push (counterVal c) := by
      fin_cases c <;> rfl
    simp only [hsm, hc1, hdec, stepState]
    rw [stepPos_right (playfieldWidth prog) (playfieldHeight prog) (entryColumn prog i + 1) (blockRow prog i) (by omega) (by omega)]
    simp only [hstack, Stack.push]
  have h3 : run 1 { s with dir := .right, stack := [counterVal c, n], pc := (entryColumn prog i + 2, blockRow prog i) } =
      some { s with dir := .right, stack := [n * counterVal c], pc := (entryColumn prog i + 3, blockRow prog i) } := by
    rw [show run 1 { s with dir := .right, stack := [counterVal c, n], pc := (entryColumn prog i + 2, blockRow prog i) } = step { s with dir := .right, stack := [counterVal c, n], pc := (entryColumn prog i + 2, blockRow prog i) } by rfl]
    unfold step
    have hdec : decodeChar '*' = .mul := by unfold decodeChar; rfl
    simp only [hsm, hc2, hdec, stepState, Stack.applyBinary]
    rw [stepPos_right (playfieldWidth prog) (playfieldHeight prog) (entryColumn prog i + 2) (blockRow prog i) (by omega) (by omega)]
  have h4 : run 1 { s with dir := .right, stack := [n * counterVal c], pc := (entryColumn prog i + 3, blockRow prog i) } =
      some { s with stack := [n * counterVal c], pc := (entryColumn prog i + 3, blockRow prog i + 1), dir := .down } := by
    rw [show run 1 { s with dir := .right, stack := [n * counterVal c], pc := (entryColumn prog i + 3, blockRow prog i) } = step { s with dir := .right, stack := [n * counterVal c], pc := (entryColumn prog i + 3, blockRow prog i) } by rfl]
    unfold step
    have hdec : decodeChar 'v' = .down := by unfold decodeChar; rfl
    simp only [hsm, hc3, hdec, stepState]
    rw [stepPos_down (playfieldWidth prog) (playfieldHeight prog) (entryColumn prog i + 3) (blockRow prog i) (by omega) (by omega)]
  have h12 : run (1 + 1) s = some { s with dir := .right, stack := [counterVal c, n], pc := (entryColumn prog i + 2, blockRow prog i) } := by
    exact run_append s { s with dir := .right, pc := (entryColumn prog i + 1, blockRow prog i) }
      (some { s with dir := .right, stack := [counterVal c, n], pc := (entryColumn prog i + 2, blockRow prog i) }) 1 1 h1 h2
  have h123 : run (1 + 1 + 1) s = some { s with dir := .right, stack := [n * counterVal c], pc := (entryColumn prog i + 3, blockRow prog i) } := by
    exact run_append s { s with dir := .right, stack := [counterVal c, n], pc := (entryColumn prog i + 2, blockRow prog i) }
      (some { s with dir := .right, stack := [n * counterVal c], pc := (entryColumn prog i + 3, blockRow prog i) }) (1 + 1) 1 h12 h3
  have h1234 : run (1 + 1 + 1 + 1) s =
      some { s with stack := [n * counterVal c], pc := (entryColumn prog i + 3, blockRow prog i + 1), dir := .down } := by
    exact run_append s { s with dir := .right, stack := [n * counterVal c], pc := (entryColumn prog i + 3, blockRow prog i) }
      (some { s with stack := [n * counterVal c], pc := (entryColumn prog i + 3, blockRow prog i + 1), dir := .down }) (1 + 1 + 1) 1 h123 h4
  rw [show 4 = 1 + 1 + 1 + 1 by omega]
  rw [h1234]
  ext <;> try rfl
  rw [entryColumn_succ]
  rw [hinc]
  simp only [blockWidth]

end Completeness

end LeanFunge
