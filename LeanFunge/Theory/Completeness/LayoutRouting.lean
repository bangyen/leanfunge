/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanFunge.Theory.Completeness.LayoutBlock
import LeanFunge.Theory.Completeness.LayoutCellMain
import LeanFunge.Theory.Completeness.Routing
import LeanFunge.Theory.Run.Relational
import LeanFunge.Theory.Step
import Mathlib.Tactic

/-!
# Generic Routing on the Generated Playfield

After a block executes, the pointer must travel to the next block. For the
fall-through case, every block's exit `v` sits at the next entry column on the
block's bottom row, and the cell below it is a space, so one step down drops
the pointer onto the next block's `>`. This module proves the generic
fall-through drop for arbitrary programs; the jump corridor routing lives
here as well once the up-turn-drop geometry is proven.

## Theorems

* `blockBodyAt_corner`: The bottom-right corner of a block's body is a space.
* `fallthrough_drop`: One step down from a block's bottom row reaches the
  next block's entry.
-/

namespace LeanFunge

namespace Completeness

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
    (hpc : s.pc = (entryColumn prog (i + 1), blockRow prog i + (blockHeight (prog.getD i .halt) - 1)))
    (hdir : s.dir = .down) (hgrid : s.grid = playfieldOf prog) :
    run 1 s = some { s with
      pc := (entryColumn prog (i + 1), blockRow prog (i + 1)),
      dir := .down } := by
  have hspace : (playfieldOf prog).get (entryColumn prog (i + 1))
      (blockRow prog i + (blockHeight (prog.getD i .halt) - 1)) = ' ' := by
    have hpb := playfield_block_get prog i hi1 (blockWidth (prog.getD i .halt))
        (blockHeight (prog.getD i .halt) - 1) (by rfl) (by have := blockHeight_pos (prog.getD i .halt); omega)
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
  have hhy : (blockRow prog i + (blockHeight (prog.getD i .halt) - 1)) + 1 < playfieldHeight prog := by
    have hb := blockHeight_pos (prog.getD i .halt)
    omega
  rw [show run 1 s = step s by rfl]
  rw [step_space s hsm (by rw [hpc, hgrid]; exact hspace)]
  rw [hdir, hpc, stepPos_down (playfieldWidth prog) (playfieldHeight prog) (entryColumn prog (i + 1))
      (blockRow prog i + (blockHeight (prog.getD i .halt) - 1)) hW hhy]
  have hpc' : (entryColumn prog (i + 1), (blockRow prog i + (blockHeight (prog.getD i .halt) - 1)) + 1)
      = (entryColumn prog (i + 1), blockRow prog (i + 1)) := by
    rw [blockRow_succ]
    apply Prod.ext
    · rfl
    · have hb := blockHeight_pos (prog.getD i .halt)
      omega
  rw [hpc']

end Completeness

end LeanFunge
