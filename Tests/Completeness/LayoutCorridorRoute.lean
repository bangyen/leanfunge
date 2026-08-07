/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanFunge.Theory.Completeness.LayoutCorridor

/-!
# Corridor Route Tests
-/

namespace LeanFunge.Tests

open LeanFunge
open LeanFunge.Completeness

/-- A `decz` jump edge routes the pointer up, across, and down to its target. -/
example :
    ((run 20 { State.init (playfieldOf layoutProgram) with
        pc := (7, 5), dir := .up }).map (fun s => s.pc))
      = some (11, 13) := by
  let S : State (playfieldWidth layoutProgram) (playfieldHeight layoutProgram) :=
    { State.init (playfieldOf layoutProgram) with pc := (7, 5), dir := .up }
  change ((run ((blockRow layoutProgram 1 - 1)
      + (if entryColumn layoutProgram 3 ≥ branchColumn layoutProgram 1 then
           entryColumn layoutProgram 3 - branchColumn layoutProgram 1
         else branchColumn layoutProgram 1 - entryColumn layoutProgram 3)
      + (blockRow layoutProgram 3 - 1 - 1)) S).map (fun s => s.pc)) = some (11, 13)
  have hwell : wellFormed layoutProgram := by
    unfold wellFormed
    intro i hi c k hk
    simp [layoutProgram] at hi -- no_squeeze: corridor route
    fin_cases c <;> interval_cases i <;> simp [layoutProgram] at hk ⊢ <;> omega -- no_squeeze: corridor route
  have h := corridor_run layoutProgram 1 3 0 (by decide) (by decide) hwell
    (by decide) S rfl (by decide) rfl rfl
  simp only [h, Option.map]
  decide

/-- A `jump` edge to an earlier block routes the pointer up and left. -/
example :
    ((run 4 { State.init (playfieldOf [.jump 0, .halt]) with
        pc := (1, 1), dir := .up }).map (fun s => s.pc))
      = some (0, 2) := by
  let prog : CMProgram := [.jump 0, .halt]
  let S : State (playfieldWidth prog) (playfieldHeight prog) :=
    { State.init (playfieldOf prog) with pc := (1, 1), dir := .up }
  change ((run ((blockRow prog 0 - 0)
      + (if entryColumn prog 0 ≥ branchColumn prog 0 then
           entryColumn prog 0 - branchColumn prog 0
         else branchColumn prog 0 - entryColumn prog 0)
      + (blockRow prog 0 - 0 - 1)) S).map (fun s => s.pc)) = some (0, 2)
  have hwell : wellFormed prog := by
    unfold wellFormed
    intro i hi c k hk
    simp [prog] at hi -- no_squeeze: corridor route
    fin_cases c <;> interval_cases i <;> simp [prog] at hk ⊢ <;> omega -- no_squeeze: corridor route
  have h := corridor_run prog 0 0 0 (by decide) (by decide) hwell
    (by decide) S rfl (by decide) rfl rfl
  simp only [h, Option.map]
  decide

end LeanFunge.Tests
