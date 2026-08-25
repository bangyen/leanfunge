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
        pc := (8, 5), dir := .up }).map (fun s => s.pc))
      = some (12, 13) := by
  let S : State (playfieldWidth layoutProgram) (playfieldHeight layoutProgram) :=
    { State.init (playfieldOf layoutProgram) with pc := (8, 5), dir := .up }
  change ((run ((blockRow layoutProgram 1 - 1)
      + (if entryColumn layoutProgram 3 ≥ branchColumn layoutProgram 1 then
           entryColumn layoutProgram 3 - branchColumn layoutProgram 1
         else branchColumn layoutProgram 1 - entryColumn layoutProgram 3)
      + (blockRow layoutProgram 3 - 1 - 1)) S).map (fun s => s.pc)) = some (12, 13)
  have hwell : wellFormed layoutProgram := by
    unfold wellFormed
    intro i hi c k hk
    simp only [
      layoutProgram, Fin.isValue, List.length_cons, List.length_nil, zero_add, Nat.reduceAdd] at hi
    fin_cases c <;> interval_cases i <;>
      (simp only [
        layoutProgram, Fin.isValue, List.getD_eq_getElem?_getD,
        List.length_cons, List.length_nil, zero_add, Nat.reduceAdd,
        Nat.ofNat_pos, getElem?_pos, List.getElem_cons_zero, Option.getD_some,
        Fin.zero_eta, reduceCtorEq, or_self, Nat.one_lt_ofNat,
        List.getElem_cons_succ, CMInstr.decz.injEq, true_and, or_false,
        Nat.reduceLT, Nat.lt_add_one, Fin.mk_one, zero_ne_one, false_and] at hk ⊢; try omega)
  have h := corridor_run layoutProgram 1 3 0 (by decide) (by decide) hwell
    (by decide) S rfl (by decide) rfl rfl
  simp only [h, Option.map]
  decide

/-- A `jump` edge to an earlier block routes the pointer up and left. -/
example :
    ((run 4 { State.init (playfieldOf [.jump 0, .halt]) with
        pc := (2, 1), dir := .up }).map (fun s => s.pc))
      = some (1, 2) := by
  let prog : CMProgram := [.jump 0, .halt]
  let S : State (playfieldWidth prog) (playfieldHeight prog) :=
    { State.init (playfieldOf prog) with pc := (2, 1), dir := .up }
  change ((run ((blockRow prog 0 - 0)
      + (if entryColumn prog 0 ≥ branchColumn prog 0 then
           entryColumn prog 0 - branchColumn prog 0
         else branchColumn prog 0 - entryColumn prog 0)
      + (blockRow prog 0 - 0 - 1)) S).map (fun s => s.pc)) = some (1, 2)
  have hwell : wellFormed prog := by
    unfold wellFormed
    intro i hi c k hk
    simp only [prog, List.length_cons, List.length_nil, zero_add, Nat.reduceAdd] at hi
    fin_cases c <;> interval_cases i <;>
      (simp only [
        prog, List.getD_eq_getElem?_getD, List.length_cons, List.length_nil,
        zero_add, Nat.reduceAdd, Nat.ofNat_pos, getElem?_pos,
        List.getElem_cons_zero, Option.getD_some, Fin.zero_eta, Fin.isValue,
        reduceCtorEq, CMInstr.jump.injEq, false_or, Nat.one_lt_ofNat,
        List.getElem_cons_succ, or_self, Fin.mk_one] at hk ⊢; try omega)
  have h := corridor_run prog 0 0 0 (by decide) (by decide) hwell
    (by decide) S rfl (by decide) rfl rfl
  simp only [h, Option.map]
  decide

end LeanFunge.Tests
