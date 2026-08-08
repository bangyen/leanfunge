/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanFunge.Theory.Completeness.LayoutSimulation
import LeanFunge.Theory.Completeness.LayoutSimulationNormalize

/-!
# Simulation Tests
-/

namespace LeanFunge.Tests

open LeanFunge
open LeanFunge.Completeness

/-- `layoutProgram` is well placed: well-formed with a `halt` at the end. -/
example : wellPlaced layoutProgram := by
  constructor
  · unfold wellFormed
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
  · intro i hi
    simp only [
      layoutProgram, Fin.isValue, List.length_cons, List.length_nil, zero_add, Nat.reduceAdd] at hi
    interval_cases i <;> simp only [
      CMInstr.instrAt, layoutProgram, Fin.isValue, List.getD_eq_getElem?_getD, List.length_cons,
      List.length_nil, zero_add, Nat.reduceAdd, Nat.ofNat_pos, getElem?_pos, List.getElem_cons_zero,
      Option.getD_some, reduceCtorEq, Nat.one_lt_ofNat, or_true, List.getElem_cons_succ,
      Nat.reduceLT, Nat.lt_add_one, lt_self_iff_false, or_false]

/-- The two-counter machine run is simulated by the playfield run. -/
example :
    ∃ m, (run m (playfieldStart layoutProgram (CMInstr.startCM 1 0))).map (fun s => (s.pc, s.stack))
      = (CMInstr.run layoutProgram 3 (CMInstr.startCM 1 0)).map
          (fun s => (blockEntry layoutProgram s.pc, [encodeState s])) := by
  have hwellPlaced : wellPlaced layoutProgram := by
    constructor
    · unfold wellFormed
      intro i hi c k hk
      simp only [
        layoutProgram, Fin.isValue, List.length_cons, List.length_nil, zero_add,
        Nat.reduceAdd] at hi
      fin_cases c <;> interval_cases i <;>
        (simp only [
          layoutProgram, Fin.isValue, List.getD_eq_getElem?_getD,
          List.length_cons, List.length_nil, zero_add, Nat.reduceAdd,
          Nat.ofNat_pos, getElem?_pos, List.getElem_cons_zero, Option.getD_some,
          Fin.zero_eta, reduceCtorEq, or_self, Nat.one_lt_ofNat,
          List.getElem_cons_succ, CMInstr.decz.injEq, true_and, or_false,
          Nat.reduceLT, Nat.lt_add_one, Fin.mk_one, zero_ne_one, false_and] at hk ⊢; try omega)
    · intro i hi
      simp only [
        layoutProgram, Fin.isValue, List.length_cons, List.length_nil, zero_add,
        Nat.reduceAdd] at hi
      interval_cases i <;> simp only [
        CMInstr.instrAt, layoutProgram, Fin.isValue, List.getD_eq_getElem?_getD, List.length_cons,
        List.length_nil, zero_add, Nat.reduceAdd, Nat.ofNat_pos, getElem?_pos,
        List.getElem_cons_zero, Option.getD_some, reduceCtorEq, Nat.one_lt_ofNat, or_true,
        List.getElem_cons_succ, Nat.reduceLT, Nat.lt_add_one, lt_self_iff_false, or_false]
  rcases (sim_run layoutProgram hwellPlaced (CMInstr.startCM 1 0) (by decide) 3) with ⟨m, hrun, hb⟩
  refine ⟨m, ?_⟩
  rw [hrun]
  rw [Option.map_map]
  congr 1

/-- The machine run leaves the counters `(1, 1)`. -/
example : CMInstr.run layoutProgram 3 (CMInstr.startCM 1 0)
    = some { pc := 3, c1 := 1, c2 := 1 } := by
  decide

/-- The playfield reaches the `halt` block entry with the encoding of `(1, 1)`
    after the inc, decz, and inc blocks. -/
example :
    ((run 20 (playfieldStart layoutProgram (CMInstr.startCM 1 0))).map (fun s => (s.pc, s.stack)))
      = some (blockEntry layoutProgram 3, [encodeState { pc := 3, c1 := 1, c2 := 1 }]) := by
  decide

/-- The machine halts, and the playfield halts along with it. -/
example : CMInstr.halts layoutProgram (CMInstr.startCM 1 0) →
    halts (playfieldStart layoutProgram (CMInstr.startCM 1 0)) := by
  have hwellPlaced : wellPlaced layoutProgram := by
    constructor
    · unfold wellFormed
      intro i hi c k hk
      simp only [
        layoutProgram, Fin.isValue, List.length_cons, List.length_nil, zero_add,
        Nat.reduceAdd] at hi
      fin_cases c <;> interval_cases i <;>
        (simp only [
          layoutProgram, Fin.isValue, List.getD_eq_getElem?_getD,
          List.length_cons, List.length_nil, zero_add, Nat.reduceAdd,
          Nat.ofNat_pos, getElem?_pos, List.getElem_cons_zero, Option.getD_some,
          Fin.zero_eta, reduceCtorEq, or_self, Nat.one_lt_ofNat,
          List.getElem_cons_succ, CMInstr.decz.injEq, true_and, or_false,
          Nat.reduceLT, Nat.lt_add_one, Fin.mk_one, zero_ne_one, false_and] at hk ⊢; try omega)
    · intro i hi
      simp only [
        layoutProgram, Fin.isValue, List.length_cons, List.length_nil, zero_add,
        Nat.reduceAdd] at hi
      interval_cases i <;> simp only [
        CMInstr.instrAt, layoutProgram, Fin.isValue, List.getD_eq_getElem?_getD, List.length_cons,
        List.length_nil, zero_add, Nat.reduceAdd, Nat.ofNat_pos, getElem?_pos,
        List.getElem_cons_zero, Option.getD_some, reduceCtorEq, Nat.one_lt_ofNat, or_true,
        List.getElem_cons_succ, Nat.reduceLT, Nat.lt_add_one, lt_self_iff_false, or_false]
  exact simulation_halts layoutProgram hwellPlaced (CMInstr.startCM 1 0) (by decide)

/-- The playfield run reflects the machine run's positions and encodings. -/
example :
    ∃ m, (run m (playfieldStart layoutProgram (CMInstr.startCM 1 0))).map (fun s => (s.pc, s.stack))
      = (CMInstr.run layoutProgram 3 (CMInstr.startCM 1 0)).map
          (fun s => (blockEntry layoutProgram s.pc, [encodeState s])) := by
  have hwellPlaced : wellPlaced layoutProgram := by
    constructor
    · unfold wellFormed
      intro i hi c k hk
      simp only [
        layoutProgram, Fin.isValue, List.length_cons, List.length_nil, zero_add,
        Nat.reduceAdd] at hi
      fin_cases c <;> interval_cases i <;>
        (simp only [
          layoutProgram, Fin.isValue, List.getD_eq_getElem?_getD,
          List.length_cons, List.length_nil, zero_add, Nat.reduceAdd,
          Nat.ofNat_pos, getElem?_pos, List.getElem_cons_zero, Option.getD_some,
          Fin.zero_eta, reduceCtorEq, or_self, Nat.one_lt_ofNat,
          List.getElem_cons_succ, CMInstr.decz.injEq, true_and, or_false,
          Nat.reduceLT, Nat.lt_add_one, Fin.mk_one, zero_ne_one, false_and] at hk ⊢; try omega)
    · intro i hi
      simp only [
        layoutProgram, Fin.isValue, List.length_cons, List.length_nil, zero_add,
        Nat.reduceAdd] at hi
      interval_cases i <;> simp only [
        CMInstr.instrAt, layoutProgram, Fin.isValue, List.getD_eq_getElem?_getD, List.length_cons,
        List.length_nil, zero_add, Nat.reduceAdd, Nat.ofNat_pos, getElem?_pos,
        List.getElem_cons_zero, Option.getD_some, reduceCtorEq, Nat.one_lt_ofNat, or_true,
        List.getElem_cons_succ, Nat.reduceLT, Nat.lt_add_one, lt_self_iff_false, or_false]
  exact simulation_map layoutProgram hwellPlaced (CMInstr.startCM 1 0) (by decide) 3

/-- `layoutProgram` normalizes to itself with an appended `halt`. -/
example : normalize layoutProgram = [.inc 1, .decz 0 3, .inc 0, .halt, .halt] := by
  decide

/-- The normalization of `layoutProgram` is well placed. -/
example : wellPlaced (normalize layoutProgram) := by
  exact wellPlaced_normalize layoutProgram

/-- Every two-counter machine has a simulating playfield: the capstone. -/
example :
    ∃ prog' : CMProgram, wellPlaced prog' ∧
      (CMInstr.halts layoutProgram (CMInstr.startCM 1 0) →
        halts (playfieldStart prog' (CMInstr.startCM 1 0))) := by
  rcases (universal_simulation layoutProgram (CMInstr.startCM 1 0) (by decide)) with
    ⟨prog', hw, hh, hr⟩
  exact ⟨prog', hw, hh⟩

end LeanFunge.Tests
