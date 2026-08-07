/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanFunge.Theory.Completeness.LayoutSimulationNormalize
import LeanFunge.Theory.Step
import Mathlib.Tactic

/-!
# The Normalized Step Agreement

A step of the normalized run agrees with the original run on the encoding,
and the agreement between the two runs is preserved.

## Main definitions

* `normalizeAgree`: The agreement between a normalized run and the original run.

## Theorems

* `normalize_step_encode`: A normalized step agrees with the original step on
  the encoding and preserves the agreement.
-/

namespace LeanFunge

namespace Completeness

open CMInstr

/-- The state agreement between a normalized run and the original run: equal
    counters, and equal program counters or both in the halted region. -/
def normalizeAgree (prog : CMProgram) (s t : CMState) : Prop :=
  s.c1 = t.c1 ∧ s.c2 = t.c2 ∧
    (s.pc = t.pc ∨ (instrAt (normalize prog) s.pc = .halt ∧ instrAt prog t.pc = .halt))

/-- A jump to `k` in the original run agrees with the clamped jump in the
    normalized run. -/
private lemma normalizeAgree_jump (prog : CMProgram) (s t : CMState) (hc1 : s.c1 = t.c1)
    (hc2 : s.c2 = t.c2) (k : ℕ) :
    normalizeAgree prog { s with pc := min k prog.length } { t with pc := k } := by
  constructor
  · simp [hc1] -- no_squeeze: simulation
  constructor
  · simp [hc2] -- no_squeeze: simulation
  by_cases hk : k < prog.length
  · left
    have hk' : k ≤ prog.length := by omega
    simp [Nat.min_eq_left hk'] -- no_squeeze: simulation
  · right
    have hge : prog.length ≤ k := by omega
    constructor
    · have hge' : prog.length ≤ min k prog.length := by
        rw [Nat.min_eq_right hge]
      exact instrAt_normalize_ge prog (min k prog.length) hge'
    · unfold instrAt
      simp [List.getD, hge] -- no_squeeze: simulation

/-- A single step of the normalized run agrees with the original run on the
    encoding and preserves the agreement. -/
theorem normalize_step_encode (prog : CMProgram) (s t : CMState) (hagree : normalizeAgree prog s t) :
    (CMInstr.step (normalize prog) s).map (fun s' => [encodeState s'])
      = (CMInstr.step prog t).map (fun s' => [encodeState s'])
    ∧ ∀ s' t', CMInstr.step (normalize prog) s = some s' → CMInstr.step prog t = some t' → normalizeAgree prog s' t' := by
  rcases hagree with ⟨hc1, hc2, hp⟩
  rcases hp with hpeq | hhalt
  · by_cases hlt : t.pc < prog.length
    · have hslt : s.pc < prog.length := by rw [hpeq]; exact hlt
      cases hget : instrAt prog t.pc with
      | inc c =>
          have hget_s : instrAt prog s.pc = .inc c := by rw [hpeq]; exact hget
          have hnorm : instrAt (normalize prog) s.pc = .inc c := by
            rw [instrAt_normalize_lt prog s.pc hslt]
            simp [clampInstr, hget_s] -- no_squeeze: simulation
          have h1 := CMInstr.step_inc prog t c hget
          have h2 := CMInstr.step_inc (normalize prog) s c hnorm
          have hinc : CMInstr.incCounter c s = CMInstr.incCounter c t := by
            fin_cases c <;> simp [incCounter, write, CMInstr.read, hc1, hc2, hpeq] -- no_squeeze: simulation
          constructor
          · fin_cases c <;> simp [h1, h2, hinc, encodeState, incCounter, write, CMInstr.read, hc1, hc2] -- no_squeeze: simulation
          · intro s' t' hs' ht'
            rw [h2] at hs'
            rw [h1] at ht'
            injection hs' with hs''
            injection ht' with ht''
            subst s'
            subst t'
            have hinc : CMInstr.incCounter c s = CMInstr.incCounter c t := by
              fin_cases c <;> simp [incCounter, write, CMInstr.read, hc1, hc2, hpeq] -- no_squeeze: simulation
            have hXY : { CMInstr.incCounter c s with pc := s.pc + 1 }
                = { CMInstr.incCounter c t with pc := t.pc + 1 } := by
              rw [hinc]
              simp [hpeq] -- no_squeeze: simulation
            rw [hXY]
            simp [normalizeAgree] -- no_squeeze: simulation
      | decz c k =>
          have hget_s : instrAt prog s.pc = .decz c k := by rw [hpeq]; exact hget
          have hnorm : instrAt (normalize prog) s.pc = .decz c (min k prog.length) := by
            rw [instrAt_normalize_lt prog s.pc hslt]
            simp [clampInstr, hget_s] -- no_squeeze: simulation
          by_cases hz : read c t = 0
          · have h1 := CMInstr.step_decz_zero prog t c k hget hz
            have h2 := CMInstr.step_decz_zero (normalize prog) s c (min k prog.length) hnorm (by simpa [CMInstr.read, hc1, hc2] using hz) -- no_squeeze: simulation
            constructor
            · simp [h1, h2, encodeState, hc1, hc2] -- no_squeeze: simulation
            · intro s' t' hs' ht'
              rw [h2] at hs'
              rw [h1] at ht'
              injection hs' with hs''
              injection ht' with ht''
              subst s'
              subst t'
              exact normalizeAgree_jump prog s t hc1 hc2 k
          · have h1 := CMInstr.step_decz_nonzero prog t c k hget hz
            have h2 := CMInstr.step_decz_nonzero (normalize prog) s c (min k prog.length) hnorm (by simpa [CMInstr.read, hc1, hc2] using hz) -- no_squeeze: simulation
            have hdec : CMInstr.decCounter c s = CMInstr.decCounter c t := by
              fin_cases c <;> simp [decCounter, write, CMInstr.read, hc1, hc2, hpeq] -- no_squeeze: simulation
            have hXY : { CMInstr.decCounter c s with pc := s.pc + 1 }
                = { CMInstr.decCounter c t with pc := t.pc + 1 } := by
              rw [hdec]
              simp [hpeq] -- no_squeeze: simulation
            constructor
            · fin_cases c <;> simp [h1, h2, hdec, encodeState, decCounter, write, CMInstr.read, hc1, hc2] -- no_squeeze: simulation
            · intro s' t' hs' ht'
              rw [h2] at hs'
              rw [h1] at ht'
              injection hs' with hs''
              injection ht' with ht''
              subst s'
              subst t'
              rw [hXY]
              simp [normalizeAgree] -- no_squeeze: simulation
      | jump k =>
          have hget_s : instrAt prog s.pc = .jump k := by rw [hpeq]; exact hget
          have hnorm : instrAt (normalize prog) s.pc = .jump (min k prog.length) := by
            rw [instrAt_normalize_lt prog s.pc hslt]
            simp [clampInstr, hget_s] -- no_squeeze: simulation
          have h1 := CMInstr.step_jump prog t k hget
          have h2 := CMInstr.step_jump (normalize prog) s (min k prog.length) hnorm
          constructor
          · simp [h1, h2, encodeState, hc1, hc2] -- no_squeeze: simulation
          · intro s' t' hs' ht'
            rw [h2] at hs'
            rw [h1] at ht'
            injection hs' with hs''
            injection ht' with ht''
            subst s'
            subst t'
            change normalizeAgree prog
              { s with pc := min k prog.length }
              { t with pc := k }
            exact normalizeAgree_jump prog s t hc1 hc2 k
      | halt =>
          have hget_s : instrAt prog s.pc = .halt := by rw [hpeq]; exact hget
          have hnorm : instrAt (normalize prog) s.pc = .halt := by
            rw [instrAt_normalize_lt prog s.pc hslt]
            simp [clampInstr, hget_s] -- no_squeeze: simulation
          have h1 := CMInstr.step_halt prog t hget
          have h2 := CMInstr.step_halt (normalize prog) s hnorm
          constructor
          · rw [h1, h2]
          · intro s' t' hs' ht'
            rw [h2] at hs'
            cases hs'
    · have hge : prog.length ≤ t.pc := by omega
      have hsge : prog.length ≤ s.pc := by rw [hpeq]; exact hge
      have ht : instrAt prog t.pc = .halt := by
        unfold instrAt
        simp [List.getD, hge] -- no_squeeze: simulation
      have hs : instrAt (normalize prog) s.pc = .halt := instrAt_normalize_ge prog s.pc hsge
      have h1 := CMInstr.step_halt (normalize prog) s hs
      have h2 := CMInstr.step_halt prog t ht
      constructor
      · rw [h1, h2]
      · intro s' t' hs' ht'
        rw [h1] at hs'
        cases hs'
  · rcases hhalt with ⟨hs, ht⟩
    have h1 := CMInstr.step_halt (normalize prog) s hs
    have h2 := CMInstr.step_halt prog t ht
    constructor
    · rw [h1, h2]
    · intro s' t' hs' ht'
      rw [h1] at hs'
      cases hs'

end Completeness

end LeanFunge
