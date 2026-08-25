/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanFunge.Theory.Completeness.LayoutSimulation
import LeanFunge.Theory.Step
import Mathlib.Tactic
/-!
# Normalization and Universality

Every two-counter machine is equivalent, on the encoded counters and on

halting, to a well-placed program: clamp every jump target into the program

and append a `halt`.

A step of the normalized run agrees with the original run on the encoding,

and the agreement between the two runs is preserved.

The normalized run agrees with the original run on the encoding, so the

playfield simulation applies to every two-counter machine: for any machine the

construction yields a well-placed program whose playfield matches the

machine's encoded run and halts whenever the machine does.

## Definitions

* `clampInstr`: Clamp a jump target into a program's instruction range.

* `normalize`: Clamp every target into the program and append a `halt`.

* `normalizeAgree`: The agreement between a normalized run and the original run.

## Theorems

* `instrAt_normalize_lt`: The normalized program's in-range instruction is the

  clamped original.

* `instrAt_normalize_ge`: Past the appended halt instruction, the normalized

  program is a halt.

* `wellPlaced_normalize`: Every program normalizes to a well-placed one.

* `normalize_step_encode`: A normalized step agrees with the original step on

  the encoding and preserves the agreement.

* `normalize_run_encode`: The normalized program's encoded run matches the

  original's.

* `normalize_halts_iff`: The normalized program halts exactly when the original

  does.

* `universal_simulation`: Every two-counter machine has a simulating playfield.

-/
namespace LeanFunge

namespace Completeness

open CMInstr

/-- Clamp a jump target into range: a target above `n` becomes `n`, and other
    instructions pass through unchanged. -/
def clampInstr (n : ℕ) : CMInstr → CMInstr
  | .jump k => .jump (min k n)
  | .decz c k => .decz c (min k n)
  | instr => instr

/-- The normalization of a program: clamp every target into the program and
    append a `halt`, so the last instruction is a `halt` and no target runs off
    the end. -/
def normalize (prog : CMProgram) : CMProgram :=
  (prog.map (clampInstr prog.length)) ++ [.halt]

private lemma getD_append_lt {α : Type} (l₁ l₂ : List α) (n : ℕ) (hn : n < l₁.length) (d : α) :
    (l₁ ++ l₂).getD n d = l₁.getD n d := by
  induction l₁ generalizing n with
  | nil =>
      simp only [List.length, not_lt_zero] at hn
  | cons x xs ih =>
      cases n with
      | zero => rfl
      | succ n =>
          simp only [List.length, Order.lt_add_one_iff, Order.add_one_le_iff] at hn
          have hn' : n < xs.length := by omega
          simpa only [
            List.cons_append, List.getD_eq_getElem?_getD, List.getElem?_cons_succ] using ih n hn'

private lemma getD_map {α β : Type} (f : α → β) (l : List α) (n : ℕ) (d : α) :
    (l.map f).getD n (f d) = f (l.getD n d) := by
  induction l generalizing n with
  | nil => simp only [
    List.map_nil, List.getD_eq_getElem?_getD, List.length_nil, not_lt_zero, not_false_eq_true,
    getElem?_neg, Option.getD_none]
  | cons x xs ih =>
      cases n with
      | zero => rfl
      | succ n => exact ih n

private lemma getD_append_right {α : Type} (l₁ l₂ : List α) (n : ℕ) (hn : l₁.length ≤ n) (d : α) :
    (l₁ ++ l₂).getD n d = l₂.getD (n - l₁.length) d := by
  induction l₁ generalizing n with
  | nil => simp only [List.nil_append, List.getD_eq_getElem?_getD, List.length_nil, tsub_zero]
  | cons x xs ih =>
      cases n with
      | zero => simp only [
        List.length_cons, nonpos_iff_eq_zero, Nat.add_eq_zero_iff, List.length_eq_zero_iff,
        one_ne_zero, and_false] at hn
      | succ n =>
          simp only [List.length, add_le_add_iff_right] at hn
          have hn' : xs.length ≤ n := by omega
          simpa only [
            List.cons_append, List.getD_eq_getElem?_getD, List.getElem?_cons_succ,
            List.length_cons, Nat.reduceSubDiff] using ih n hn'

/-- The normalized program's instruction at an in-range index is the clamped
    original instruction. -/
lemma instrAt_normalize_lt (prog : CMProgram) (i : ℕ) (hi : i < prog.length) :
    instrAt (normalize prog) i = clampInstr prog.length (instrAt prog i) := by
  unfold instrAt normalize
  have hlen : i < (prog.map (clampInstr prog.length)).length := by
    simpa only [List.length_map] using hi
  rw [getD_append_lt (prog.map (clampInstr prog.length)) [.halt] i hlen .halt]
  change (prog.map (clampInstr prog.length)).getD i (clampInstr prog.length .halt)
      = clampInstr prog.length (prog.getD i .halt)
  rw [getD_map (clampInstr prog.length) prog i .halt]

/-- Past the appended `halt`, the normalized program is a `halt`. -/
lemma instrAt_normalize_ge (prog : CMProgram) (i : ℕ) (hi : prog.length ≤ i) :
    instrAt (normalize prog) i = .halt := by
  unfold instrAt normalize
  have hlen : (prog.map (clampInstr prog.length)).length ≤ i := by
    simpa only [List.length_map] using hi
  rw [getD_append_right (prog.map (clampInstr prog.length)) [.halt] i hlen .halt]
  have hsub : i - (prog.map (clampInstr prog.length)).length = i - prog.length := by
    simp only [List.length_map]
  rw [hsub]
  by_cases h0 : i - prog.length = 0
  · simp only [
    h0, List.getD_eq_getElem?_getD, List.length_cons, List.length_nil, zero_add, zero_lt_one,
    getElem?_pos, List.getElem_cons_zero, Option.getD_some]
  · have hpos : 0 < i - prog.length := by omega
    simp only [
      h0, List.getD_eq_getElem?_getD, List.length_cons, List.length_nil, zero_add, Nat.lt_one_iff,
      not_false_eq_true, getElem?_neg, Option.getD_none]

/-- The normalized program is well placed. -/
theorem wellPlaced_normalize (prog : CMProgram) : wellPlaced (normalize prog) := by
  constructor
  · unfold wellFormed
    intro i hi c k hk
    change instrAt (normalize prog) i = .decz c k ∨ instrAt (normalize prog) i = .jump k at hk
    have hlen : i < prog.length := by
      by_contra h
      have hge : prog.length ≤ i := by omega
      have hh : instrAt (normalize prog) i = .halt := instrAt_normalize_ge prog i hge
      rw [hh] at hk
      rcases hk with hk | hk <;> cases hk
    have hget' : instrAt (normalize prog) i = clampInstr prog.length (instrAt prog i) :=
      instrAt_normalize_lt prog i hlen
    rw [hget'] at hk
    rcases hk with hk | hk
    · cases hget : instrAt prog i with
      | decz c0 k₀ =>
          have hk' : c0 = c ∧ min k₀ prog.length = k := by
            simpa only [clampInstr, hget, decz.injEq] using hk
          rw [← hk'.2]
          have hm : min k₀ prog.length ≤ prog.length := Nat.min_le_right k₀ prog.length
          have hlen' : (normalize prog).length = prog.length + 1 := by
            dsimp only [normalize]
            simp only [
              List.length_append, List.length_map, List.length_cons, List.length_nil, zero_add,
]
          omega
      | jump k₀ =>
          simp only [clampInstr, hget, reduceCtorEq] at hk ⊢
      | _ => simp only [clampInstr, hget, reduceCtorEq] at hk ⊢
    · cases hget : instrAt prog i with
      | decz c0 k₀ =>
          simp only [clampInstr, hget, reduceCtorEq] at hk ⊢
      | jump k₀ =>
          have hk' : min k₀ prog.length = k := by
            simpa only [clampInstr, hget, jump.injEq] using hk
          rw [← hk']
          have hm : min k₀ prog.length ≤ prog.length := Nat.min_le_right k₀ prog.length
          have hlen' : (normalize prog).length = prog.length + 1 := by
            dsimp only [normalize]
            simp only [
              List.length_append, List.length_map, List.length_cons, List.length_nil, zero_add,
]
          omega
      | _ => simp only [clampInstr, hget, reduceCtorEq] at hk ⊢
  · intro i hi
    have hlen : (normalize prog).length = prog.length + 1 := by
      dsimp only [normalize]
      simp only [
        List.length_append, List.length_map, List.length_cons, List.length_nil, zero_add,
]
    rw [hlen] at hi
    by_cases hlt : i < prog.length
    · right
      omega
    · have hge : prog.length ≤ i := by omega
      left
      exact instrAt_normalize_ge prog i hge

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
  · simp only [hc1]
  constructor
  · simp only [hc2]
  by_cases hk : k < prog.length
  · left
    have hk' : k ≤ prog.length := by omega
    simp only [Nat.min_eq_left hk']
  · right
    have hge : prog.length ≤ k := by omega
    constructor
    · have hge' : prog.length ≤ min k prog.length := by
        rw [Nat.min_eq_right hge]
      exact instrAt_normalize_ge prog (min k prog.length) hge'
    · unfold instrAt
      simp only [List.getD, hge, not_lt, getElem?_neg, Option.getD_none]

/-- A single step of the normalized run agrees with the original run on the
    encoding and preserves the agreement. -/
theorem normalize_step_encode (prog : CMProgram) (s t : CMState)
    (hagree : normalizeAgree prog s t) :
    (CMInstr.step (normalize prog) s).map (fun s' => [encodeState s'])
      = (CMInstr.step prog t).map (fun s' => [encodeState s'])
    ∧ ∀ s' t', CMInstr.step (normalize prog) s = some s'
        → CMInstr.step prog t = some t' → normalizeAgree prog s' t' := by
  rcases hagree with ⟨hc1, hc2, hp⟩
  rcases hp with hpeq | hhalt
  · by_cases hlt : t.pc < prog.length
    · have hslt : s.pc < prog.length := by rw [hpeq]; exact hlt
      cases hget : instrAt prog t.pc with
      | inc c =>
          have hget_s : instrAt prog s.pc = .inc c := by rw [hpeq]; exact hget
          have hnorm : instrAt (normalize prog) s.pc = .inc c := by
            rw [instrAt_normalize_lt prog s.pc hslt]
            simp only [clampInstr, hget_s]
          have h1 := CMInstr.step_inc prog t c hget
          have h2 := CMInstr.step_inc (normalize prog) s c hnorm
          have hinc : CMInstr.incCounter c s = CMInstr.incCounter c t := by
            fin_cases c <;> simp only [incCounter, write, CMInstr.read, hc1, hc2, hpeq]
          constructor
          · fin_cases c <;> simp only [encodeState, Int.ofNat_eq_natCast, h2, incCounter, write,
              ↓reduceIte, CMInstr.read, hc1, hc2, Option.map_some, h1, one_ne_zero]
          · intro s' t' hs' ht'
            rw [h2] at hs'
            rw [h1] at ht'
            injection hs' with hs''
            injection ht' with ht''
            subst s'
            subst t'
            have hinc : CMInstr.incCounter c s = CMInstr.incCounter c t := by
              fin_cases c <;>
                simp only [incCounter, write, CMInstr.read, hc1, hc2, hpeq, ↓reduceIte, one_ne_zero]
            have hXY : { CMInstr.incCounter c s with pc := s.pc + 1 }
                = { CMInstr.incCounter c t with pc := t.pc + 1 } := by
              rw [hinc]
              simp only [hpeq]
            rw [hXY]
            simp only [normalizeAgree, true_or, and_self]
      | decz c k =>
          have hget_s : instrAt prog s.pc = .decz c k := by rw [hpeq]; exact hget
          have hnorm : instrAt (normalize prog) s.pc = .decz c (min k prog.length) := by
            rw [instrAt_normalize_lt prog s.pc hslt]
            simp only [clampInstr, hget_s]
          by_cases hz : read c t = 0
          · have h1 := CMInstr.step_decz_zero prog t c k hget hz
            have h2 := CMInstr.step_decz_zero (normalize prog) s c
              (min k prog.length) hnorm
                (by simpa only [CMInstr.read, hc1, hc2, Fin.val_eq_zero_iff, Fin.isValue] using hz)
            constructor
            · simp only [h1, h2, encodeState, hc1, hc2, Int.ofNat_eq_natCast, Option.map_some]
            · intro s' t' hs' ht'
              rw [h2] at hs'
              rw [h1] at ht'
              injection hs' with hs''
              injection ht' with ht''
              subst s'
              subst t'
              exact normalizeAgree_jump prog s t hc1 hc2 k
          · have h1 := CMInstr.step_decz_nonzero prog t c k hget hz
            have h2 := CMInstr.step_decz_nonzero (normalize prog) s c
              (min k prog.length) hnorm
                (by simpa only [
                  CMInstr.read, hc1, hc2, Fin.val_eq_zero_iff, Fin.isValue, ne_eq] using hz)
            have hdec : CMInstr.decCounter c s = CMInstr.decCounter c t := by
              fin_cases c <;>
                simp only [decCounter, write, CMInstr.read, hc1, hc2, hpeq, ↓reduceIte, one_ne_zero]
            have hXY : { CMInstr.decCounter c s with pc := s.pc + 1 }
                = { CMInstr.decCounter c t with pc := t.pc + 1 } := by
              rw [hdec]
              simp only [hpeq]
            constructor
            · fin_cases c <;> simp only [encodeState, Int.ofNat_eq_natCast, h2, decCounter, write,
                ↓reduceIte, CMInstr.read, hc1, hc2, Option.map_some, h1, one_ne_zero]
            · intro s' t' hs' ht'
              rw [h2] at hs'
              rw [h1] at ht'
              injection hs' with hs''
              injection ht' with ht''
              subst s'
              subst t'
              rw [hXY]
              simp only [normalizeAgree, true_or, and_self]
      | jump k =>
          have hget_s : instrAt prog s.pc = .jump k := by rw [hpeq]; exact hget
          have hnorm : instrAt (normalize prog) s.pc = .jump (min k prog.length) := by
            rw [instrAt_normalize_lt prog s.pc hslt]
            simp only [clampInstr, hget_s]
          have h1 := CMInstr.step_jump prog t k hget
          have h2 := CMInstr.step_jump (normalize prog) s (min k prog.length) hnorm
          constructor
          · simp only [h1, h2, encodeState, hc1, hc2, Int.ofNat_eq_natCast, Option.map_some]
          · intro s' t' hs' ht'
            rw [h2] at hs'
            rw [h1] at ht'
            injection hs' with hs''
            injection ht' with ht''
            subst s'
            subst t'
            exact normalizeAgree_jump prog s t hc1 hc2 k
      | halt =>
          have hget_s : instrAt prog s.pc = .halt := by rw [hpeq]; exact hget
          have hnorm : instrAt (normalize prog) s.pc = .halt := by
            rw [instrAt_normalize_lt prog s.pc hslt]
            simp only [clampInstr, hget_s]
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
        simp only [List.getD, hge, not_lt, getElem?_neg, Option.getD_none]
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

open CMInstr

/-- The normalized run agrees with the original run on the encoding, and
    preserves the state agreement. -/
private lemma normalize_run_encode_aux (prog : CMProgram) (n : ℕ) (s t : CMState)
    (hagree : normalizeAgree prog s t) :
    (CMInstr.run (normalize prog) n s).map (fun s' => [encodeState s'])
      = (CMInstr.run prog n t).map (fun s' => [encodeState s'])
    ∧ ∀ s' t', CMInstr.run (normalize prog) n s = some s'
        → CMInstr.run prog n t = some t' → normalizeAgree prog s' t' := by
  induction n with
  | zero =>
      constructor
      · simp only [
        CMInstr.run, encodeState, hagree.1, hagree.2.1, Int.ofNat_eq_natCast, Option.map_some]
      · intro s' t' h1 h2
        simp only [CMInstr.run, Option.some.injEq] at h1 h2
        subst s'
        subst t'
        exact hagree
  | succ n ih =>
      have hih := ih
      cases hnorm : CMInstr.run (normalize prog) n s with
      | none =>
          have htn : CMInstr.run prog n t = none := by
            by_contra h
            cases h2 : CMInstr.run prog n t with
            | none => exact h h2
            | some tₙ =>
                have hleft : (CMInstr.run (normalize prog) n s).map
                    (fun s' => [encodeState s']) = none := by
                  simp only [hnorm, Option.map_none]
                have hright : (CMInstr.run prog n t).map
                    (fun s' => [encodeState s']) = some [encodeState tₙ] := by
                  simp only [h2, Option.map_some]
                rw [← hih.1] at hright
                rw [hleft] at hright
                simp only [reduceCtorEq] at hright
          constructor
          · rw [CMInstr.run_succ, hnorm, CMInstr.run_succ, htn]
            simp only [Option.bind_none, Option.map_none]
          · intro s' t' h1 h2
            rw [CMInstr.run_succ, hnorm] at h1
            simp only [Option.bind_none, reduceCtorEq] at h1
      | some sₙ =>
          cases hprog : CMInstr.run prog n t with
          | none =>
              have hleft : (CMInstr.run (normalize prog) n s).map
                  (fun s' => [encodeState s']) = some [encodeState sₙ] := by
                simp only [hnorm, Option.map_some]
              have hright : (CMInstr.run prog n t).map
                  (fun s' => [encodeState s']) = none := by
                simp only [hprog, Option.map_none]
              rw [hih.1] at hleft
              rw [hright] at hleft
              simp only [reduceCtorEq] at hleft
          | some tₙ =>
              have hsync : normalizeAgree prog sₙ tₙ := hih.2 sₙ tₙ hnorm hprog
              have hstep := normalize_step_encode prog sₙ tₙ hsync
              constructor
              · rw [CMInstr.run_succ, hnorm, CMInstr.run_succ, hprog]
                simp only [hstep.1, Option.bind_some]
              · intro s' t' h1 h2
                rw [CMInstr.run_succ, hnorm] at h1
                rw [CMInstr.run_succ, hprog] at h2
                simp only [Option.bind_some] at h1
                simp only [Option.bind_some] at h2
                exact hstep.2 s' t' h1 h2

/-- The normalized program's encoded run matches the original's. -/
theorem normalize_run_encode (prog : CMProgram) (s₀ : CMState) (n : ℕ) :
    (CMInstr.run (normalize prog) n s₀).map (fun s' => [encodeState s'])
      = (CMInstr.run prog n s₀).map (fun s' => [encodeState s']) := by
  have hagree : normalizeAgree prog s₀ s₀ := by
    constructor
    · rfl
    constructor
    · rfl
    · left
      rfl
  exact (normalize_run_encode_aux prog n s₀ s₀ hagree).1

/-- The normalized program halts exactly when the original does. -/
theorem normalize_halts_iff (prog : CMProgram) (s₀ : CMState) :
    CMInstr.halts (normalize prog) s₀ ↔ CMInstr.halts prog s₀ := by
  constructor
  · intro h
    rcases h with ⟨n, hn⟩
    have hmap := normalize_run_encode prog s₀ n
    rw [hn] at hmap
    have hprogmap : (CMInstr.run prog n s₀).map (fun s' => [encodeState s']) = none := by
      simpa only [Option.map_eq_none_iff, Option.map_none] using hmap.symm
    have hrun : CMInstr.run prog n s₀ = none := by
      by_contra h
      cases h2 : CMInstr.run prog n s₀ with
      | none => exact h h2
      | some t =>
          have hm : (CMInstr.run prog n s₀).map
              (fun s' => [encodeState s']) = some [encodeState t] := by
            rw [h2]
            change some [encodeState t] = some [encodeState t]
            rfl
          rw [hprogmap] at hm
          cases hm
    exact ⟨n, hrun⟩
  · intro h
    rcases h with ⟨n, hn⟩
    have hmap := normalize_run_encode prog s₀ n
    rw [hn] at hmap
    have hnormmap : (CMInstr.run (normalize prog) n s₀).map
        (fun s' => [encodeState s']) = none := by
      simpa only [Option.map_eq_none_iff, Option.map_none] using hmap
    have hrun : CMInstr.run (normalize prog) n s₀ = none := by
      by_contra h
      cases h2 : CMInstr.run (normalize prog) n s₀ with
      | none => exact h h2
      | some t =>
          have hm : (CMInstr.run (normalize prog) n s₀).map
              (fun s' => [encodeState s']) = some [encodeState t] := by
            rw [h2]
            change some [encodeState t] = some [encodeState t]
            rfl
          rw [hnormmap] at hm
          cases hm
    exact ⟨n, hrun⟩

/-- Every two-counter machine has a simulating playfield. -/
theorem universal_simulation (prog : CMProgram) (s₀ : CMState) (hs₀ : s₀.pc < prog.length) :
    ∃ prog' : CMProgram,
      wellPlaced prog' ∧
      (halts (playfieldStart prog' s₀) ↔ CMInstr.halts prog s₀) ∧
      ∀ n : ℕ, ∃ m : ℕ,
        (run m (playfieldStart prog' s₀)).map (fun s => s.stack)
          = (CMInstr.run prog n s₀).map (fun s => [encodeState s]) := by
  refine ⟨normalize prog, wellPlaced_normalize prog, ?_, ?_⟩
  · have hlen : s₀.pc < (normalize prog).length := by
      dsimp only [normalize]
      simp only [
        List.length_append, List.length_map, List.length_cons, List.length_nil, zero_add,
        Order.lt_add_one_iff]
      omega
    exact (simulation_halts_iff (normalize prog) (wellPlaced_normalize prog) s₀
      hlen).trans (normalize_halts_iff prog s₀)
  · intro n
    have hlen : s₀.pc < (normalize prog).length := by
      dsimp only [normalize]
      simp only [
        List.length_append, List.length_map, List.length_cons, List.length_nil, zero_add,
        Order.lt_add_one_iff]
      omega
    rcases (simulation_map (normalize prog) (wellPlaced_normalize prog) s₀ hlen n) with ⟨m, hmap⟩
    refine ⟨m, ?_⟩
    have hstack : (run m (playfieldStart (normalize prog) s₀)).map (fun s => s.stack)
        = (CMInstr.run (normalize prog) n s₀).map (fun s => [encodeState s]) := by
      have hproj := congrArg (fun o : Option ((ℕ × ℕ) × List Int) => o.map (fun t => t.2)) hmap
      simpa only [Option.map_map] using hproj
    rw [hstack]
    exact normalize_run_encode prog s₀ n

end Completeness

end LeanFunge
