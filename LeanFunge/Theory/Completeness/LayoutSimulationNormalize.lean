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
      simp [List.length] at hn -- no_squeeze: simulation
  | cons x xs ih =>
      cases n with
      | zero => rfl
      | succ n =>
          simp [List.length] at hn -- no_squeeze: simulation
          have hn' : n < xs.length := by omega
          simpa using ih n hn' -- no_squeeze: simulation

private lemma getD_map {α β : Type} (f : α → β) (l : List α) (n : ℕ) (d : α) :
    (l.map f).getD n (f d) = f (l.getD n d) := by
  induction l generalizing n with
  | nil => simp -- no_squeeze: simulation
  | cons x xs ih =>
      cases n with
      | zero => rfl
      | succ n => exact ih n

private lemma getD_append_right {α : Type} (l₁ l₂ : List α) (n : ℕ) (hn : l₁.length ≤ n) (d : α) :
    (l₁ ++ l₂).getD n d = l₂.getD (n - l₁.length) d := by
  induction l₁ generalizing n with
  | nil => simp -- no_squeeze: simulation
  | cons x xs ih =>
      cases n with
      | zero => simp at hn -- no_squeeze: simulation
      | succ n =>
          simp [List.length] at hn -- no_squeeze: simulation
          have hn' : xs.length ≤ n := by omega
          simpa using ih n hn' -- no_squeeze: simulation

/-- The normalized program's instruction at an in-range index is the clamped
    original instruction. -/
lemma instrAt_normalize_lt (prog : CMProgram) (i : ℕ) (hi : i < prog.length) :
    instrAt (normalize prog) i = clampInstr prog.length (instrAt prog i) := by
  unfold instrAt normalize
  have hlen : i < (prog.map (clampInstr prog.length)).length := by
    simpa using hi -- no_squeeze: simulation
  rw [getD_append_lt (prog.map (clampInstr prog.length)) [.halt] i hlen .halt]
  change (prog.map (clampInstr prog.length)).getD i (clampInstr prog.length .halt)
      = clampInstr prog.length (prog.getD i .halt)
  rw [getD_map (clampInstr prog.length) prog i .halt]

/-- Past the appended `halt`, the normalized program is a `halt`. -/
lemma instrAt_normalize_ge (prog : CMProgram) (i : ℕ) (hi : prog.length ≤ i) :
    instrAt (normalize prog) i = .halt := by
  unfold instrAt normalize
  have hlen : (prog.map (clampInstr prog.length)).length ≤ i := by
    simpa using hi -- no_squeeze: simulation
  rw [getD_append_right (prog.map (clampInstr prog.length)) [.halt] i hlen .halt]
  have hsub : i - (prog.map (clampInstr prog.length)).length = i - prog.length := by
    simp -- no_squeeze: simulation
  rw [hsub]
  by_cases h0 : i - prog.length = 0
  · simp [h0] -- no_squeeze: simulation
  · have hpos : 0 < i - prog.length := by omega
    simp [h0] -- no_squeeze: simulation

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
            simpa [clampInstr, hget] using hk -- no_squeeze: simulation
          rw [← hk'.2]
          have hm : min k₀ prog.length ≤ prog.length := Nat.min_le_right k₀ prog.length
          have hlen' : (normalize prog).length = prog.length + 1 := by
            dsimp [normalize] -- no_squeeze: simulation
            simp -- no_squeeze: simulation
          omega
      | jump k₀ =>
          simp [clampInstr, hget] at hk ⊢ -- no_squeeze: simulation
      | _ => simp [clampInstr, hget] at hk ⊢ -- no_squeeze: simulation
    · cases hget : instrAt prog i with
      | decz c0 k₀ =>
          simp [clampInstr, hget] at hk ⊢ -- no_squeeze: simulation
      | jump k₀ =>
          have hk' : min k₀ prog.length = k := by
            simpa [clampInstr, hget] using hk -- no_squeeze: simulation
          rw [← hk']
          have hm : min k₀ prog.length ≤ prog.length := Nat.min_le_right k₀ prog.length
          have hlen' : (normalize prog).length = prog.length + 1 := by
            dsimp [normalize] -- no_squeeze: simulation
            simp -- no_squeeze: simulation
          omega
      | _ => simp [clampInstr, hget] at hk ⊢ -- no_squeeze: simulation
  · intro i hi
    have hlen : (normalize prog).length = prog.length + 1 := by
      dsimp [normalize] -- no_squeeze: simulation
      simp -- no_squeeze: simulation
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

open CMInstr

/-- The normalized run agrees with the original run on the encoding, and
    preserves the state agreement. -/
private lemma normalize_run_encode_aux (prog : CMProgram) (n : ℕ) (s t : CMState)
    (hagree : normalizeAgree prog s t) :
    (CMInstr.run (normalize prog) n s).map (fun s' => [encodeState s'])
      = (CMInstr.run prog n t).map (fun s' => [encodeState s'])
    ∧ ∀ s' t', CMInstr.run (normalize prog) n s = some s' → CMInstr.run prog n t = some t' → normalizeAgree prog s' t' := by
  induction n with
  | zero =>
      constructor
      · simp [CMInstr.run, encodeState, hagree.1, hagree.2.1] -- no_squeeze: simulation
      · intro s' t' h1 h2
        simp [CMInstr.run] at h1 h2 -- no_squeeze: simulation
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
                have hleft : (CMInstr.run (normalize prog) n s).map (fun s' => [encodeState s']) = none := by simp [hnorm] -- no_squeeze: simulation
                have hright : (CMInstr.run prog n t).map (fun s' => [encodeState s']) = some [encodeState tₙ] := by simp [h2] -- no_squeeze: simulation
                rw [← hih.1] at hright
                rw [hleft] at hright
                simp at hright -- no_squeeze: simulation
          constructor
          · rw [CMInstr.run_succ, hnorm, CMInstr.run_succ, htn]
            simp -- no_squeeze: simulation
          · intro s' t' h1 h2
            rw [CMInstr.run_succ, hnorm] at h1
            simp at h1 -- no_squeeze: simulation
      | some sₙ =>
          cases hprog : CMInstr.run prog n t with
          | none =>
              have hleft : (CMInstr.run (normalize prog) n s).map (fun s' => [encodeState s']) = some [encodeState sₙ] := by simp [hnorm] -- no_squeeze: simulation
              have hright : (CMInstr.run prog n t).map (fun s' => [encodeState s']) = none := by simp [hprog] -- no_squeeze: simulation
              rw [hih.1] at hleft
              rw [hright] at hleft
              simp at hleft -- no_squeeze: simulation
          | some tₙ =>
              have hsync : normalizeAgree prog sₙ tₙ := hih.2 sₙ tₙ hnorm hprog
              have hstep := normalize_step_encode prog sₙ tₙ hsync
              constructor
              · rw [CMInstr.run_succ, hnorm, CMInstr.run_succ, hprog]
                simp [hstep.1] -- no_squeeze: simulation
              · intro s' t' h1 h2
                rw [CMInstr.run_succ, hnorm] at h1
                rw [CMInstr.run_succ, hprog] at h2
                simp at h1 -- no_squeeze: simulation
                simp at h2 -- no_squeeze: simulation
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
      simpa using hmap.symm -- no_squeeze: simulation
    have hrun : CMInstr.run prog n s₀ = none := by
      by_contra h
      cases h2 : CMInstr.run prog n s₀ with
      | none => exact h h2
      | some t =>
          have hm : (CMInstr.run prog n s₀).map (fun s' => [encodeState s']) = some [encodeState t] := by
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
    have hnormmap : (CMInstr.run (normalize prog) n s₀).map (fun s' => [encodeState s']) = none := by
      simpa using hmap -- no_squeeze: simulation
    have hrun : CMInstr.run (normalize prog) n s₀ = none := by
      by_contra h
      cases h2 : CMInstr.run (normalize prog) n s₀ with
      | none => exact h h2
      | some t =>
          have hm : (CMInstr.run (normalize prog) n s₀).map (fun s' => [encodeState s']) = some [encodeState t] := by
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
      (CMInstr.halts prog s₀ → halts (playfieldStart prog' s₀)) ∧
      ∀ n : ℕ, ∃ m : ℕ,
        (run m (playfieldStart prog' s₀)).map (fun s => s.stack)
          = (CMInstr.run prog n s₀).map (fun s => [encodeState s]) := by
  refine ⟨normalize prog, wellPlaced_normalize prog, ?_, ?_⟩
  · intro h
    have hlen : s₀.pc < (normalize prog).length := by
      dsimp [normalize] -- no_squeeze: simulation
      simp -- no_squeeze: simulation
      omega
    exact simulation_halts (normalize prog) (wellPlaced_normalize prog) s₀ hlen
      ((normalize_halts_iff prog s₀).mpr h)
  · intro n
    have hlen : s₀.pc < (normalize prog).length := by
      dsimp [normalize] -- no_squeeze: simulation
      simp -- no_squeeze: simulation
      omega
    rcases (simulation_map (normalize prog) (wellPlaced_normalize prog) s₀ hlen n) with ⟨m, hmap⟩
    refine ⟨m, ?_⟩
    have hstack : (run m (playfieldStart (normalize prog) s₀)).map (fun s => s.stack)
        = (CMInstr.run (normalize prog) n s₀).map (fun s => [encodeState s]) := by
      have hproj := congrArg (fun o : Option ((ℕ × ℕ) × List Int) => o.map (fun t => t.2)) hmap
      simpa using hproj -- no_squeeze: stack projection
    rw [hstack]
    exact normalize_run_encode prog s₀ n

end Completeness

end LeanFunge
