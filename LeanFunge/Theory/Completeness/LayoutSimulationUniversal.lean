/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanFunge.Theory.Completeness.LayoutSimulationNormalize
import LeanFunge.Theory.Completeness.LayoutSimulationNormalizeStep
import LeanFunge.Theory.Completeness.LayoutSimulationRun
import LeanFunge.Theory.Step
import Mathlib.Tactic

/-!
# The Universality Statement

The normalized run agrees with the original run on the encoding, so the
playfield simulation applies to every two-counter machine: for any machine the
construction yields a well-placed program whose playfield matches the
machine's encoded run and halts whenever the machine does.

## Theorems

* `normalize_run_encode`: The normalized program's encoded run matches the
  original's.
* `normalize_halts_iff`: The normalized program halts exactly when the original
  does.
* `universal_simulation`: Every two-counter machine has a simulating playfield.
-/

namespace LeanFunge

namespace Completeness

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
