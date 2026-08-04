/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanFunge.Core.Semantics
import LeanFunge.Theory.Random

/-!
# Multi-Step Relational Semantics

## Main definitions

* `runRel`: A finite relational execution, including propagation after halt.

## Theorems

* `run_refines_runRel`: Every deterministic run is a relational run.
* `runRel_append`: Relational runs compose across an intermediate live state.
-/

namespace LeanFunge

/-- Execute `n` relational steps. A live state may take any `stepRel` outcome;
    once a run reaches `none`, later steps remain halted. -/
def runRel (n : ℕ) (s : State w h) (result : Option (State w h)) : Prop :=
  match n with
  | 0 => result = some s
  | n + 1 =>
      (∃ sₙ, runRel n s (some sₙ) ∧ stepRel sₙ result) ∨
        (runRel n s none ∧ result = none)

/-- Every deterministic run is permitted by the multi-step relation. -/
theorem run_refines_runRel (n : ℕ) (s : State w h) (result : Option (State w h))
    (h : run n s = result) : runRel n s result := by
  induction n generalizing s result with
  | zero =>
      rw [run] at h
      exact h.symm
  | succ n ih =>
      rcases hrun : run n s with _ | sₙ
      · rw [run, hrun] at h
        right
        exact ⟨ih s none hrun, h.symm⟩
      · rw [run, hrun] at h
        cases hstep : step sₙ with
        | none =>
            change step sₙ = result at h
            rw [hstep] at h
            cases h
            left
            exact ⟨sₙ, ih s (some sₙ) hrun,
              step_none_refines_stepRel sₙ hstep⟩
        | some s' =>
            change step sₙ = result at h
            rw [hstep] at h
            cases h
            left
            exact ⟨sₙ, ih s (some sₙ) hrun, step_refines_stepRel sₙ s' hstep⟩

/-- A one-step relational run is exactly a `stepRel` transition. -/
theorem runRel_one (s : State w h) (result : Option (State w h)) :
    runRel 1 s result ↔ stepRel s result := by
  constructor
  · intro h
    rcases h with ⟨s₀, hs₀, hstep⟩ | ⟨hhalt, hresult⟩
    · cases hs₀
      exact hstep
    · cases hhalt
  · intro h
    left
    exact ⟨s, rfl, h⟩

/-- Once a relational run has halted, every longer bound is also halted. -/
theorem runRel_halts_mono (s : State w h) {n : ℕ}
    (h : runRel n s none) (m : ℕ) : runRel (n + m) s none := by
  induction m with
  | zero => simpa using h
  | succ m ih =>
      rw [Nat.add_succ]
      change runRel (n + m + 1) s none
      right
      exact ⟨ih, rfl⟩

/-- Compose a relational prefix with a relational continuation. -/
theorem runRel_append (s s' : State w h) (result : Option (State w h))
    (n m : ℕ) (h₁ : runRel n s (some s'))
    (h₂ : runRel m s' result) : runRel (n + m) s result := by
  induction m generalizing result with
  | zero =>
      rw [runRel] at h₂
      cases h₂
      simpa using h₁
  | succ m ih =>
      rw [runRel] at h₂
      rcases h₂ with ⟨sₘ, hₘ, hstep⟩ | ⟨hhalt, hresult⟩
      · rw [Nat.add_succ]
        left
        exact ⟨sₘ, ih (some sₘ) hₘ, hstep⟩
      · rw [Nat.add_succ]
        right
        exact ⟨ih none hhalt, hresult⟩

end LeanFunge
