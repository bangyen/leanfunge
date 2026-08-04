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

end LeanFunge
