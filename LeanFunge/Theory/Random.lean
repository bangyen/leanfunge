/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanFunge.Core.Semantics
import Mathlib.Data.Nat.Notation

/-!
# Nondeterminism

## Theorems

* `step_refines_stepRel`: Every `some` outcome of `step` is permitted by the
  relation.
* `step_none_refines_stepRel`: Every halting step is a halting step of the
  relation.
* `stepRel_random_choice`: At a `?` outside string mode, the relation permits
  choosing any direction.
* `stepRel_random_four`: All four cardinal directions are reachable outcomes
  of a `?`.
* `stepRel_eq_step_of_not_random`: Outside a `?`, the relation agrees exactly
  with the deterministic step.
* `stepRel_unique_of_not_random`: Outside a `?`, the relation has at most one
  successor, so every deterministic program has a unique next state.
* `stepRel_not_unique_of_random`: At a `?`, the relation has distinct
  successors, so the nondeterminism is genuine.
-/

namespace LeanFunge

/-- The deterministic interpreter is a sound refinement of the
    nondeterministic transition relation: every `some` outcome it produces is
    permitted by the relation. -/
theorem step_refines_stepRel (s : State w h) (s' : State w h) (h : step s = some s') :
    stepRel s (some s') := by
  left
  exact h.symm

/-- A halting deterministic step is also a halting step of the relation. -/
theorem step_none_refines_stepRel (s : State w h) (h : step s = none) :
    stepRel s none := by
  left
  exact h.symm

/-- At a `?` outside string mode, the relation permits choosing any
    direction. -/
theorem stepRel_random_choice (s : State w h) (hm : s.stringMode = false)
    (hr : decodeChar (s.grid.get s.pc.1 s.pc.2) = .random) (d : Direction) :
    stepRel s (some { s with dir := d, pc := stepPos w h d s.pc }) := by
  right
  refine ⟨d, ?_, ?_, rfl⟩
  · rw [hm]
    trivial
  · exact hr

/-- All four cardinal directions are reachable outcomes of a `?`. -/
theorem stepRel_random_four (s : State w h) (hm : s.stringMode = false)
    (hr : decodeChar (s.grid.get s.pc.1 s.pc.2) = .random) :
    stepRel s (some { s with dir := .up, pc := stepPos w h .up s.pc }) ∧
    stepRel s (some { s with dir := .down, pc := stepPos w h .down s.pc }) ∧
    stepRel s (some { s with dir := .left, pc := stepPos w h .left s.pc }) ∧
    stepRel s (some { s with dir := .right, pc := stepPos w h .right s.pc }) := by
  constructor
  · exact stepRel_random_choice s hm hr .up
  · constructor
    · exact stepRel_random_choice s hm hr .down
    · constructor
      · exact stepRel_random_choice s hm hr .left
      · exact stepRel_random_choice s hm hr .right

/-- Outside a `?`, the relation agrees exactly with the deterministic step. -/
theorem stepRel_eq_step_of_not_random (s : State w h) (s' : Option (State w h))
    (hr : decodeChar (s.grid.get s.pc.1 s.pc.2) ≠ .random) :
    stepRel s s' ↔ s' = step s := by
  constructor
  · intro h
    rcases h with h | h
    · exact h
    · rcases h with ⟨d, hm, hr', h'⟩
      exact False.elim (hr hr')
  · intro h
    left
    exact h

/-- Outside a `?`, the relation has at most one successor: any two outcomes of
    a step from a non-random state coincide, so every deterministic program
    has a unique next state. -/
theorem stepRel_unique_of_not_random (s : State w h) (s₁ s₂ : Option (State w h))
    (hr : decodeChar (s.grid.get s.pc.1 s.pc.2) ≠ .random)
    (h₁ : stepRel s s₁) (h₂ : stepRel s s₂) :
    s₁ = s₂ := by
  rw [stepRel_eq_step_of_not_random s s₁ hr] at h₁
  rw [stepRel_eq_step_of_not_random s s₂ hr] at h₂
  exact h₁.trans h₂.symm

/-- At a `?` outside string mode, the relation has distinct successors. -/
theorem stepRel_not_unique_of_random (s : State w h) (hm : s.stringMode = false)
    (hr : decodeChar (s.grid.get s.pc.1 s.pc.2) = .random) :
    ¬ ∀ s₁ s₂, stepRel s s₁ → stepRel s s₂ → s₁ = s₂ := by
  intro hunique
  have heq := hunique
    (some { s with dir := .up, pc := stepPos w h .up s.pc })
    (some { s with dir := .down, pc := stepPos w h .down s.pc })
    (stepRel_random_choice s hm hr .up)
    (stepRel_random_choice s hm hr .down)
  have hdir : Direction.up = Direction.down := by
    have h := congrArg (fun o : Option (State w h) => o.map State.dir) heq
    simpa only [Option.map] using h
  cases hdir

end LeanFunge
