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

end LeanFunge
