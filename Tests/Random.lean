/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanFunge.Theory.Random

/-!
# Nondeterminism Tests
-/

namespace LeanFunge.Tests

open LeanFunge

example {w h : ℕ} (s : State w h) (s' : State w h) (h : step s = some s') :
    stepRel s (some s') :=
  step_refines_stepRel s s' h

example {w h : ℕ} (s : State w h) (h : step s = none) :
    stepRel s none :=
  step_none_refines_stepRel s h

example {w h : ℕ} (s : State w h) (hm : s.stringMode = false)
    (hr : decodeChar (s.grid.get s.pc.1 s.pc.2) = .random) (d : Direction) :
    stepRel s (some { s with dir := d, pc := stepPos w h d s.pc }) :=
  stepRel_random_choice s hm hr d

example {w h : ℕ} (s : State w h) (hm : s.stringMode = false)
    (hr : decodeChar (s.grid.get s.pc.1 s.pc.2) = .random) :
    stepRel s (some { s with dir := .up, pc := stepPos w h .up s.pc }) ∧
    stepRel s (some { s with dir := .down, pc := stepPos w h .down s.pc }) ∧
    stepRel s (some { s with dir := .left, pc := stepPos w h .left s.pc }) ∧
    stepRel s (some { s with dir := .right, pc := stepPos w h .right s.pc }) :=
  stepRel_random_four s hm hr

example {w h : ℕ} (s : State w h) (s' : Option (State w h))
    (hr : decodeChar (s.grid.get s.pc.1 s.pc.2) ≠ .random) :
    stepRel s s' ↔ s' = step s :=
  stepRel_eq_step_of_not_random s s' hr

example {w h : ℕ} (s : State w h) (s₁ s₂ : Option (State w h))
    (hr : decodeChar (s.grid.get s.pc.1 s.pc.2) ≠ .random)
    (h₁ : stepRel s s₁) (h₂ : stepRel s s₂) :
    s₁ = s₂ :=
  stepRel_unique_of_not_random s s₁ s₂ hr h₁ h₂

end LeanFunge.Tests
