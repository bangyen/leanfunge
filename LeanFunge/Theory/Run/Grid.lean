/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanFunge.Core.Semantics
import LeanFunge.Theory.Invariance
import Mathlib.Data.Nat.Notation

/-!
# Run-Level Grid Invariance

## Main definitions

* `stepPreservesGrid`: A state whose next step cannot write to the playfield.

## Theorems

* `step_grid_of_stepPreservesGrid`: A step from a grid-preserving state leaves
  the playfield unchanged.
* `run_grid_invariant`: If every state reached during a run is grid-preserving,
  the playfield is unchanged across the whole run — in particular, a cell
  never written by the put instruction keeps its value.
-/

namespace LeanFunge

/-- A state whose next step cannot write to the playfield: either it is in
    string mode, or the instruction at the pointer is not `p`. -/
def stepPreservesGrid (s : State w h) : Prop :=
  s.stringMode = true ∨ decodeChar (s.grid.get s.pc.1 s.pc.2) ≠ .put

/-- A step from a grid-preserving state leaves the playfield unchanged. -/
theorem step_grid_of_stepPreservesGrid {s s' : State w h} (hstep : step s = some s')
    (hp : stepPreservesGrid s) : s'.grid = s.grid := by
  unfold step at hstep
  dsimp only at hstep
  by_cases hs : s.stringMode = true
  · rw [hs] at hstep
    change some (stepString s (s.grid.get s.pc.1 s.pc.2)) = some s' at hstep
    injection hstep with hs'
    rw [← hs']
    unfold stepString
    cases (s.grid.get s.pc.1 s.pc.2).toNat == '"'.toNat <;> rfl
  · have hf : s.stringMode = false := by
      have h := show s.stringMode = false ∨ s.stringMode = true by
        cases s.stringMode <;> decide
      rcases h with h | h
      · exact h
      · exact False.elim (hs h)
    rw [hf] at hstep
    have hne : decodeChar (s.grid.get s.pc.1 s.pc.2) ≠ .put := by
      rcases hp with hp | hp
      · exact False.elim (hs hp)
      · exact hp
    cases hins : decodeChar (s.grid.get s.pc.1 s.pc.2) with
    | push n =>
        rw [hins] at hstep
        change some (stepState s (.push n)) = some s' at hstep
        injection hstep with hs'
        rw [← hs']
        rfl
    | add =>
        rw [hins] at hstep
        change some (stepState s .add) = some s' at hstep
        injection hstep with hs'
        rw [← hs']
        rfl
    | sub =>
        rw [hins] at hstep
        change some (stepState s .sub) = some s' at hstep
        injection hstep with hs'
        rw [← hs']
        rfl
    | mul =>
        rw [hins] at hstep
        change some (stepState s .mul) = some s' at hstep
        injection hstep with hs'
        rw [← hs']
        rfl
    | div =>
        rw [hins] at hstep
        change some (stepState s .div) = some s' at hstep
        injection hstep with hs'
        rw [← hs']
        rfl
    | mod =>
        rw [hins] at hstep
        change some (stepState s .mod) = some s' at hstep
        injection hstep with hs'
        rw [← hs']
        rfl
    | not =>
        rw [hins] at hstep
        change some (stepState s .not) = some s' at hstep
        injection hstep with hs'
        rw [← hs']
        rfl
    | greater =>
        rw [hins] at hstep
        change some (stepState s .greater) = some s' at hstep
        injection hstep with hs'
        rw [← hs']
        rfl
    | right =>
        rw [hins] at hstep
        change some (stepState s .right) = some s' at hstep
        injection hstep with hs'
        rw [← hs']
        rfl
    | left =>
        rw [hins] at hstep
        change some (stepState s .left) = some s' at hstep
        injection hstep with hs'
        rw [← hs']
        rfl
    | up =>
        rw [hins] at hstep
        change some (stepState s .up) = some s' at hstep
        injection hstep with hs'
        rw [← hs']
        rfl
    | down =>
        rw [hins] at hstep
        change some (stepState s .down) = some s' at hstep
        injection hstep with hs'
        rw [← hs']
        rfl
    | chooseH =>
        rw [hins] at hstep
        change some (stepState s .chooseH) = some s' at hstep
        injection hstep with hs'
        rw [← hs']
        rfl
    | chooseV =>
        rw [hins] at hstep
        change some (stepState s .chooseV) = some s' at hstep
        injection hstep with hs'
        rw [← hs']
        rfl
    | random =>
        rw [hins] at hstep
        change some (stepState s .random) = some s' at hstep
        injection hstep with hs'
        rw [← hs']
        rfl
    | stringMode =>
        rw [hins] at hstep
        change some (stepState s .stringMode) = some s' at hstep
        injection hstep with hs'
        rw [← hs']
        rfl
    | dup =>
        rw [hins] at hstep
        change some (stepState s .dup) = some s' at hstep
        injection hstep with hs'
        rw [← hs']
        rfl
    | swap =>
        rw [hins] at hstep
        change some (stepState s .swap) = some s' at hstep
        injection hstep with hs'
        rw [← hs']
        rfl
    | drop =>
        rw [hins] at hstep
        change some (stepState s .drop) = some s' at hstep
        injection hstep with hs'
        rw [← hs']
        rfl
    | printInt =>
        rw [hins] at hstep
        change some (stepState s .printInt) = some s' at hstep
        injection hstep with hs'
        rw [← hs']
        rfl
    | printChar =>
        rw [hins] at hstep
        change some (stepState s .printChar) = some s' at hstep
        injection hstep with hs'
        rw [← hs']
        rfl
    | trampoline =>
        rw [hins] at hstep
        change some (stepState s .trampoline) = some s' at hstep
        injection hstep with hs'
        rw [← hs']
        rfl
    | get =>
        rw [hins] at hstep
        change some (stepState s .get) = some s' at hstep
        injection hstep with hs'
        rw [← hs']
        rfl
    | inputInt =>
        rw [hins] at hstep
        change some (stepState s .inputInt) = some s' at hstep
        injection hstep with hs'
        rw [← hs']
        rfl
    | nop =>
        rw [hins] at hstep
        change some (stepState s .nop) = some s' at hstep
        injection hstep with hs'
        rw [← hs']
        rfl
    | inputChar =>
        rw [hins] at hstep
        change some (stepState s .inputChar) = some s' at hstep
        injection hstep with hs'
        rw [← hs']
        unfold stepState
        cases h : s.input <;> rfl
    | put => exact False.elim (hne hins)
    | halt =>
        rw [hins] at hstep
        change none = some s' at hstep
        contradiction

/-- If every state reached during a run is grid-preserving, the playfield is
    unchanged across the whole run. -/
theorem run_grid_invariant (s : State w h) (n : ℕ) (s' : State w h)
    (h : run n s = some s')
    (hno : ∀ k, k ≤ n → ∀ sₖ, run k s = some sₖ → stepPreservesGrid sₖ) :
    s'.grid = s.grid := by
  induction n generalizing s' with
  | zero =>
      rw [run] at h
      injection h with hs'
      rw [hs']
  | succ n ih =>
      rcases hrun : run n s with _ | sₙ
      · rw [run, hrun] at h
        cases h
      · rw [run, hrun] at h
        have hstep : step sₙ = some s' := by simpa only using h
        have hsₙ : sₙ.grid = s.grid := by
          apply ih sₙ hrun
          intro k hk sₖ hsₖ
          exact hno k (Nat.le_trans hk (Nat.le_succ n)) sₖ hsₖ
        exact (step_grid_of_stepPreservesGrid hstep (hno n (Nat.le_succ n) sₙ hrun)).trans hsₙ

end LeanFunge
