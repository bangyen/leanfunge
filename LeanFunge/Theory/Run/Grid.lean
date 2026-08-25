/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanFunge.Core.Semantics
import LeanFunge.Theory.Grid
import LeanFunge.Theory.Invariance
import LeanFunge.Theory.Step
import Mathlib.Data.Nat.Notation

/-!
# Run-Level Grid Invariance

## Main definitions

* `stepPreservesGrid`: A state whose next step cannot write to the playfield.
* `putX`, `putY`, `putChar`: The coordinates and character a `p` step writes.
* `stepPreservesCell`: A state whose next step cannot change a given cell.
* `stepWrite`: The write a single step performs, if any.
* `applyWrite`: Apply an optional write to a playfield.
* `runWrites`: The writes performed by the first `n` steps of a run, in order.
* `gridNoPut`: A playfield with no put instruction in any of its cells.

## Theorems

* `step_grid_of_stepPreservesGrid`: A step from a grid-preserving state leaves
  the playfield unchanged.
* `run_grid_invariant`: If every state reached during a run is grid-preserving,
  the playfield is unchanged across the whole run — in particular, a cell
  never written by the put instruction keeps its value.
* `step_grid_put`: A `p` step writes exactly one cell of the playfield.
* `step_cell_of_stepPreservesCell`: A step that does not write a cell leaves
  that cell unchanged.
* `run_cell_invariant`: A cell never written during a run keeps its value.
* `step_grid_applyWrite`: A step's playfield is the previous playfield with
  the step's write applied.
* `run_grid_writes`: The playfield after `n` steps is the initial playfield
  with the run's accumulated put writes applied in order — the run-level
  memory model.
* `stepPreservesGrid_of_gridNoPut`: On a playfield with no put instruction,
  every state preserves the playfield.
* `run_grid_invariant_of_noPut`: A program with no put instruction cannot
  modify itself, for every number of steps.
-/

namespace LeanFunge

/-- A state whose next step cannot write to the playfield: either it is in
    string mode, or the instruction at the pointer is not `p`. -/
def stepPreservesGrid (s : State w h) : Prop :=
  s.stringMode = true ∨ decodeChar (s.grid.get s.pc.1 s.pc.2) ≠ .put

/-- A step from a grid-preserving state leaves the playfield unchanged. -/
theorem step_grid_of_stepPreservesGrid {s s' : State w h} (hstep : step s = some s')
    (hp : stepPreservesGrid s) : s'.grid = s.grid := by
  by_cases hs : s.stringMode = true
  · rw [step_eq_stepString s hs] at hstep
    injection hstep with hs'
    rw [← hs']
    unfold stepString
    cases (s.grid.get s.pc.1 s.pc.2).toNat == '"'.toNat <;> rfl
  · have hf : s.stringMode = false := stringMode_false_of_not hs
    have hne : decodeChar (s.grid.get s.pc.1 s.pc.2) ≠ .put := by
      rcases hp with hp | hp
      · exact absurd hp hs
      · exact hp
    rw [step_eq_stepState s hf (decodeChar_ne_halt_of_step hf hstep)] at hstep
    injection hstep with hs'
    rw [← hs']
    exact stepState_grid_of_ne_put s _ hne

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

/-- The x-coordinate written by a `p` step from `s`: the second value popped
    off the stack. -/
def putX (s : State w h) : ℕ :=
  Int.toNat (Stack.pop (Stack.pop s.stack).1).2

/-- The y-coordinate written by a `p` step from `s`: the first value popped
    off the stack. -/
def putY (s : State w h) : ℕ :=
  Int.toNat (Stack.pop s.stack).2

/-- The character written by a `p` step from `s`: the third value popped off
    the stack, as a character. -/
def putChar (s : State w h) : Char :=
  Char.ofNat (Int.toNat (Stack.pop (Stack.pop (Stack.pop s.stack).1).1).2)

/-- A `p` step writes exactly one cell of the playfield, at the popped
    coordinates and with the popped value as its character. -/
theorem step_grid_put {s s' : State w h} (hstep : step s = some s')
    (hstr : s.stringMode = false)
    (hins : decodeChar (s.grid.get s.pc.1 s.pc.2) = .put) :
    s'.grid = Grid.put s.grid (putX s) (putY s) (putChar s) := by
  unfold step at hstep
  dsimp only at hstep
  rw [hstr, hins] at hstep
  change some (stepState s .put) = some s' at hstep
  injection hstep with hs'
  rw [← hs']
  rfl

/-- A state whose next step cannot change the cell at `(x, y)`: either the step
    does not write at all, or it writes at different wrapped coordinates. -/
def stepPreservesCell (x y : ℕ) (s : State w h) : Prop :=
  stepPreservesGrid s ∨ (putX s % w ≠ x % w ∨ putY s % h ≠ y % h)

/-- A step that does not write the cell at `(x, y)` leaves that cell
    unchanged. -/
theorem step_cell_of_stepPreservesCell {s s' : State w h} (x y : ℕ)
    (hstep : step s = some s') (hp : stepPreservesCell x y s) :
    s'.grid.get x y = s.grid.get x y := by
  rcases hp with hp | hp
  · rw [step_grid_of_stepPreservesGrid hstep hp]
  · by_cases hg : stepPreservesGrid s
    · rw [step_grid_of_stepPreservesGrid hstep hg]
    · have hstr : s.stringMode = false := by
        rcases hs : s.stringMode with _ | _
        · rfl
        · exact absurd (Or.inl hs) hg
      have hins : decodeChar (s.grid.get s.pc.1 s.pc.2) = .put := by
        by_contra hne
        exact hg (Or.inr hne)
      rw [step_grid_put hstep hstr hins]
      exact Grid.get_put_other _ _ _ _ _ _ (by
        rcases hp with h | h
        · exact Or.inl (fun he => h he.symm)
        · exact Or.inr (fun he => h he.symm))

/-- If no state reached during a run writes the cell at `(x, y)`, the cell
    keeps its value across the whole run. -/
theorem run_cell_invariant (x y : ℕ) (s : State w h) (n : ℕ) (s' : State w h)
    (h : run n s = some s')
    (hno : ∀ k, k ≤ n → ∀ sₖ, run k s = some sₖ → stepPreservesCell x y sₖ) :
    s'.grid.get x y = s.grid.get x y := by
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
        have hsₙ : sₙ.grid.get x y = s.grid.get x y := by
          apply ih sₙ hrun
          intro k hk sₖ hsₖ
          exact hno k (Nat.le_trans hk (Nat.le_succ n)) sₖ hsₖ
        exact (step_cell_of_stepPreservesCell x y hstep
          (hno n (Nat.le_succ n) sₙ hrun)).trans hsₙ

/-- The write a single step performs: `some (x, y, c)` when the step executes
    `p` outside string mode, and `none` when it leaves the playfield alone. -/
def stepWrite (s : State w h) : Option (ℕ × ℕ × Char) :=
  if s.stringMode = true then none
  else if decodeChar (s.grid.get s.pc.1 s.pc.2) = .put then
    some (putX s, putY s, putChar s)
  else none

/-- Apply an optional write to a playfield. -/
def applyWrite (g : Grid w h) : Option (ℕ × ℕ × Char) → Grid w h
  | none => g
  | some (x, y, c) => Grid.put g x y c

/-- A step's playfield is the previous playfield with the step's write
    applied. -/
theorem step_grid_applyWrite {s s' : State w h} (hstep : step s = some s') :
    s'.grid = applyWrite s.grid (stepWrite s) := by
  unfold stepWrite
  by_cases hs : s.stringMode = true
  · rw [if_pos hs]
    exact step_grid_of_stepPreservesGrid hstep (Or.inl hs)
  · rw [if_neg hs]
    have hstr : s.stringMode = false := by
      rcases h : s.stringMode with _ | _
      · rfl
      · exact absurd h hs
    by_cases hp : decodeChar (s.grid.get s.pc.1 s.pc.2) = .put
    · rw [if_pos hp]
      exact step_grid_put hstep hstr hp
    · rw [if_neg hp]
      exact step_grid_of_stepPreservesGrid hstep (Or.inr hp)

/-- The writes performed by the first `n` steps from `s`, in order. A step that
    writes nothing, and a run that has already halted, contribute nothing. -/
def runWrites (n : ℕ) (s : State w h) : List (ℕ × ℕ × Char) :=
  match n with
  | 0 => []
  | n + 1 =>
      match run n s with
      | none => runWrites n s
      | some sₙ =>
          match stepWrite sₙ with
          | none => runWrites n s
          | some wt => runWrites n s ++ [wt]

/-- The playfield after `n` steps is the initial playfield with the run's
    accumulated `p` writes applied in order: the run-level `p`/`g` memory
    model. -/
theorem run_grid_writes (s : State w h) (n : ℕ) (s' : State w h)
    (h : run n s = some s') :
    s'.grid
      = (runWrites n s).foldl (fun g wt => Grid.put g wt.1 wt.2.1 wt.2.2) s.grid := by
  induction n generalizing s' with
  | zero =>
      rw [run] at h
      injection h with hs'
      rw [hs']
      rfl
  | succ n ih =>
      rcases hrun : run n s with _ | sₙ
      · rw [run, hrun] at h
        cases h
      · rw [run, hrun] at h
        have hstep : step sₙ = some s' := by simpa only using h
        have hsₙ := ih sₙ hrun
        have hws : runWrites (n + 1) s =
            match stepWrite sₙ with
            | none => runWrites n s
            | some wt => runWrites n s ++ [wt] := by
          rw [runWrites, hrun]
        rw [step_grid_applyWrite hstep, hsₙ, hws]
        rcases hw : stepWrite sₙ with _ | wt
        · rfl
        · simp only [List.foldl_append, List.foldl_cons, List.foldl_nil]
          rfl

/-- A playfield with no put instruction in any of its cells: a program that
    cannot modify itself. -/
def gridNoPut (g : Grid w h) : Prop :=
  ∀ x < w, ∀ y < h, decodeChar (g.cells y x) ≠ .put

instance (g : Grid w h) : Decidable (gridNoPut g) := by
  unfold gridNoPut
  infer_instance

/-- On a playfield with no put instruction, every state preserves the
    playfield: the wrapped pointer always lands on a non-put cell. -/
theorem stepPreservesGrid_of_gridNoPut {s : State w h} (hw : 0 < w) (hh : 0 < h)
    (hg : gridNoPut s.grid) : stepPreservesGrid s := by
  right
  unfold Grid.get
  exact hg _ (Nat.mod_lt _ hw) _ (Nat.mod_lt _ hh)

/-- A playfield containing no put instruction is unchanged across any run: the
    program cannot modify itself, for every number of steps. Unlike a
    step-count-specific computation, this quantifies over all runs. -/
theorem run_grid_invariant_of_noPut {s : State w h} (hw : 0 < w) (hh : 0 < h)
    (hg : gridNoPut s.grid) (n : ℕ) (s' : State w h) (h : run n s = some s') :
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
        have hsₙ : sₙ.grid = s.grid := ih sₙ hrun
        have hgₙ : gridNoPut sₙ.grid := by
          rw [hsₙ]; exact hg
        exact (step_grid_of_stepPreservesGrid hstep
          (stepPreservesGrid_of_gridNoPut hw hh hgₙ)).trans hsₙ

end LeanFunge
