/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanFunge.Core.Semantics
import LeanFunge.Theory.Invariance
import LeanFunge.Theory.Invariance
import LeanFunge.Theory.Step
import LeanFunge.Theory.Step

/-!
# Run-Level Divergence

Programs whose every step is a no-op never halt. This module proves the basic
divergence facts: on an all-space playfield the interpreter runs forever
without ever modifying the playfield or entering string mode.

The all-space case generalizes to any straight line of safe cells. A cell is
safe when it neither halts, turns, writes the playfield, nor toggles string
mode; `put` must be excluded because a write could place an `@` further along
the line, and `"` because it would leave the instruction set behind. On such a
line the pointer keeps its direction and stays on the line forever, so the
program diverges.

## Main definitions

* `SafeInstr`: An instruction that neither halts, turns, writes the playfield,
  nor toggles string mode.
* `SafeLine`: Every cell of the row or column the pointer travels along is
  safe.

## Theorems

* `run_space_step`: A run on an all-space playfield always has a successor
  state with the same grid and string mode off.
* `run_space_some`: A run on an all-space playfield never halts.
* `step_safe`: A safe step keeps the direction, the playfield, string mode off,
  and the pointer on its line.
* `safe_at_pc`: On a safe line the cell at the pointer is a safe instruction.
* `run_safe_line_step`: Every state of a run along a safe line stays on the
  line with the same direction and playfield.
* `run_safe_line_some`: A run along a safe line never halts.
* `not_halts_safe_line`: A program on a safe line diverges.
-/

namespace LeanFunge

/-- On an all-space playfield every step is a nop: each run has a successor
    state whose playfield is still all spaces and whose string mode is still
    off. -/
theorem run_space_step (w h : ℕ) (k x y : ℕ) :
    ∃ s_k : State w h,
      run k { State.init (Grid.space w h) with pc := (x, y), dir := .right } = some s_k ∧
      s_k.grid = Grid.space w h ∧ s_k.stringMode = false := by
  induction k with
  | zero =>
      refine ⟨{ State.init (Grid.space w h) with pc := (x, y), dir := .right }, rfl, ?_, ?_⟩
      · rfl
      · rfl
  | succ k ih =>
      rcases ih with ⟨s_k, hk, hgrid, hsm⟩
      have hcell : s_k.grid.get s_k.pc.1 s_k.pc.2 = ' ' := by
        rw [hgrid]
        rfl
      have hdec : decodeChar ' ' = .nop := by
        unfold decodeChar
        rfl
      have hstep : step s_k = some { s_k with pc := stepPos w h s_k.dir s_k.pc } := by
        unfold step
        simp only [hsm, hcell, hdec, stepState]
      refine ⟨{ s_k with pc := stepPos w h s_k.dir s_k.pc }, ?_, ?_, ?_⟩
      · rw [run, hk]
        change step s_k = some { s_k with pc := stepPos w h s_k.dir s_k.pc }
        rw [hstep]
      · exact hgrid
      · exact hsm

/-- A run on an all-space playfield never halts. -/
theorem run_space_some (w h : ℕ) (k x y : ℕ) :
    run k { State.init (Grid.space w h) with pc := (x, y), dir := .right } ≠ none := by
  rcases run_space_step w h k x y with ⟨s_k, hk, _, _⟩
  rw [hk]
  intro h
  cases h

/-- Instructions that neither halt, turn, write the playfield, nor toggle
    string mode. -/
def SafeInstr (i : Instruction) : Prop :=
  i ≠ .halt ∧ i ≠ .right ∧ i ≠ .left ∧ i ≠ .up ∧ i ≠ .down ∧
    i ≠ .chooseH ∧ i ≠ .chooseV ∧ i ≠ .random ∧ i ≠ .stringMode ∧ i ≠ .put

instance (i : Instruction) : Decidable (SafeInstr i) := by
  unfold SafeInstr
  infer_instance

/-- A safe step keeps the direction, the playfield, and string mode off, and
    leaves the pointer on the same line. -/
theorem step_safe {s : State w h} (hm : s.stringMode = false)
    (hsafe : SafeInstr (decodeChar (s.grid.get s.pc.1 s.pc.2))) :
    ∃ s', step s = some s' ∧ s'.dir = s.dir ∧ s'.grid = s.grid ∧
      s'.stringMode = false ∧
      (match s.dir with
       | .right | .left => s'.pc.2 % h = s.pc.2 % h
       | .up | .down => s'.pc.1 % w = s.pc.1 % w) := by
  obtain ⟨hhalt, hr, hl, hu, hd, hch, hcv, hrand, hstr, hput⟩ := hsafe
  have hone : ∀ p : ℕ × ℕ,
      (match s.dir with
       | .right | .left => (stepPos w h s.dir p).2 % h = p.2 % h
       | .up | .down => (stepPos w h s.dir p).1 % w = p.1 % w) := by
    intro p
    cases hdd : s.dir <;> (unfold stepPos; simp only [Nat.mod_mod])
  refine ⟨stepState s (decodeChar (s.grid.get s.pc.1 s.pc.2)),
    step_eq_stepState s hm hhalt, ?_, ?_, ?_, ?_⟩
  · exact stepState_dir_of_ne s _ hr hl hu hd hch hcv
  · exact stepState_grid_of_ne_put s _ hput
  · rw [stepState_stringMode_of_ne s _ hstr]
    exact hm
  · -- the pointer moves once, except the trampoline, which hops twice
    cases hins : decodeChar (s.grid.get s.pc.1 s.pc.2) with
    | halt => exact absurd hins hhalt
    | right => exact absurd hins hr
    | left => exact absurd hins hl
    | up => exact absurd hins hu
    | down => exact absurd hins hd
    | chooseH => exact absurd hins hch
    | chooseV => exact absurd hins hcv
    | random => exact absurd hins hrand
    | stringMode => exact absurd hins hstr
    | put => exact absurd hins hput
    | trampoline =>
        change (match s.dir with
          | .right | .left =>
              (stepPos w h s.dir (stepPos w h s.dir s.pc)).2 % h = s.pc.2 % h
          | .up | .down =>
              (stepPos w h s.dir (stepPos w h s.dir s.pc)).1 % w = s.pc.1 % w)
        cases hdd : s.dir <;> (unfold stepPos; simp only [Nat.mod_mod])
    | inputChar =>
        have hpc : (stepState s .inputChar).pc = stepPos w h s.dir s.pc := by
          unfold stepState
          cases s.input <;> rfl
        rw [hpc]
        exact hone s.pc
    | _ => exact hone s.pc

/-- Every cell the pointer can reach while moving in direction `d` from a
    position on the line through `pos` is safe. For horizontal directions the
    line is a row; for vertical directions a column. -/
def SafeLine (g : Grid w h) (d : Direction) (pos : ℕ × ℕ) : Prop :=
  match d with
  | .right | .left => ∀ x' < w, SafeInstr (decodeChar (g.cells (pos.2 % h) x'))
  | .up | .down => ∀ y' < h, SafeInstr (decodeChar (g.cells y' (pos.1 % w)))

/-- On a safe line the cell at the pointer is a safe instruction. -/
theorem safe_at_pc {g : Grid w h} {d : Direction} {pos p : ℕ × ℕ}
    (hw : 0 < w) (hh : 0 < h)
    (hp : match d with
          | .right | .left => p.2 % h = pos.2 % h
          | .up | .down => p.1 % w = pos.1 % w)
    (hline : SafeLine g d pos) :
    SafeInstr (decodeChar (g.get p.1 p.2)) := by
  unfold Grid.get
  cases d with
  | right =>
      rw [show p.2 % h = pos.2 % h from hp]
      exact hline _ (Nat.mod_lt _ hw)
  | left =>
      rw [show p.2 % h = pos.2 % h from hp]
      exact hline _ (Nat.mod_lt _ hw)
  | up =>
      rw [show p.1 % w = pos.1 % w from hp]
      exact hline _ (Nat.mod_lt _ hh)
  | down =>
      rw [show p.1 % w = pos.1 % w from hp]
      exact hline _ (Nat.mod_lt _ hh)

/-- A run along a safe line never halts: every reachable state has a successor
    on the same line, with the same direction and playfield. -/
theorem run_safe_line_step {s : State w h} (hw : 0 < w) (hh : 0 < h)
    (hm : s.stringMode = false) (hline : SafeLine s.grid s.dir s.pc) (n : ℕ) :
    ∃ s', run n s = some s' ∧ s'.dir = s.dir ∧ s'.grid = s.grid ∧
      s'.stringMode = false ∧
      (match s.dir with
       | .right | .left => s'.pc.2 % h = s.pc.2 % h
       | .up | .down => s'.pc.1 % w = s.pc.1 % w) := by
  induction n with
  | zero =>
      refine ⟨s, rfl, rfl, rfl, hm, ?_⟩
      cases s.dir <;> rfl
  | succ n ih =>
      obtain ⟨sₙ, hrun, hdir, hgrid, hsm, hpos⟩ := ih
      have hsafe : SafeInstr (decodeChar (sₙ.grid.get sₙ.pc.1 sₙ.pc.2)) := by
        rw [hgrid]
        exact safe_at_pc (g := s.grid) (d := s.dir) (pos := s.pc) (p := sₙ.pc)
          hw hh hpos hline
      obtain ⟨s', hstep, hd', hg', hs', hp'⟩ := step_safe hsm hsafe
      refine ⟨s', ?_, ?_, ?_, hs', ?_⟩
      · rw [run, hrun]; exact hstep
      · rw [hd', hdir]
      · rw [hg', hgrid]
      · rw [hdir] at hp'
        cases hdd : s.dir <;> rw [hdd] at hp' hpos <;> exact hp'.trans hpos

/-- A run along a safe line never halts. -/
theorem run_safe_line_some {s : State w h} (hw : 0 < w) (hh : 0 < h)
    (hm : s.stringMode = false) (hline : SafeLine s.grid s.dir s.pc) (n : ℕ) :
    run n s ≠ none := by
  obtain ⟨s', hrun, _, _, _, _⟩ := run_safe_line_step hw hh hm hline n
  rw [hrun]
  intro hc
  cases hc

/-- A program on a safe line diverges: it never halts, at any number of
    steps. -/
theorem not_halts_safe_line {s : State w h} (hw : 0 < w) (hh : 0 < h)
    (hm : s.stringMode = false) (hline : SafeLine s.grid s.dir s.pc) :
    ¬ halts s := by
  intro hc
  rcases hc with ⟨n, hn⟩
  exact run_safe_line_some hw hh hm hline n hn

end LeanFunge
