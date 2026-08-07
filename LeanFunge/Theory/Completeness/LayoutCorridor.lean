/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanFunge.Theory.Completeness.LayoutCellMain
import LeanFunge.Theory.Completeness.LayoutCellRange
import LeanFunge.Theory.Completeness.Routing
import LeanFunge.Theory.Run.Relational
import LeanFunge.Theory.Step
import Mathlib.Tactic

/-!
# The Corridor Routing on the Generated Playfield

A jump edge routes the pointer up its branch column to the header, across
the corridor row to the target's entry column, and down to the target block.
This module proves the foundations of that routing: a run that drops down
through cells that are spaces or `v`s (a drop passes the exit `v` of the
preceding block), and the fact that a block body holds no cell beyond its
width. The header-row lookup and the generalized block lookup, and the
up-turn-drop routing itself, complete the corridor.

## Main definitions

* `corridorRowAt`: The cell a corridor row places at a column, or a space.

## Theorems

* `step_down_cell`: A step through a space or a `v` while going down keeps
  the pointer down.
* `run_down`: Running down through spaces and `v`s keeps the pointer down.
* `blockBodyAt_out`: A block body has no cell beyond its width.
-/

namespace LeanFunge

namespace Completeness

/-- The cell that header row `y` places at column `x`: the corridor turn at
    the branch column, the drop `v` at the target's entry column, or a
    space. -/
def corridorRowAt (prog : CMProgram) (x y : ℕ) : Char :=
  match prog.getD y .halt with
  | .decz _ k =>
      let C := entryColumn prog y + 4
      if x = C then (if entryColumn prog k ≥ C then '>' else '<')
      else if x = entryColumn prog k then 'v' else ' '
  | .jump k =>
      let C := entryColumn prog y + 1
      if x = C then (if entryColumn prog k ≥ C then '>' else '<')
      else if x = entryColumn prog k then 'v' else ' '
  | _ => ' '

/-- A step through a space or a `v` while going down keeps the pointer down. -/
theorem step_down_cell (s : State w h) (hsm : s.stringMode = false) (hdir : s.dir = .down)
    (hcell : s.grid.get s.pc.1 s.pc.2 = ' ' ∨ s.grid.get s.pc.1 s.pc.2 = 'v') :
    step s = some { s with pc := stepPos w h .down s.pc } := by
  rcases hcell with hsp | hv
  · rw [step_space s hsm hsp]
    rw [hdir]
  · rw [step_dir_down s hsm hv]
    rw [hdir]

/-- Running down through spaces and `v`s keeps the pointer down. -/
theorem run_down (s : State w h) (n : ℕ) (x y : ℕ)
    (hsm : s.stringMode = false) (hpc : s.pc = (x % w, y % h))
    (hdir : s.dir = .down)
    (hdown : ∀ k : ℕ, k < n →
      s.grid.get (runPos w h k .down (x % w, y % h)).1 (runPos w h k .down (x % w, y % h)).2 = ' '
        ∨ s.grid.get (runPos w h k .down (x % w, y % h)).1 (runPos w h k .down (x % w, y % h)).2 = 'v') :
    run n s = some { s with pc := runPos w h n .down (x % w, y % h) } := by
  induction n with
  | zero =>
      rw [run]
      congr
      simp only [runPos, ← hpc]
  | succ n ih =>
      have hrun : run n s = some { s with pc := runPos w h n .down (x % w, y % h) } :=
        ih (fun k hk => hdown k (Nat.lt_trans hk (Nat.lt_succ_self n)))
      rw [show run (n + 1) s = (run n s).bind step by rfl]
      rw [hrun]
      change step { s with pc := runPos w h n .down (x % w, y % h) }
        = some { s with pc := runPos w h (n + 1) .down (x % w, y % h) }
      have hp : s.grid.get (runPos w h n .down (x % w, y % h)).1 (runPos w h n .down (x % w, y % h)).2 = ' '
          ∨ s.grid.get (runPos w h n .down (x % w, y % h)).1 (runPos w h n .down (x % w, y % h)).2 = 'v' :=
        hdown n (Nat.lt_succ_self n)
      rcases hp with hsp | hv
      · rw [show step { s with pc := runPos w h n .down (x % w, y % h) }
            = some { s with pc := runPos w h (n + 1) .down (x % w, y % h) } by
          unfold step
          have hdec : decodeChar ' ' = .nop := by unfold decodeChar; rfl
          simp only [hsm, hsp, hdec, stepState]
          rw [hdir]
          rfl]
      · rw [show step { s with pc := runPos w h n .down (x % w, y % h) }
            = some { s with pc := runPos w h (n + 1) .down (x % w, y % h) } by
          unfold step
          have hdec : decodeChar 'v' = .down := by unfold decodeChar; rfl
          simp only [hsm, hv, hdec, stepState]
          rw [hdir]
          rfl]

/-- A block body has no cell beyond its width. -/
theorem blockBodyAt_out (instr : CMInstr) (dx dy : ℕ) (hdx : blockWidth instr < dx) :
    blockBodyAt instr dx dy = ' ' := by
  cases instr with
  | inc c0 => fin_cases c0 <;> simp only [blockBodyAt, blockWidth] at hdx ⊢ <;> split_ifs <;> first | rfl | omega
  | decz c0 _ => fin_cases c0 <;> simp only [blockBodyAt, blockWidth] at hdx ⊢ <;> split_ifs <;> first | rfl | omega
  | jump _ => simp only [blockBodyAt, blockWidth] at hdx ⊢ <;> split_ifs <;> first | rfl | omega
  | halt => simp only [blockBodyAt, blockWidth] at hdx ⊢ <;> split_ifs <;> first | rfl | omega

end Completeness

end LeanFunge
