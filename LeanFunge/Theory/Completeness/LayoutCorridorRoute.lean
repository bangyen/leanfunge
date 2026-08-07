/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanFunge.Theory.Completeness.LayoutCorridorLeft
import LeanFunge.Theory.Completeness.LayoutCorridorRight
import LeanFunge.Theory.Run.Relational
import Mathlib.Tactic

/-!
# The Corridor Route

A jump edge routes the pointer up its branch column to the header, across the
corridor row, and down to the target block. `corridor_run` dispatches on the
relative position of the target: `corridorRunRight` routes a target at or
beyond the branch column, `corridorRunLeft` one before it.

## Theorems

* `corridor_run`: The up-turn, along-drop, and down segments route the pointer
  from the branch cell to the target's entry.
-/

namespace LeanFunge

namespace Completeness

/-- The up-turn, along-drop, and down segments route the pointer from a jump
    edge's branch cell to the target block's entry. -/
theorem corridor_run (prog : CMProgram) (i k : ℕ) (c : Fin 2)
    (hi : i < prog.length) (hk : k < prog.length) (hwell : wellFormed prog)
    (hget : prog.getD i .halt = .decz c k ∨ prog.getD i .halt = .jump k)
    (s : State (playfieldWidth prog) (playfieldHeight prog))
    (hsm : s.stringMode = false) (hpc : s.pc = (branchColumn prog i, blockRow prog i - 1))
    (hdir : s.dir = .up) (hgrid : s.grid = playfieldOf prog) :
    run ((blockRow prog i - i)
        + (if entryColumn prog k ≥ branchColumn prog i then entryColumn prog k - branchColumn prog i
           else branchColumn prog i - entryColumn prog k)
        + (blockRow prog k - i - 1)) s =
      some { s with pc := (entryColumn prog k, blockRow prog k), dir := .down } := by
  by_cases hge : entryColumn prog k ≥ branchColumn prog i
  · have h := corridorRunRight prog i k c hi hk hwell hget s hsm hpc hdir hgrid hge
    rw [show (blockRow prog i - i)
        + (if entryColumn prog k ≥ branchColumn prog i then entryColumn prog k - branchColumn prog i
           else branchColumn prog i - entryColumn prog k)
        + (blockRow prog k - i - 1)
        = (blockRow prog i - i) + (entryColumn prog k - branchColumn prog i) + (blockRow prog k - i - 1) by
      simp [hge]] -- no_squeeze: corridor route
    exact h
  · have h := corridorRunLeft prog i k c hi hk hwell hget s hsm hpc hdir hgrid hge
    rw [show (blockRow prog i - i)
        + (if entryColumn prog k ≥ branchColumn prog i then entryColumn prog k - branchColumn prog i
           else branchColumn prog i - entryColumn prog k)
        + (blockRow prog k - i - 1)
        = (blockRow prog i - i) + (branchColumn prog i - entryColumn prog k) + (blockRow prog k - i - 1) by
      simp [hge]] -- no_squeeze: corridor route
    exact h

end Completeness

end LeanFunge
