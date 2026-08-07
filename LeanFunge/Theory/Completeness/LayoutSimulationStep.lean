/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanFunge.Theory.Completeness.LayoutCorridorRoute
import LeanFunge.Theory.Completeness.LayoutJumpBlock
import LeanFunge.Theory.Completeness.LayoutRouting
import LeanFunge.Theory.Completeness.LayoutSimulationBlock
import LeanFunge.Theory.Run.Relational
import LeanFunge.Theory.Step
import Mathlib.Tactic

/-!
# The Per-Instruction Simulation

Each two-counter machine instruction, executed from a block's entry with the
encoded pair on the stack, produces a playfield run to the successor block's
entry with the encoded successor state (or stops, for `halt`). The block run
is composed with the fall-through drop or the corridor jump.

## Main definitions

* `blockEntry`: The playfield position of a block's entry.

## Theorems

* `sim_inc`: An `inc` block increments a counter and falls through.
* `sim_jump`: A `jump` block routes through the corridor.
* `sim_halt`: A `halt` block stops the machine.
-/

namespace LeanFunge

namespace Completeness

open CMInstr

/-- The playfield position of a block's entry. -/
def blockEntry (prog : CMProgram) (pc : ℕ) : ℕ × ℕ :=
  (entryColumn prog pc, blockRow prog pc)

/-- An `inc` block increments a counter and falls through to the next block. -/
theorem sim_inc (prog : CMProgram) (i : ℕ) (c : Fin 2) (hi1 : i + 1 < prog.length)
    (hinc : prog.getD i .halt = .inc c)
    (s : State (playfieldWidth prog) (playfieldHeight prog))
    (hsm : s.stringMode = false) (hpc : s.pc = (entryColumn prog i, blockRow prog i))
    (hgrid : s.grid = playfieldOf prog)
    (hstack : s.stack = [encodeState { pc := i, c1 := c1, c2 := c2 }]) :
    run 5 s = some { s with
      stack := [encodeState (incCounter c { pc := i, c1 := c1, c2 := c2 })],
      pc := (entryColumn prog (i + 1), blockRow prog (i + 1)),
      dir := .down } := by
  let cm : CMState := { pc := i, c1 := c1, c2 := c2 }
  let s1 : State (playfieldWidth prog) (playfieldHeight prog) :=
    { s with
      stack := [encodeState (incCounter c cm)],
      pc := (entryColumn prog (i + 1), blockRow prog i + 1),
      dir := .down }
  have h1 := incBlock_run prog i hi1 hinc s hsm hpc hstack hgrid
  have h1' : run 4 s = some s1 := by
    rw [h1]
    congr 1
    dsimp [s1] -- no_squeeze: simulation
    rw [encode_incCounter c cm]
  have hpc1 : s1.pc = (entryColumn prog (i + 1), blockRow prog i + (blockHeight (prog.getD i .halt) - 1)) := by
    dsimp [s1] -- no_squeeze: simulation
    rw [hinc]
    norm_num [blockHeight]
  have h2 := fallthrough_drop prog i hi1 s1 hsm hpc1 rfl hgrid
  have h12 : run (4 + 1) s = some { s with
      stack := [encodeState (incCounter c cm)],
      pc := (entryColumn prog (i + 1), blockRow prog (i + 1)),
      dir := .down } := by
    exact run_append s s1 (some { s with
      stack := [encodeState (incCounter c cm)],
      pc := (entryColumn prog (i + 1), blockRow prog (i + 1)),
      dir := .down }) 4 1 h1' h2
  rw [show 5 = 4 + 1 by omega]
  exact h12

/-- A `jump` block routes the pointer through the corridor to its target. -/
theorem sim_jump (prog : CMProgram) (i k : ℕ) (hi1 : i + 1 < prog.length)
    (hwell : wellFormed prog) (hjump : prog.getD i .halt = .jump k)
    (s : State (playfieldWidth prog) (playfieldHeight prog))
    (hsm : s.stringMode = false) (hpc : s.pc = (entryColumn prog i, blockRow prog i))
    (hgrid : s.grid = playfieldOf prog)
    (hstack : s.stack = [encodeState { pc := i, c1 := c1, c2 := c2 }]) :
    run (2 + corridorSteps prog i k) s = some { s with
      stack := [encodeState { pc := k, c1 := c1, c2 := c2 }],
      pc := (entryColumn prog k, blockRow prog k),
      dir := .down } := by
  let cm : CMState := { pc := i, c1 := c1, c2 := c2 }
  have hk : k < prog.length := hwell i (by omega) 0 k (Or.inr hjump)
  let s1 : State (playfieldWidth prog) (playfieldHeight prog) :=
    { s with pc := (entryColumn prog i + 1, blockRow prog i - 1), dir := .up }
  have h1 := jumpBlock_run prog i (by omega) hjump s hsm hpc hgrid
  have h1' : run 2 s = some s1 := by
    simpa [s1] using h1 -- no_squeeze: simulation
  have hpc1 : s1.pc = (branchColumn prog i, blockRow prog i - 1) := by
    dsimp [s1] -- no_squeeze: simulation
    rw [branchColumn, hjump]
    norm_num [blockWidth]
  have h2 := corridor_run prog i k 0 (by omega) hk hwell (Or.inr hjump) s1 hsm hpc1 rfl hgrid
  have h12 : run (2 + corridorSteps prog i k) s = some { s with
      stack := [encodeState { pc := k, c1 := c1, c2 := c2 }],
      pc := (entryColumn prog k, blockRow prog k),
      dir := .down } := by
    dsimp [cm] -- no_squeeze: simulation
    simpa [hstack] using (run_append s s1 -- no_squeeze: simulation
      (some { s with pc := (entryColumn prog k, blockRow prog k), dir := .down })
      2 (corridorSteps prog i k) h1' h2)
  exact h12

/-- A `halt` block stops the machine. -/
theorem sim_halt (prog : CMProgram) (i : ℕ) (hi : i < prog.length)
    (hhalt : prog.getD i .halt = .halt)
    (s : State (playfieldWidth prog) (playfieldHeight prog))
    (hsm : s.stringMode = false) (hpc : s.pc = (entryColumn prog i, blockRow prog i))
    (hgrid : s.grid = playfieldOf prog) :
    run 2 s = none :=
  haltBlockRun prog i hi hhalt s hsm hpc hgrid

end Completeness

end LeanFunge
