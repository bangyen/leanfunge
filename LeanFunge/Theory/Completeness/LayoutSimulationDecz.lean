/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanFunge.Theory.Completeness.LayoutCorridorRoute
import LeanFunge.Theory.Completeness.LayoutDecz
import LeanFunge.Theory.Completeness.LayoutDeczBranch
import LeanFunge.Theory.Completeness.LayoutRouting
import LeanFunge.Theory.Completeness.LayoutSimulation
import LeanFunge.Theory.Run.Relational
import LeanFunge.Theory.Step
import Mathlib.Tactic

/-!
# The `decz` Simulation

A `decz` block branches on the parity of the encoding: on an even encoding
(the counter positive) it decrements and falls through, on an odd encoding
(the counter zero) it routes through the corridor to its target.

## Theorems

* `sim_decz_zero`: A `decz` on a zero counter jumps through the corridor.
* `sim_decz_nonzero`: A `decz` on a positive counter decrements and falls
  through.
-/

namespace LeanFunge

namespace Completeness

open CMInstr

/-- A `decz` block on a zero counter routes through the corridor to its
    target, with the encoding unchanged. -/
theorem sim_decz_zero (prog : CMProgram) (i k : ℕ) (c : Fin 2) (hi1 : i + 1 < prog.length)
    (hwell : wellFormed prog) (hdecz : prog.getD i .halt = .decz c k)
    (s : State (playfieldWidth prog) (playfieldHeight prog))
    (hsm : s.stringMode = false) (hpc : s.pc = (entryColumn prog i, blockRow prog i))
    (hgrid : s.grid = playfieldOf prog)
    (hstack : s.stack = [encodeState { pc := i, c1 := c1, c2 := c2 }])
    (hz : read c { pc := i, c1 := c1, c2 := c2 } = 0) :
    run (5 + corridorSteps prog i k) s = some { s with
      stack := [encodeState { pc := k, c1 := c1, c2 := c2 }],
      pc := (entryColumn prog k, blockRow prog k),
      dir := .down } := by
  let cm : CMState := { pc := i, c1 := c1, c2 := c2 }
  have hnz : encodeState cm % counterVal c ≠ 0 := by
    intro h
    have hne : read c cm ≠ 0 := (encode_mod_zero c cm).mp h
    exact hne hz
  let s1 : State (playfieldWidth prog) (playfieldHeight prog) :=
    { s with
      dir := .right,
      stack := [encodeState cm % counterVal c, encodeState cm],
      pc := (entryColumn prog i + 4, blockRow prog i) }
  have h1 := deczBlock_prefix prog i hi1 hdecz s hsm hpc hstack hgrid
  have h1' : run 4 s = some s1 := by
    rw [h1]
  have hpc1 : s1.pc = (entryColumn prog i + 4, blockRow prog i) := by rfl
  have hstack1 : s1.stack = [encodeState cm % counterVal c, encodeState cm] := by rfl
  have h2 := deczBlock_jump prog i hi1 hdecz s1 hsm hpc1 hstack1 hgrid hnz
  let s2 : State (playfieldWidth prog) (playfieldHeight prog) :=
    { s with pc := (entryColumn prog i + 4, blockRow prog i - 1), dir := .up }
  have h2' : run 1 s1 = some s2 := by
    rw [h2]
    simpa [s1, s2, hstack, cm] -- no_squeeze: simulation
  have hpc2 : s2.pc = (branchColumn prog i, blockRow prog i - 1) := by
    dsimp [s2] -- no_squeeze: simulation
    rw [branchColumn, hdecz]
    norm_num [blockWidth]
  have hk : k < prog.length := hwell i (by omega) c k (Or.inl hdecz)
  have h3 := corridor_run prog i k c (by omega) hk hwell (Or.inl hdecz) s2 hsm hpc2 rfl hgrid
  have h12 : run (4 + 1) s = some s2 := by
    exact run_append s s1 (some s2) 4 1 h1' h2'
  have h123 : run (4 + 1 + corridorSteps prog i k) s = some { s with
      pc := (entryColumn prog k, blockRow prog k), dir := .down } := by
    exact run_append s s2 (some { s with pc := (entryColumn prog k, blockRow prog k), dir := .down })
      (4 + 1) (corridorSteps prog i k) h12 h3
  have htotal : 4 + 1 + corridorSteps prog i k = 5 + corridorSteps prog i k := by omega
  rw [← htotal]
  simpa [hstack] using h123 -- no_squeeze: simulation

/-- A `decz` block on a positive counter decrements and falls through to the
    next block. -/
theorem sim_decz_nonzero (prog : CMProgram) (i : ℕ) (c : Fin 2) (hi1 : i + 1 < prog.length)
    (hdecz : prog.getD i .halt = .decz c k)
    (s : State (playfieldWidth prog) (playfieldHeight prog))
    (hsm : s.stringMode = false) (hpc : s.pc = (entryColumn prog i, blockRow prog i))
    (hgrid : s.grid = playfieldOf prog)
    (hstack : s.stack = [encodeState { pc := i, c1 := c1, c2 := c2 }])
    (hnz : read c { pc := i, c1 := c1, c2 := c2 } ≠ 0) :
    run 10 s = some { s with
      stack := [encodeState (decCounter c { pc := i, c1 := c1, c2 := c2 })],
      pc := (entryColumn prog (i + 1), blockRow prog (i + 1)),
      dir := .down } := by
  let cm : CMState := { pc := i, c1 := c1, c2 := c2 }
  have hz' : encodeState cm % counterVal c = 0 := (encode_mod_zero c cm).mpr hnz
  let s1 : State (playfieldWidth prog) (playfieldHeight prog) :=
    { s with
      dir := .right,
      stack := [encodeState cm % counterVal c, encodeState cm],
      pc := (entryColumn prog i + 4, blockRow prog i) }
  have h1 := deczBlock_prefix prog i hi1 hdecz s hsm hpc hstack hgrid
  have h1' : run 4 s = some s1 := by
    rw [h1]
  have hpc1 : s1.pc = (entryColumn prog i + 4, blockRow prog i) := by rfl
  have hstack1 : s1.stack = [encodeState cm % counterVal c, encodeState cm] := by rfl
  have h2 := deczBlock_decrement prog i hi1 hdecz s1 hsm hpc1 hstack1 hgrid hz'
  let s2 : State (playfieldWidth prog) (playfieldHeight prog) :=
    { s with
      stack := [encodeState cm / counterVal c],
      pc := (entryColumn prog i + 5, blockRow prog i + 4),
      dir := .down }
  have h2' : run 5 s1 = some s2 := by
    rw [h2]
  have hpc2 : s2.pc = (entryColumn prog (i + 1), blockRow prog i + (blockHeight (prog.getD i .halt) - 1)) := by
    dsimp [s2] -- no_squeeze: simulation
    rw [hdecz]
    norm_num [blockHeight]
    rw [entryColumn_succ]
    rw [hdecz]
    norm_num [blockWidth]
  have h3 := fallthrough_drop prog i hi1 s2 hsm hpc2 rfl hgrid
  have h123 : run (4 + 5 + 1) s = some { s with
      stack := [encodeState (decCounter c cm)],
      pc := (entryColumn prog (i + 1), blockRow prog (i + 1)),
      dir := .down } := by
    have h12 : run (4 + 5) s = some s2 := by
      exact run_append s s1 (some s2) 4 5 h1' h2'
    have h3' : run 1 s2 = some { s with
        stack := [encodeState (decCounter c cm)],
        pc := (entryColumn prog (i + 1), blockRow prog (i + 1)),
        dir := .down } := by
      simpa [encode_deczCounter c cm hnz] using h3 -- no_squeeze: simulation
    exact run_append s s2 (some { s with
      stack := [encodeState (decCounter c cm)],
      pc := (entryColumn prog (i + 1), blockRow prog (i + 1)),
      dir := .down }) (4 + 5) 1 h12 h3'
  have htotal : 4 + 5 + 1 = 10 := by omega
  rw [← htotal]
  simpa using h123 -- no_squeeze: simulation

end Completeness

end LeanFunge
