/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanFunge.Theory.Completeness.Layout
import LeanFunge.Theory.Completeness.LayoutBlock
import LeanFunge.Theory.Completeness.LayoutCells
import LeanFunge.Theory.Completeness.LayoutCorridor
import LeanFunge.Theory.Completeness.LayoutRouting
import LeanFunge.Theory.Completeness.PairEncoding
import LeanFunge.Theory.Completeness.TwoCounter
import LeanFunge.Theory.Run.Relational
import LeanFunge.Theory.Step
import Mathlib.Tactic
/-!
# The Simulation of Two-Counter Machines

The two-counter machine state is encoded as the single stack value

`2^c1 * 3^c2`, and the counter updates translate into stack arithmetic. This

module proves the encoding-level lemmas the simulation needs, and the step

count of a corridor jump.

The `halt` block stops the machine wherever it sits, including as the last

block of the playfield, where the cell lookups need `≤` bounds instead of the

strict ones that hold for interior blocks.

Each two-counter machine instruction, executed from a block's entry with the

encoded pair on the stack, produces a playfield run to the successor block's

entry with the encoded successor state (or stops, for `halt`). The block run

is composed with the fall-through drop or the corridor jump.

A `decz` block branches on the parity of the encoding: on an even encoding

(the counter positive) it decrements and falls through, on an odd encoding

(the counter zero) it routes through the corridor to its target.

One two-counter machine step corresponds to a playfield run from a block's

entry to the successor block with the successor state's encoding, or stops for

a `halt`. The successor's program counter is shown to stay in bounds.

The machine run is simulated by the playfield run: the playfield reaches the

successor block with the successor state's encoding, or stops when the machine

stops. The universality corollaries project the simulation to the pointer

position and stack, and lift halting from the machine to the playfield.

## Definitions

* `encodeState`: The stack value encoding a two-counter machine state.

* `corridorSteps`: The number of playfield steps a corridor jump takes.

* `wellPlaced`: A well-formed program whose last instruction is `halt`, so no

  fall-through runs off the end of the playfield.

* `blockEntry`: The playfield position of a block's entry.

* `afterState`: The playfield state after executing a block, at the successor

  entry with the successor's encoding.

* `playfieldStart`: The playfield start state for a two-counter machine state.

## Theorems

* `encode_incCounter`: Incrementing a counter multiplies the encoding by its digit.

* `encode_deczCounter`: Decrementing a positive counter divides the encoding by its digit.

* `encode_mod_zero`: The encoding's remainder tests whether the counter is positive.

* `corridorSteps_pos`: A corridor jump takes at least one step.

* `lastCellAt_halt_body`: The body readback of a `halt` block at an in-range offset.

* `playfield_halt_get`: The cells of a `halt` block read back its body.

* `haltBlockRun`: A `halt` block stops the machine.

* `sim_inc`: An `inc` block increments a counter and falls through.

* `sim_jump`: A `jump` block routes through the corridor.

* `sim_halt`: A `halt` block stops the machine.

* `sim_decz_zero`: A `decz` on a zero counter jumps through the corridor.

* `sim_decz_nonzero`: A `decz` on a positive counter decrements and falls

  through.

* `step_pc_lt`: A machine step stays within the program.

* `sim_step`: One machine step is a playfield run to the successor entry.

* `sim_run`: The machine run is simulated by the playfield run.

* `simulation_map`: The playfield run reflects the machine run's positions and

  encodings.

* `simulation_halts`: If the machine halts, the playfield halts.

-/
namespace LeanFunge

namespace Completeness

open CMInstr

/-- The stack value encoding a two-counter machine state. -/
def encodeState (s : CMState) : Int :=
  Int.ofNat (encode s.c1 s.c2)

/-- The number of playfield steps a corridor jump edge takes. -/
def corridorSteps (prog : CMProgram) (i k : ℕ) : ℕ :=
  (blockRow prog i - i)
    + (if entryColumn prog k ≥ branchColumn prog i then
         entryColumn prog k - branchColumn prog i
       else branchColumn prog i - entryColumn prog k)
    + (blockRow prog k - i - 1)

/-- A well-formed program whose last instruction is `halt`, so no fall-through
    runs off the end of the playfield. -/
def wellPlaced (prog : CMProgram) : Prop :=
  wellFormed prog ∧ ∀ i : ℕ, i < prog.length → instrAt prog i = .halt ∨ i + 1 < prog.length

/-- Incrementing a counter multiplies the encoding by its digit. -/
theorem encode_incCounter (c : Fin 2) (s : CMState) :
    encodeState (incCounter c s) = encodeState s * counterVal c := by
  fin_cases c
  · simpa [encodeState, incCounter, write, CMInstr.read, counterVal] using (encode_inc_c1_int s.c1 s.c2).symm -- no_squeeze: simulation
  · simpa [encodeState, incCounter, write, CMInstr.read, counterVal] using (encode_inc_c2_int s.c1 s.c2).symm -- no_squeeze: simulation

/-- Decrementing a positive counter divides the encoding by its digit. -/
theorem encode_deczCounter (c : Fin 2) (s : CMState) (h : CMInstr.read c s ≠ 0) :
    encodeState (decCounter c s) = encodeState s / counterVal c := by
  fin_cases c
  · have h1 : 0 < s.c1 := by
      have : s.c1 ≠ 0 := by simpa [CMInstr.read] using h -- no_squeeze: simulation
      omega
    simpa [encodeState, decCounter, write, CMInstr.read, counterVal, h1] using (encode_decz_c1_int s.c1 s.c2 h1).symm -- no_squeeze: simulation
  · have h2 : 0 < s.c2 := by
      have : s.c2 ≠ 0 := by simpa [CMInstr.read] using h -- no_squeeze: simulation
      omega
    simpa [encodeState, decCounter, write, CMInstr.read, counterVal, h2] using (encode_decz_c2_int s.c1 s.c2 h2).symm -- no_squeeze: simulation

/-- The encoding's remainder tests whether the counter is positive. -/
theorem encode_mod_zero (c : Fin 2) (s : CMState) :
    encodeState s % counterVal c = 0 ↔ CMInstr.read c s ≠ 0 := by
  fin_cases c
  · simp [encodeState, counterVal, CMInstr.read] -- no_squeeze: simulation
    have hdvd : (2 : Int) ∣ (encode s.c1 s.c2 : Int) ↔ (2 : ℕ) ∣ encode s.c1 s.c2 := by
      simpa using (Int.natCast_dvd_natCast (m := 2) (n := encode s.c1 s.c2)) -- no_squeeze: simulation
    rw [hdvd]
    have h := encode_c1_pos s.c1 s.c2
    rw [Nat.dvd_iff_mod_eq_zero, h.symm]
    omega
  · simp [encodeState, counterVal, CMInstr.read] -- no_squeeze: simulation
    have hdvd : (3 : Int) ∣ (encode s.c1 s.c2 : Int) ↔ (3 : ℕ) ∣ encode s.c1 s.c2 := by
      simpa using (Int.natCast_dvd_natCast (m := 3) (n := encode s.c1 s.c2)) -- no_squeeze: simulation
    rw [hdvd]
    have h := encode_c2_pos s.c1 s.c2
    rw [Nat.dvd_iff_mod_eq_zero, h.symm]
    omega

/-- A corridor jump takes at least one step. -/
theorem corridorSteps_pos (prog : CMProgram) (i : ℕ) (hi : i < prog.length) (k : ℕ) :
    1 ≤ corridorSteps prog i k := by
  dsimp [corridorSteps] -- no_squeeze: simulation
  have hge : prog.length ≤ blockRow prog i := blockRow_ge_length prog i
  omega

/-- The body readback of a `halt` block, at any in-range offset. -/
lemma lastCellAt_halt_body (w h D y dx dy : ℕ) (hdx : dx < 2) (hdy : dy < 2)
    (hD : D < w) (hD1 : D + 1 < w) (hy : y < h) (hy1 : y + 1 < h) :
    lastCellAt w h ' ' [((D, y), '>'), ((D + 1, y), '@')] (D + dx) (y + dy)
      = blockBodyAt .halt dx dy := by
  have hmodD : D % w = D := Nat.mod_eq_of_lt hD
  have hmodD1 : (D + 1) % w = D + 1 := Nat.mod_eq_of_lt hD1
  have hmodDx : (D + dx) % w = D + dx := Nat.mod_eq_of_lt (by omega)
  have hmodY : y % h = y := Nat.mod_eq_of_lt hy
  have hmodYdy : (y + dy) % h = y + dy := Nat.mod_eq_of_lt (by omega)
  interval_cases dx <;> interval_cases dy
  <;> simp [blockBodyAt, lastCellAt, hmodD, hmodD1, hmodDx, hmodY, hmodYdy] -- no_squeeze: halt body

/-- The cells of a `halt` block read back its body, at any block position. -/
theorem playfield_halt_get (prog : CMProgram) (i : ℕ) (hi : i < prog.length)
    (hhalt : prog.getD i .halt = .halt) (dx dy : ℕ) (hdx : dx < 2) (hdy : dy < 2) :
    (playfieldOf prog).get (entryColumn prog i + dx) (blockRow prog i + dy)
      = blockBodyAt .halt dx dy := by
  let pw := playfieldWidth prog
  let ph := playfieldHeight prog
  have hW : entryColumn prog i + 2 ≤ pw := by
    dsimp [pw] -- no_squeeze: simulation
    rw [playfieldWidth]
    have hmono : entryColumn prog (i + 1) ≤ entryColumn prog prog.length :=
      entryColumn_mono prog (i + 1) prog.length (by omega)
    rw [entryColumn_succ] at hmono
    rw [hhalt] at hmono
    norm_num [blockWidth] at hmono
    omega
  have hH0 : blockRow prog i + 2 ≤ ph := by
    dsimp [ph] -- no_squeeze: simulation
    rw [playfieldHeight]
    have hmono : blockRow prog (i + 1) ≤ blockRow prog prog.length :=
      blockRow_mono prog (i := i + 1) (j := prog.length) (by omega)
    rw [blockRow_succ] at hmono
    rw [hhalt] at hmono
    norm_num [blockHeight] at hmono
    omega
  have hH : blockRow prog i + dy < ph := by omega
  rw [playfieldOf_get_eq_lastCellAt]
  unfold playfieldCells
  have hmain : ∀ k : ℕ, i < k → k ≤ prog.length →
      lastCellAt pw ph ' ' (List.flatMap (fun j => blockCellList prog j) (List.range k))
        (entryColumn prog i + dx) (blockRow prog i + dy)
        = blockBodyAt .halt dx dy := by
    intro k hik hkn
    induction k with
    | zero => omega
    | succ k ih =>
        by_cases hik' : i < k
        · have hprev := ih hik' (by omega)
          rw [flatMap_range_succ, lastCellAt_append, hprev]
          have hdyb : dy < blockHeight (prog.getD i .halt) := by
            rw [hhalt]
            norm_num [blockHeight]
            exact hdy
          exact lastCellAt_block_after prog i k dx dy (by omega) (by omega) hdyb hH
              (blockBodyAt .halt dx dy)
        · have heq : i = k := by omega
          subst i
          rw [flatMap_range_succ, lastCellAt_append]
          rw [lastCellAt_flatMap_before prog k (by omega) dx dy (by omega)]
          have hbody : lastCellAt pw ph ' ' (blockCellList prog k)
              (entryColumn prog k + dx) (blockRow prog k + dy) = blockBodyAt .halt dx dy := by
            rw [blockCellList_eq, hhalt]
            simp only [blockCorridorCells]
            have hD : entryColumn prog k < pw := by omega
            have hD1 : entryColumn prog k + 1 < pw := by omega
            have hy : blockRow prog k < ph := by omega
            have hy1 : blockRow prog k + 1 < ph := by omega
            simpa [blockBodyCells] using (lastCellAt_halt_body pw ph (entryColumn prog k) -- no_squeeze: simulation
              (blockRow prog k) dx dy hdx hdy hD hD1 hy hy1)
          exact hbody
  have hres := hmain prog.length (by omega) (by rfl)
  rw [hres]

/-- A `halt` block stops the machine, wherever it sits. -/
theorem haltBlockRun (prog : CMProgram) (i : ℕ) (hi : i < prog.length)
    (hhalt : prog.getD i .halt = .halt)
    (s : State (playfieldWidth prog) (playfieldHeight prog))
    (hsm : s.stringMode = false) (hpc : s.pc = (entryColumn prog i, blockRow prog i))
    (hgrid : s.grid = playfieldOf prog) :
    run 2 s = none := by
  have hW : entryColumn prog i + 1 < playfieldWidth prog := by
    have hle : entryColumn prog i + 2 ≤ playfieldWidth prog := by
      rw [playfieldWidth]
      have hmono : entryColumn prog (i + 1) ≤ entryColumn prog prog.length :=
        entryColumn_mono prog (i + 1) prog.length (by omega)
      rw [entryColumn_succ] at hmono
      rw [hhalt] at hmono
      norm_num [blockWidth] at hmono
      omega
    omega
  have hH : blockRow prog i < playfieldHeight prog := by
    have hle : blockRow prog i + 2 ≤ playfieldHeight prog := by
      rw [playfieldHeight]
      have hmono : blockRow prog (i + 1) ≤ blockRow prog prog.length :=
        blockRow_mono prog (i := i + 1) (j := prog.length) (by omega)
      rw [blockRow_succ] at hmono
      rw [hhalt] at hmono
      norm_num [blockHeight] at hmono
      omega
    omega
  have hc0 : s.grid.get (entryColumn prog i) (blockRow prog i) = '>' := by
    rw [hgrid]
    have h := playfield_halt_get prog i hi hhalt 0 0 (by norm_num) (by norm_num)
    simpa only [blockBodyAt] using h
  have hc1 : s.grid.get (entryColumn prog i + 1) (blockRow prog i) = '@' := by
    rw [hgrid]
    have h := playfield_halt_get prog i hi hhalt 1 0 (by norm_num) (by norm_num)
    simpa only [blockBodyAt] using h
  have h1 : run 1 s = some { s with dir := .right, pc := (entryColumn prog i + 1, blockRow prog i) } := by
    rw [show run 1 s = step s by rfl]
    unfold step
    have hdec : decodeChar '>' = .right := by unfold decodeChar; rfl
    simp only [hsm, hpc, hc0, hdec, stepState]
    rw [stepPos_right (playfieldWidth prog) (playfieldHeight prog) (entryColumn prog i) (blockRow prog i) hW hH]
  have h2 : run 1 { s with dir := .right, pc := (entryColumn prog i + 1, blockRow prog i) } = none := by
    rw [show run 1 { s with dir := .right, pc := (entryColumn prog i + 1, blockRow prog i) } = step { s with dir := .right, pc := (entryColumn prog i + 1, blockRow prog i) } by rfl]
    unfold step
    have hdec : decodeChar '@' = .halt := by unfold decodeChar; rfl
    simp only [hsm, hc1, hdec, stepState]
  have h12 : run (1 + 1) s = none := by
    exact run_append s { s with dir := .right, pc := (entryColumn prog i + 1, blockRow prog i) } none 1 1 h1 h2
  rw [show 2 = 1 + 1 by omega]
  exact h12

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

open CMInstr

/-- The playfield state after executing a block: the successor entry with the
    successor state's encoding. -/
def afterState (prog : CMProgram)
    (s₀ : State (playfieldWidth prog) (playfieldHeight prog)) (s' : CMState) :
    State (playfieldWidth prog) (playfieldHeight prog) :=
  { s₀ with stack := [encodeState s'], pc := blockEntry prog s'.pc, dir := .down }

/-- The playfield start state for a two-counter machine state. -/
def playfieldStart (prog : CMProgram) (s₀ : CMState) : State (playfieldWidth prog) (playfieldHeight prog) :=
  { State.init (playfieldOf prog) with
    stack := [encodeState s₀],
    pc := blockEntry prog s₀.pc,
    dir := .down }

/-- A machine step stays within the program. -/
theorem step_pc_lt (prog : CMProgram) (hwellPlaced : wellPlaced prog) (s₀ : CMState)
    (hs₀ : s₀.pc < prog.length) :
    ∀ s', CMInstr.step prog s₀ = some s' → s'.pc < prog.length := by
  cases hget : CMInstr.instrAt prog s₀.pc with
  | inc c =>
      intro s' hstep
      have hs := CMInstr.step_inc prog s₀ c hget
      rw [hstep] at hs
      injection hs with hs'
      rw [hs']
      have hfall := (hwellPlaced.2 s₀.pc hs₀)
      rcases hfall with hh | hf
      · exfalso
        have : CMInstr.instrAt prog s₀.pc ≠ .halt := by
          rw [hget]
          intro h
          cases h
        exact this hh
      · simpa [CMInstr.incCounter, CMInstr.write, CMInstr.read] -- no_squeeze: simulation
  | decz c k =>
      intro s' hstep
      by_cases hz : CMInstr.read c s₀ = 0
      · have hs := CMInstr.step_decz_zero prog s₀ c k hget hz
        rw [hstep] at hs
        injection hs with hs'
        rw [hs']
        have hk : k < prog.length := (hwellPlaced.1) s₀.pc hs₀ c k (Or.inl (by simpa [CMInstr.instrAt] using hget)) -- no_squeeze: simulation
        simpa -- no_squeeze: simulation
      · have hs := CMInstr.step_decz_nonzero prog s₀ c k hget hz
        rw [hstep] at hs
        injection hs with hs'
        rw [hs']
        have hfall := (hwellPlaced.2 s₀.pc hs₀)
        rcases hfall with hh | hf
        · exfalso
          have : CMInstr.instrAt prog s₀.pc ≠ .halt := by
            rw [hget]
            intro h
            cases h
          exact this hh
        · simpa [CMInstr.decCounter, CMInstr.write, CMInstr.read] -- no_squeeze: simulation
  | jump k =>
      intro s' hstep
      have hs := CMInstr.step_jump prog s₀ k hget
      rw [hstep] at hs
      injection hs with hs'
      rw [hs']
      have hk : k < prog.length := (hwellPlaced.1) s₀.pc hs₀ 0 k (Or.inr (by simpa [CMInstr.instrAt] using hget)) -- no_squeeze: simulation
      simpa -- no_squeeze: simulation
  | halt =>
      intro s' hstep
      rw [CMInstr.step_halt prog s₀ hget] at hstep
      cases hstep

/-- One machine step is a playfield run to the successor entry. -/
theorem sim_step (prog : CMProgram) (hwell : wellFormed prog) (s₀ : CMState)
    (hs₀ : s₀.pc < prog.length) (hfall : s₀.pc + 1 < prog.length ∨ CMInstr.instrAt prog s₀.pc = .halt)
    (s : State (playfieldWidth prog) (playfieldHeight prog))
    (hsm : s.stringMode = false) (hpc : s.pc = blockEntry prog s₀.pc)
    (hgrid : s.grid = playfieldOf prog) (hstack : s.stack = [encodeState s₀]) :
    match CMInstr.step prog s₀ with
    | some s' => ∃ n, run n s = some (afterState prog s s')
    | none => run 2 s = none := by
  cases hget : CMInstr.instrAt prog s₀.pc with
  | inc c =>
      have hinc : prog.getD s₀.pc .halt = .inc c := by simpa [CMInstr.instrAt] using hget -- no_squeeze: simulation
      have hs := CMInstr.step_inc prog s₀ c hget
      rw [hs]
      have hi1 : s₀.pc + 1 < prog.length := by
        rcases hfall with hf | hh
        · exact hf
        · exfalso
          have : CMInstr.instrAt prog s₀.pc ≠ .halt := by
            rw [hget]
            intro h
            cases h
          exact this hh
      have hrun := sim_inc prog s₀.pc c hi1 hinc s hsm hpc hgrid hstack
      refine ⟨5, ?_⟩
      simpa [afterState, blockEntry] using hrun -- no_squeeze: simulation
  | decz c k =>
      have hdecz : prog.getD s₀.pc .halt = .decz c k := by simpa [CMInstr.instrAt] using hget -- no_squeeze: simulation
      by_cases hz : CMInstr.read c s₀ = 0
      · have hs := CMInstr.step_decz_zero prog s₀ c k hget hz
        rw [hs]
        have hi1 : s₀.pc + 1 < prog.length := by
          rcases hfall with hf | hh
          · exact hf
          · exfalso
            have : CMInstr.instrAt prog s₀.pc ≠ .halt := by
              rw [hget]
              intro h
              cases h
            exact this hh
        have hrun := sim_decz_zero prog s₀.pc k c hi1 hwell hdecz s hsm hpc hgrid hstack hz
        refine ⟨5 + corridorSteps prog s₀.pc k, ?_⟩
        simpa [afterState, blockEntry] using hrun -- no_squeeze: simulation
      · have hs := CMInstr.step_decz_nonzero prog s₀ c k hget hz
        rw [hs]
        have hi1 : s₀.pc + 1 < prog.length := by
          rcases hfall with hf | hh
          · exact hf
          · exfalso
            have : CMInstr.instrAt prog s₀.pc ≠ .halt := by
              rw [hget]
              intro h
              cases h
            exact this hh
        have hrun := sim_decz_nonzero prog s₀.pc c hi1 hdecz s hsm hpc hgrid hstack hz
        refine ⟨10, ?_⟩
        simpa [afterState, blockEntry] using hrun -- no_squeeze: simulation
  | jump k =>
      have hjump : prog.getD s₀.pc .halt = .jump k := by simpa [CMInstr.instrAt] using hget -- no_squeeze: simulation
      have hs := CMInstr.step_jump prog s₀ k hget
      rw [hs]
      have hi1 : s₀.pc + 1 < prog.length := by
        rcases hfall with hf | hh
        · exact hf
        · exfalso
          have : CMInstr.instrAt prog s₀.pc ≠ .halt := by
            rw [hget]
            intro h
            cases h
          exact this hh
      have hrun := sim_jump prog s₀.pc k hi1 hwell hjump s hsm hpc hgrid hstack
      refine ⟨2 + corridorSteps prog s₀.pc k, ?_⟩
      simpa [afterState, blockEntry] using hrun -- no_squeeze: simulation
  | halt =>
      have hhalt : prog.getD s₀.pc .halt = .halt := by simpa [CMInstr.instrAt] using hget -- no_squeeze: simulation
      have hs := CMInstr.step_halt prog s₀ hget
      rw [hs]
      have hrun := sim_halt prog s₀.pc hs₀ hhalt s hsm hpc hgrid
      exact hrun

open CMInstr

/-- The machine run is simulated by the playfield run: the playfield reaches
    the successor block with the successor state's encoding, or stops. -/
theorem sim_run (prog : CMProgram) (hwellPlaced : wellPlaced prog) (s₀ : CMState)
    (hs₀ : s₀.pc < prog.length) (n : ℕ) :
    ∃ m, run m (playfieldStart prog s₀)
        = (CMInstr.run prog n s₀).map (fun s' => afterState prog (playfieldStart prog s₀) s')
      ∧ ∀ s', CMInstr.run prog n s₀ = some s' → s'.pc < prog.length := by
  induction n with
  | zero =>
      refine ⟨0, ?_, ?_⟩
      · rw [show run 0 (playfieldStart prog s₀) = some (playfieldStart prog s₀) by rfl]
        rw [show CMInstr.run prog 0 s₀ = some s₀ by rfl]
        simp [playfieldStart, afterState, blockEntry] -- no_squeeze: simulation
      · intro s' h
        have h' : s' = s₀ := by
          simpa [CMInstr.run] using h.symm -- no_squeeze: simulation
        subst s'
        exact hs₀
  | succ n ih =>
      rcases ih with ⟨mₙ, hrunₙ, hbₙ⟩
      by_cases hnone : CMInstr.run prog n s₀ = none
      · refine ⟨mₙ, ?_, ?_⟩
        · rw [hrunₙ, CMInstr.run_succ, hnone]
          simp -- no_squeeze: simulation
        · intro s' h
          rw [CMInstr.run_succ, hnone] at h
          simp at h -- no_squeeze: simulation
      · have hsome : ∃ sₙ, CMInstr.run prog n s₀ = some sₙ := by
          by_contra h
          have hnone' : CMInstr.run prog n s₀ = none := by
            cases h2 : CMInstr.run prog n s₀ with
            | none => rfl
            | some sₙ => exact False.elim (h ⟨sₙ, h2⟩)
          exact hnone hnone'
        rcases hsome with ⟨sₙ, hrunₙ'⟩
        have hsm : (playfieldStart prog s₀).stringMode = false := rfl
        have hgrid : (playfieldStart prog s₀).grid = playfieldOf prog := rfl
        have hfall : sₙ.pc + 1 < prog.length ∨ CMInstr.instrAt prog sₙ.pc = .halt :=
          Or.symm (hwellPlaced.2 sₙ.pc (hbₙ sₙ hrunₙ'))
        have hstep := sim_step prog (hwellPlaced.1) sₙ (hbₙ sₙ hrunₙ') hfall
          (afterState prog (playfieldStart prog s₀) sₙ) hsm rfl hgrid rfl
        cases hstep2 : CMInstr.step prog sₙ with
        | none =>
            have hnone' : CMInstr.step prog sₙ = none := hstep2
            have hrun2 : run 2 (afterState prog (playfieldStart prog s₀) sₙ) = none := by
              simpa [hnone'] using hstep -- no_squeeze: simulation
            have hreach : run mₙ (playfieldStart prog s₀) = some (afterState prog (playfieldStart prog s₀) sₙ) := by
              rw [hrunₙ, hrunₙ']
              simp -- no_squeeze: simulation
            refine ⟨mₙ + 2, ?_, ?_⟩
            · have hcomp : run (mₙ + 2) (playfieldStart prog s₀) = none := by
                exact run_append (playfieldStart prog s₀) (afterState prog (playfieldStart prog s₀) sₙ) none mₙ 2 hreach hrun2
              rw [hcomp]
              rw [CMInstr.run_succ, hrunₙ']
              simp [hnone'] -- no_squeeze: simulation
            · intro s' h
              rw [CMInstr.run_succ, hrunₙ'] at h
              simp [hnone'] at h -- no_squeeze: simulation
        | some s' =>
            have hs' := hstep
            rw [hstep2] at hs'
            rcases hs' with ⟨n', hrun'⟩
            have hlt' : s'.pc < prog.length :=
              step_pc_lt prog hwellPlaced sₙ (hbₙ sₙ hrunₙ') s' hstep2
            have hreach : run mₙ (playfieldStart prog s₀) = some (afterState prog (playfieldStart prog s₀) sₙ) := by
              rw [hrunₙ, hrunₙ']
              simp -- no_squeeze: simulation
            refine ⟨mₙ + n', ?_, ?_⟩
            · have hcomp : run (mₙ + n') (playfieldStart prog s₀) = some (afterState prog (playfieldStart prog s₀) s') := by
                have hcomp' : run (mₙ + n') (playfieldStart prog s₀)
                    = some (afterState prog (afterState prog (playfieldStart prog s₀) sₙ) s') := by
                  exact run_append (playfieldStart prog s₀) (afterState prog (playfieldStart prog s₀) sₙ)
                    (some (afterState prog (afterState prog (playfieldStart prog s₀) sₙ) s')) mₙ n' hreach hrun'
                simpa [afterState] using hcomp' -- no_squeeze: simulation
              rw [hcomp]
              rw [CMInstr.run_succ, hrunₙ']
              simp [hstep2] -- no_squeeze: simulation
            · intro s'' h
              rw [CMInstr.run_succ, hrunₙ'] at h
              simp [hstep2] at h -- no_squeeze: simulation
              have hfin : s'' = s' := by
                simpa using h.symm -- no_squeeze: simulation
              rw [hfin]
              exact hlt'

/-- The playfield run reflects the machine run's positions and encodings. -/
theorem simulation_map (prog : CMProgram) (hwellPlaced : wellPlaced prog) (s₀ : CMState)
    (hs₀ : s₀.pc < prog.length) (n : ℕ) :
    ∃ m, (run m (playfieldStart prog s₀)).map (fun s => (s.pc, s.stack))
      = (CMInstr.run prog n s₀).map (fun s => (blockEntry prog s.pc, [encodeState s])) := by
  rcases (sim_run prog hwellPlaced s₀ hs₀ n) with ⟨m, hrun, hb⟩
  refine ⟨m, ?_⟩
  rw [hrun]
  rw [Option.map_map]
  congr 1

/-- If the machine halts, the playfield halts. -/
theorem simulation_halts (prog : CMProgram) (hwellPlaced : wellPlaced prog) (s₀ : CMState)
    (hs₀ : s₀.pc < prog.length) :
    CMInstr.halts prog s₀ → halts (playfieldStart prog s₀) := by
  intro h
  rcases h with ⟨n, hn⟩
  rcases (sim_run prog hwellPlaced s₀ hs₀ n) with ⟨m, hrun, hb⟩
  rw [hn] at hrun
  refine ⟨m, ?_⟩
  simpa using hrun -- no_squeeze: simulation

end Completeness

end LeanFunge
