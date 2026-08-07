/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanFunge.Theory.Completeness.LayoutCells
import LeanFunge.Theory.Completeness.Routing
import LeanFunge.Theory.Run.Relational
import LeanFunge.Theory.Step
import Mathlib.Tactic
/-!
# The Block Executions on the Generated Playfield

An `inc` block of the generated playfield executes its instruction: the body cells read back exactly the block's snippet, and the instruction pointer steps through them. Running from a block's entry multiplies the stack top by the counter digit and exits down the fall-through column, for arbitrary programs.

The `decz` test cells `> : digit %` of a block on the generated playfield leave the encoded pair on the stack with the remainder on top at the branch cell, for arbitrary programs.

A `jump` block of the generated playfield sends the pointer up its corridor column, and a `halt` block stops the machine, for arbitrary programs.

The `|` branch cell of a `decz` block sends the pointer down through the decrement cells `digit / > v` on an even encoding (counter positive), dividing the value and exiting down the fall-through column, or up the corridor column on an odd encoding (counter zero), with the value unchanged.

## Definitions

* `counterVal`: The integer that an `inc`/`decz` block pushes or tests with.

## Theorems

* `stepPos_right`: Moving right one cell does not wrap when the cell is inside the playfield.

* `stepPos_down`: Moving down one cell does not wrap when the cell is inside the playfield.

* `incBlock_run`: An `inc` block multiplies the stack top by its counter digit and exits down.

* `deczBlock_prefix`: The `> : digit %` cells leave `[n % digit, n]` at the branch cell.

* `stepPos_up`: Moving up one cell does not wrap when the cell is inside the playfield.

* `jumpBlock_run`: A `jump` block sends the pointer up its corridor column.

* `haltBlock_run`: A `halt` block stops the machine.

* `deczBlock_decrement`: On an even encoding the block divides the value and exits down the fall-through column.

* `deczBlock_jump`: On an odd encoding the block sends the pointer up the corridor column with the value unchanged.

-/
namespace LeanFunge

namespace Completeness

/-- The integer that an `inc`/`decz` block pushes or tests with: `2` for
    counter 1, `3` for counter 2. -/
def counterVal (c : Fin 2) : Int := if c = 0 then 2 else 3

/-- Moving right one cell does not wrap when the cell is inside the playfield. -/
theorem stepPos_right (w h : ℕ) (p y : ℕ) (hp : p + 1 < w) (hy : y < h) :
    stepPos w h Direction.right (p, y) = (p + 1, y) := by
  unfold stepPos
  rw [Nat.mod_eq_of_lt hp]
  rw [Nat.mod_eq_of_lt hy]

/-- Moving down one cell does not wrap when the cell is inside the playfield. -/
theorem stepPos_down (w h : ℕ) (p y : ℕ) (hp : p < w) (hy : y + 1 < h) :
    stepPos w h Direction.down (p, y) = (p, y + 1) := by
  unfold stepPos
  rw [Nat.mod_eq_of_lt hp]
  rw [Nat.mod_eq_of_lt hy]

/-- An `inc` block multiplies the stack top by its counter digit and exits
    down its fall-through column. -/
theorem incBlock_run (prog : CMProgram) (i : ℕ) (hi1 : i + 1 < prog.length)
    (hinc : prog.getD i .halt = .inc c)
    (s : State (playfieldWidth prog) (playfieldHeight prog))
    (hsm : s.stringMode = false) (hpc : s.pc = (entryColumn prog i, blockRow prog i))
    (hstack : s.stack = [n]) (hgrid : s.grid = playfieldOf prog) :
    run 4 s = some { s with
      stack := [n * counterVal c],
      pc := (entryColumn prog (i + 1), blockRow prog i + 1),
      dir := .down } := by
  have hW : entryColumn prog i + blockWidth (prog.getD i .halt) < playfieldWidth prog := by
    rw [playfieldWidth]
    rw [← entryColumn_succ]
    exact entryColumn_strict_mono prog hi1
  have hH : blockRow prog i + blockHeight (prog.getD i .halt) < playfieldHeight prog := by
    rw [playfieldHeight]
    rw [← blockRow_succ]
    exact blockRow_strict_mono prog hi1
  rw [hinc] at hW
  rw [hinc] at hH
  simp only [blockWidth] at hW
  simp only [blockHeight] at hH
  have hc0 : s.grid.get (entryColumn prog i) (blockRow prog i) = '>' := by
    rw [hgrid]
    have hpb := playfield_block_get prog i hi1 0 0 (by exact Nat.zero_le _) (by exact blockHeight_pos _)
    rw [hinc] at hpb
    simpa only [blockBodyAt] using hpb
  have hc1 : s.grid.get (entryColumn prog i + 1) (blockRow prog i) = counterDigit c := by
    rw [hgrid]
    have hpb := playfield_block_get prog i hi1 1 0 (by rw [hinc]; norm_num [blockWidth]) (by exact blockHeight_pos _)
    rw [hinc] at hpb
    simpa only [blockBodyAt] using hpb
  have hc2 : s.grid.get (entryColumn prog i + 2) (blockRow prog i) = '*' := by
    rw [hgrid]
    have hpb := playfield_block_get prog i hi1 2 0 (by rw [hinc]; norm_num [blockWidth]) (by exact blockHeight_pos _)
    rw [hinc] at hpb
    simpa only [blockBodyAt] using hpb
  have hc3 : s.grid.get (entryColumn prog i + 3) (blockRow prog i) = 'v' := by
    rw [hgrid]
    have hpb := playfield_block_get prog i hi1 3 0 (by rw [hinc]; norm_num [blockWidth]) (by exact blockHeight_pos _)
    rw [hinc] at hpb
    simpa only [blockBodyAt] using hpb
  have h1 : run 1 s = some { s with dir := .right, pc := (entryColumn prog i + 1, blockRow prog i) } := by
    rw [show run 1 s = step s by rfl]
    unfold step
    have hdec : decodeChar '>' = .right := by unfold decodeChar; rfl
    simp only [hsm, hpc, hc0, hdec, stepState]
    rw [stepPos_right (playfieldWidth prog) (playfieldHeight prog) (entryColumn prog i) (blockRow prog i) (by omega) (by omega)]
  have h2 : run 1 { s with dir := .right, pc := (entryColumn prog i + 1, blockRow prog i) } =
      some { s with dir := .right, stack := [counterVal c, n], pc := (entryColumn prog i + 2, blockRow prog i) } := by
    rw [show run 1 { s with dir := .right, pc := (entryColumn prog i + 1, blockRow prog i) } = step { s with dir := .right, pc := (entryColumn prog i + 1, blockRow prog i) } by rfl]
    unfold step
    have hdec : decodeChar (counterDigit c) = .push (counterVal c) := by
      fin_cases c <;> rfl
    simp only [hsm, hc1, hdec, stepState]
    rw [stepPos_right (playfieldWidth prog) (playfieldHeight prog) (entryColumn prog i + 1) (blockRow prog i) (by omega) (by omega)]
    simp only [hstack, Stack.push]
  have h3 : run 1 { s with dir := .right, stack := [counterVal c, n], pc := (entryColumn prog i + 2, blockRow prog i) } =
      some { s with dir := .right, stack := [n * counterVal c], pc := (entryColumn prog i + 3, blockRow prog i) } := by
    rw [show run 1 { s with dir := .right, stack := [counterVal c, n], pc := (entryColumn prog i + 2, blockRow prog i) } = step { s with dir := .right, stack := [counterVal c, n], pc := (entryColumn prog i + 2, blockRow prog i) } by rfl]
    unfold step
    have hdec : decodeChar '*' = .mul := by unfold decodeChar; rfl
    simp only [hsm, hc2, hdec, stepState, Stack.applyBinary]
    rw [stepPos_right (playfieldWidth prog) (playfieldHeight prog) (entryColumn prog i + 2) (blockRow prog i) (by omega) (by omega)]
  have h4 : run 1 { s with dir := .right, stack := [n * counterVal c], pc := (entryColumn prog i + 3, blockRow prog i) } =
      some { s with stack := [n * counterVal c], pc := (entryColumn prog i + 3, blockRow prog i + 1), dir := .down } := by
    rw [show run 1 { s with dir := .right, stack := [n * counterVal c], pc := (entryColumn prog i + 3, blockRow prog i) } = step { s with dir := .right, stack := [n * counterVal c], pc := (entryColumn prog i + 3, blockRow prog i) } by rfl]
    unfold step
    have hdec : decodeChar 'v' = .down := by unfold decodeChar; rfl
    simp only [hsm, hc3, hdec, stepState]
    rw [stepPos_down (playfieldWidth prog) (playfieldHeight prog) (entryColumn prog i + 3) (blockRow prog i) (by omega) (by omega)]
  have h12 : run (1 + 1) s = some { s with dir := .right, stack := [counterVal c, n], pc := (entryColumn prog i + 2, blockRow prog i) } := by
    exact run_append s { s with dir := .right, pc := (entryColumn prog i + 1, blockRow prog i) }
      (some { s with dir := .right, stack := [counterVal c, n], pc := (entryColumn prog i + 2, blockRow prog i) }) 1 1 h1 h2
  have h123 : run (1 + 1 + 1) s = some { s with dir := .right, stack := [n * counterVal c], pc := (entryColumn prog i + 3, blockRow prog i) } := by
    exact run_append s { s with dir := .right, stack := [counterVal c, n], pc := (entryColumn prog i + 2, blockRow prog i) }
      (some { s with dir := .right, stack := [n * counterVal c], pc := (entryColumn prog i + 3, blockRow prog i) }) (1 + 1) 1 h12 h3
  have h1234 : run (1 + 1 + 1 + 1) s =
      some { s with stack := [n * counterVal c], pc := (entryColumn prog i + 3, blockRow prog i + 1), dir := .down } := by
    exact run_append s { s with dir := .right, stack := [n * counterVal c], pc := (entryColumn prog i + 3, blockRow prog i) }
      (some { s with stack := [n * counterVal c], pc := (entryColumn prog i + 3, blockRow prog i + 1), dir := .down }) (1 + 1 + 1) 1 h123 h4
  rw [show 4 = 1 + 1 + 1 + 1 by omega]
  rw [h1234]
  ext <;> try rfl
  rw [entryColumn_succ]
  rw [hinc]
  simp only [blockWidth]

/-- The `decz` test cells leave the remainder on top of the encoded pair at
    the branch cell. -/
theorem deczBlock_prefix (prog : CMProgram) (i : ℕ) (hi1 : i + 1 < prog.length)
    (hdecz : prog.getD i .halt = .decz c k)
    (s : State (playfieldWidth prog) (playfieldHeight prog))
    (hsm : s.stringMode = false) (hpc : s.pc = (entryColumn prog i, blockRow prog i))
    (hstack : s.stack = [n]) (hgrid : s.grid = playfieldOf prog) :
    run 4 s = some { s with
      dir := .right,
      stack := [n % counterVal c, n],
      pc := (entryColumn prog i + 4, blockRow prog i) } := by
  have hW : entryColumn prog i + blockWidth (prog.getD i .halt) < playfieldWidth prog := by
    rw [playfieldWidth]
    rw [← entryColumn_succ]
    exact entryColumn_strict_mono prog hi1
  have hH : blockRow prog i + blockHeight (prog.getD i .halt) < playfieldHeight prog := by
    rw [playfieldHeight]
    rw [← blockRow_succ]
    exact blockRow_strict_mono prog hi1
  rw [hdecz] at hW
  rw [hdecz] at hH
  simp only [blockWidth] at hW
  simp only [blockHeight] at hH
  have hc0 : s.grid.get (entryColumn prog i) (blockRow prog i) = '>' := by
    rw [hgrid]
    have hpb := playfield_block_get prog i hi1 0 0 (by exact Nat.zero_le _) (by exact blockHeight_pos _)
    rw [hdecz] at hpb
    simpa only [blockBodyAt] using hpb
  have hc1 : s.grid.get (entryColumn prog i + 1) (blockRow prog i) = ':' := by
    rw [hgrid]
    have hpb := playfield_block_get prog i hi1 1 0 (by rw [hdecz]; norm_num [blockWidth]) (by exact blockHeight_pos _)
    rw [hdecz] at hpb
    simpa only [blockBodyAt] using hpb
  have hc2 : s.grid.get (entryColumn prog i + 2) (blockRow prog i) = counterDigit c := by
    rw [hgrid]
    have hpb := playfield_block_get prog i hi1 2 0 (by rw [hdecz]; norm_num [blockWidth]) (by exact blockHeight_pos _)
    rw [hdecz] at hpb
    simpa only [blockBodyAt] using hpb
  have hc3 : s.grid.get (entryColumn prog i + 3) (blockRow prog i) = '%' := by
    rw [hgrid]
    have hpb := playfield_block_get prog i hi1 3 0 (by rw [hdecz]; norm_num [blockWidth]) (by exact blockHeight_pos _)
    rw [hdecz] at hpb
    simpa only [blockBodyAt] using hpb
  have h1 : run 1 s = some { s with dir := .right, pc := (entryColumn prog i + 1, blockRow prog i) } := by
    rw [show run 1 s = step s by rfl]
    unfold step
    have hdec : decodeChar '>' = .right := by unfold decodeChar; rfl
    simp only [hsm, hpc, hc0, hdec, stepState]
    rw [stepPos_right (playfieldWidth prog) (playfieldHeight prog) (entryColumn prog i) (blockRow prog i) (by omega) (by omega)]
  have h2 : run 1 { s with dir := .right, pc := (entryColumn prog i + 1, blockRow prog i) } =
      some { s with dir := .right, stack := [n, n], pc := (entryColumn prog i + 2, blockRow prog i) } := by
    rw [show run 1 { s with dir := .right, pc := (entryColumn prog i + 1, blockRow prog i) } = step { s with dir := .right, pc := (entryColumn prog i + 1, blockRow prog i) } by rfl]
    unfold step
    have hdec : decodeChar ':' = .dup := by unfold decodeChar; rfl
    simp only [hsm, hc1, hdec, stepState, Stack.dup]
    rw [stepPos_right (playfieldWidth prog) (playfieldHeight prog) (entryColumn prog i + 1) (blockRow prog i) (by omega) (by omega)]
    simp only [hstack, Stack.dup]
  have h3 : run 1 { s with dir := .right, stack := [n, n], pc := (entryColumn prog i + 2, blockRow prog i) } =
      some { s with dir := .right, stack := [counterVal c, n, n], pc := (entryColumn prog i + 3, blockRow prog i) } := by
    rw [show run 1 { s with dir := .right, stack := [n, n], pc := (entryColumn prog i + 2, blockRow prog i) } = step { s with dir := .right, stack := [n, n], pc := (entryColumn prog i + 2, blockRow prog i) } by rfl]
    unfold step
    have hdec : decodeChar (counterDigit c) = .push (counterVal c) := by
      fin_cases c <;> rfl
    simp only [hsm, hc2, hdec, stepState, Stack.push]
    rw [stepPos_right (playfieldWidth prog) (playfieldHeight prog) (entryColumn prog i + 2) (blockRow prog i) (by omega) (by omega)]
  have h4 : run 1 { s with dir := .right, stack := [counterVal c, n, n], pc := (entryColumn prog i + 3, blockRow prog i) } =
      some { s with dir := .right, stack := [n % counterVal c, n], pc := (entryColumn prog i + 4, blockRow prog i) } := by
    rw [show run 1 { s with dir := .right, stack := [counterVal c, n, n], pc := (entryColumn prog i + 3, blockRow prog i) } = step { s with dir := .right, stack := [counterVal c, n, n], pc := (entryColumn prog i + 3, blockRow prog i) } by rfl]
    unfold step
    have hdec : decodeChar '%' = .mod := by unfold decodeChar; rfl
    simp only [hsm, hc3, hdec, stepState, Stack.applyBinary]
    rw [stepPos_right (playfieldWidth prog) (playfieldHeight prog) (entryColumn prog i + 3) (blockRow prog i) (by omega) (by omega)]
  have h12 : run (1 + 1) s = some { s with dir := .right, stack := [n, n], pc := (entryColumn prog i + 2, blockRow prog i) } := by
    exact run_append s { s with dir := .right, pc := (entryColumn prog i + 1, blockRow prog i) }
      (some { s with dir := .right, stack := [n, n], pc := (entryColumn prog i + 2, blockRow prog i) }) 1 1 h1 h2
  have h123 : run (1 + 1 + 1) s = some { s with dir := .right, stack := [counterVal c, n, n], pc := (entryColumn prog i + 3, blockRow prog i) } := by
    exact run_append s { s with dir := .right, stack := [n, n], pc := (entryColumn prog i + 2, blockRow prog i) }
      (some { s with dir := .right, stack := [counterVal c, n, n], pc := (entryColumn prog i + 3, blockRow prog i) }) (1 + 1) 1 h12 h3
  have h1234 : run (1 + 1 + 1 + 1) s =
      some { s with dir := .right, stack := [n % counterVal c, n], pc := (entryColumn prog i + 4, blockRow prog i) } := by
    exact run_append s { s with dir := .right, stack := [counterVal c, n, n], pc := (entryColumn prog i + 3, blockRow prog i) }
      (some { s with dir := .right, stack := [n % counterVal c, n], pc := (entryColumn prog i + 4, blockRow prog i) }) (1 + 1 + 1) 1 h123 h4
  rw [show 4 = 1 + 1 + 1 + 1 by omega]
  rw [h1234]

theorem stepPos_up (w h : ℕ) (p y : ℕ) (hp : p < w) (hy0 : 0 < y) (hy : y < h) :
    stepPos w h Direction.up (p, y) = (p, y - 1) := by
  unfold stepPos
  rw [Nat.mod_eq_of_lt hp]
  have hmod : (y + h - 1) % h = y - 1 := by
    have hsub : y + h - 1 = (y - 1) + h := by omega
    rw [hsub]
    have hyl : y - 1 < h := by omega
    rw [Nat.add_mod_right, Nat.mod_eq_of_lt hyl]
  rw [hmod]

/-- A `jump` block sends the pointer up its corridor column. -/
theorem jumpBlock_run (prog : CMProgram) (i : ℕ) (hi1 : i + 1 < prog.length)
    (hjump : prog.getD i .halt = .jump k)
    (s : State (playfieldWidth prog) (playfieldHeight prog))
    (hsm : s.stringMode = false) (hpc : s.pc = (entryColumn prog i, blockRow prog i))
    (hgrid : s.grid = playfieldOf prog) :
    run 2 s = some { s with pc := (entryColumn prog i + 1, blockRow prog i - 1), dir := .up } := by
  have hW : entryColumn prog i + blockWidth (prog.getD i .halt) < playfieldWidth prog := by
    rw [playfieldWidth]
    rw [← entryColumn_succ]
    exact entryColumn_strict_mono prog hi1
  have hH : blockRow prog i + blockHeight (prog.getD i .halt) < playfieldHeight prog := by
    rw [playfieldHeight]
    rw [← blockRow_succ]
    exact blockRow_strict_mono prog hi1
  rw [hjump] at hW
  rw [hjump] at hH
  simp only [blockWidth] at hW
  simp only [blockHeight] at hH
  have hy0 : 0 < blockRow prog i := by
    have hle : prog.length ≤ blockRow prog i := blockRow_ge_length prog i
    omega
  have hc0 : s.grid.get (entryColumn prog i) (blockRow prog i) = '>' := by
    rw [hgrid]
    have hpb := playfield_block_get prog i hi1 0 0 (by exact Nat.zero_le _) (by exact blockHeight_pos _)
    rw [hjump] at hpb
    simpa only [blockBodyAt] using hpb
  have hc1 : s.grid.get (entryColumn prog i + 1) (blockRow prog i) = '^' := by
    rw [hgrid]
    have hpb := playfield_block_get prog i hi1 1 0 (by rw [hjump]; norm_num [blockWidth]) (by exact blockHeight_pos _)
    rw [hjump] at hpb
    simpa only [blockBodyAt] using hpb
  have h1 : run 1 s = some { s with dir := .right, pc := (entryColumn prog i + 1, blockRow prog i) } := by
    rw [show run 1 s = step s by rfl]
    unfold step
    have hdec : decodeChar '>' = .right := by unfold decodeChar; rfl
    simp only [hsm, hpc, hc0, hdec, stepState]
    rw [stepPos_right (playfieldWidth prog) (playfieldHeight prog) (entryColumn prog i) (blockRow prog i) (by omega) (by omega)]
  have h2 : run 1 { s with dir := .right, pc := (entryColumn prog i + 1, blockRow prog i) } =
      some { s with pc := (entryColumn prog i + 1, blockRow prog i - 1), dir := .up } := by
    rw [show run 1 { s with dir := .right, pc := (entryColumn prog i + 1, blockRow prog i) } = step { s with dir := .right, pc := (entryColumn prog i + 1, blockRow prog i) } by rfl]
    unfold step
    have hdec : decodeChar '^' = .up := by unfold decodeChar; rfl
    simp only [hsm, hc1, hdec, stepState]
    rw [stepPos_up (playfieldWidth prog) (playfieldHeight prog) (entryColumn prog i + 1) (blockRow prog i) (by omega) (by omega) (by omega)]
  have h12 : run (1 + 1) s = some { s with pc := (entryColumn prog i + 1, blockRow prog i - 1), dir := .up } := by
    exact run_append s { s with dir := .right, pc := (entryColumn prog i + 1, blockRow prog i) }
      (some { s with pc := (entryColumn prog i + 1, blockRow prog i - 1), dir := .up }) 1 1 h1 h2
  rw [show 2 = 1 + 1 by omega]
  rw [h12]

/-- A `halt` block stops the machine. -/
theorem haltBlock_run (prog : CMProgram) (i : ℕ) (hi1 : i + 1 < prog.length)
    (hhalt : prog.getD i .halt = .halt)
    (s : State (playfieldWidth prog) (playfieldHeight prog))
    (hsm : s.stringMode = false) (hpc : s.pc = (entryColumn prog i, blockRow prog i))
    (hgrid : s.grid = playfieldOf prog) :
    run 2 s = none := by
  have hW : entryColumn prog i + blockWidth (prog.getD i .halt) < playfieldWidth prog := by
    rw [playfieldWidth]
    rw [← entryColumn_succ]
    exact entryColumn_strict_mono prog hi1
  have hH : blockRow prog i + blockHeight (prog.getD i .halt) < playfieldHeight prog := by
    rw [playfieldHeight]
    rw [← blockRow_succ]
    exact blockRow_strict_mono prog hi1
  rw [hhalt] at hW
  rw [hhalt] at hH
  simp only [blockWidth] at hW
  simp only [blockHeight] at hH
  have hc0 : s.grid.get (entryColumn prog i) (blockRow prog i) = '>' := by
    rw [hgrid]
    have hpb := playfield_block_get prog i hi1 0 0 (by exact Nat.zero_le _) (by exact blockHeight_pos _)
    rw [hhalt] at hpb
    simpa only [blockBodyAt] using hpb
  have hc1 : s.grid.get (entryColumn prog i + 1) (blockRow prog i) = '@' := by
    rw [hgrid]
    have hpb := playfield_block_get prog i hi1 1 0 (by rw [hhalt]; norm_num [blockWidth]) (by exact blockHeight_pos _)
    rw [hhalt] at hpb
    simpa only [blockBodyAt] using hpb
  have h1 : run 1 s = some { s with dir := .right, pc := (entryColumn prog i + 1, blockRow prog i) } := by
    rw [show run 1 s = step s by rfl]
    unfold step
    have hdec : decodeChar '>' = .right := by unfold decodeChar; rfl
    simp only [hsm, hpc, hc0, hdec, stepState]
    rw [stepPos_right (playfieldWidth prog) (playfieldHeight prog) (entryColumn prog i) (blockRow prog i) (by omega) (by omega)]
  have h2 : run 1 { s with dir := .right, pc := (entryColumn prog i + 1, blockRow prog i) } = none := by
    rw [show run 1 { s with dir := .right, pc := (entryColumn prog i + 1, blockRow prog i) } = step { s with dir := .right, pc := (entryColumn prog i + 1, blockRow prog i) } by rfl]
    unfold step
    have hdec : decodeChar '@' = .halt := by unfold decodeChar; rfl
    simp only [hsm, hc1, hdec, stepState]
  have h12 : run (1 + 1) s = none := by
    exact run_append s { s with dir := .right, pc := (entryColumn prog i + 1, blockRow prog i) } none 1 1 h1 h2
  rw [show 2 = 1 + 1 by omega]
  rw [h12]

theorem deczBlock_decrement (prog : CMProgram) (i : ℕ) (hi1 : i + 1 < prog.length)
    (hdecz : prog.getD i .halt = .decz c k)
    (s : State (playfieldWidth prog) (playfieldHeight prog))
    (hsm : s.stringMode = false) (hpc : s.pc = (entryColumn prog i + 4, blockRow prog i))
    (hstack : s.stack = [n % counterVal c, n])
    (hgrid : s.grid = playfieldOf prog) (hz : n % counterVal c = 0) :
    run 5 s = some { s with
      stack := [n / counterVal c],
      pc := (entryColumn prog i + 5, blockRow prog i + 4),
      dir := .down } := by
  have hW : entryColumn prog i + blockWidth (prog.getD i .halt) < playfieldWidth prog := by
    rw [playfieldWidth]
    rw [← entryColumn_succ]
    exact entryColumn_strict_mono prog hi1
  have hH : blockRow prog i + blockHeight (prog.getD i .halt) < playfieldHeight prog := by
    rw [playfieldHeight]
    rw [← blockRow_succ]
    exact blockRow_strict_mono prog hi1
  rw [hdecz] at hW
  rw [hdecz] at hH
  simp only [blockWidth] at hW
  simp only [blockHeight] at hH
  have hy0 : 0 < blockRow prog i := by
    have hle : prog.length ≤ blockRow prog i := blockRow_ge_length prog i
    omega
  have hc0 : s.grid.get (entryColumn prog i + 4) (blockRow prog i) = '|' := by
    rw [hgrid]
    have hpb := playfield_block_get prog i hi1 4 0 (by rw [hdecz]; norm_num [blockWidth]) (by exact blockHeight_pos _)
    rw [hdecz] at hpb
    simpa only [blockBodyAt] using hpb
  have hc1 : s.grid.get (entryColumn prog i + 4) (blockRow prog i + 1) = counterDigit c := by
    rw [hgrid]
    have hpb := playfield_block_get prog i hi1 4 1 (by rw [hdecz]; norm_num [blockWidth]) (by rw [hdecz]; norm_num [blockHeight])
    rw [hdecz] at hpb
    simpa only [blockBodyAt] using hpb
  have hc2 : s.grid.get (entryColumn prog i + 4) (blockRow prog i + 2) = '/' := by
    rw [hgrid]
    have hpb := playfield_block_get prog i hi1 4 2 (by rw [hdecz]; norm_num [blockWidth]) (by rw [hdecz]; norm_num [blockHeight])
    rw [hdecz] at hpb
    simpa only [blockBodyAt] using hpb
  have hc3 : s.grid.get (entryColumn prog i + 4) (blockRow prog i + 3) = '>' := by
    rw [hgrid]
    have hpb := playfield_block_get prog i hi1 4 3 (by rw [hdecz]; norm_num [blockWidth]) (by rw [hdecz]; norm_num [blockHeight])
    rw [hdecz] at hpb
    simpa only [blockBodyAt] using hpb
  have hc4 : s.grid.get (entryColumn prog i + 5) (blockRow prog i + 3) = 'v' := by
    rw [hgrid]
    have hpb := playfield_block_get prog i hi1 5 3 (by rw [hdecz]; norm_num [blockWidth]) (by rw [hdecz]; norm_num [blockHeight])
    rw [hdecz] at hpb
    simpa only [blockBodyAt] using hpb
  have h1 : run 1 s = some { s with stack := [n], pc := (entryColumn prog i + 4, blockRow prog i + 1), dir := .down } := by
    rw [show run 1 s = step s by rfl]
    rw [step_chooseV s hsm (by simpa only [hpc] using hc0) (n % counterVal c) [n] hstack]
    simp only [hpc, hz, if_pos]
    rw [stepPos_down (playfieldWidth prog) (playfieldHeight prog) (entryColumn prog i + 4) (blockRow prog i) (by omega) (by omega)]
  have h2 : run 1 { s with stack := [n], pc := (entryColumn prog i + 4, blockRow prog i + 1), dir := .down } =
      some { s with stack := [counterVal c, n], pc := (entryColumn prog i + 4, blockRow prog i + 2), dir := .down } := by
    rw [show run 1 { s with stack := [n], pc := (entryColumn prog i + 4, blockRow prog i + 1), dir := .down } = step { s with stack := [n], pc := (entryColumn prog i + 4, blockRow prog i + 1), dir := .down } by rfl]
    unfold step
    have hdec : decodeChar (counterDigit c) = .push (counterVal c) := by
      fin_cases c <;> rfl
    simp only [hsm, hc1, hdec, stepState, Stack.push]
    rw [stepPos_down (playfieldWidth prog) (playfieldHeight prog) (entryColumn prog i + 4) (blockRow prog i + 1) (by omega) (by omega)]
  have h3 : run 1 { s with stack := [counterVal c, n], pc := (entryColumn prog i + 4, blockRow prog i + 2), dir := .down } =
      some { s with stack := [n / counterVal c], pc := (entryColumn prog i + 4, blockRow prog i + 3), dir := .down } := by
    rw [show run 1 { s with stack := [counterVal c, n], pc := (entryColumn prog i + 4, blockRow prog i + 2), dir := .down } = step { s with stack := [counterVal c, n], pc := (entryColumn prog i + 4, blockRow prog i + 2), dir := .down } by rfl]
    unfold step
    have hdec : decodeChar '/' = .div := by unfold decodeChar; rfl
    simp only [hsm, hc2, hdec, stepState, Stack.applyBinary]
    rw [stepPos_down (playfieldWidth prog) (playfieldHeight prog) (entryColumn prog i + 4) (blockRow prog i + 2) (by omega) (by omega)]
  have h4 : run 1 { s with stack := [n / counterVal c], pc := (entryColumn prog i + 4, blockRow prog i + 3), dir := .down } =
      some { s with stack := [n / counterVal c], pc := (entryColumn prog i + 5, blockRow prog i + 3), dir := .right } := by
    rw [show run 1 { s with stack := [n / counterVal c], pc := (entryColumn prog i + 4, blockRow prog i + 3), dir := .down } = step { s with stack := [n / counterVal c], pc := (entryColumn prog i + 4, blockRow prog i + 3), dir := .down } by rfl]
    unfold step
    have hdec : decodeChar '>' = .right := by unfold decodeChar; rfl
    simp only [hsm, hc3, hdec, stepState]
    rw [stepPos_right (playfieldWidth prog) (playfieldHeight prog) (entryColumn prog i + 4) (blockRow prog i + 3) (by omega) (by omega)]
  have h5 : run 1 { s with stack := [n / counterVal c], pc := (entryColumn prog i + 5, blockRow prog i + 3), dir := .right } =
      some { s with stack := [n / counterVal c], pc := (entryColumn prog i + 5, blockRow prog i + 4), dir := .down } := by
    rw [show run 1 { s with stack := [n / counterVal c], pc := (entryColumn prog i + 5, blockRow prog i + 3), dir := .right } = step { s with stack := [n / counterVal c], pc := (entryColumn prog i + 5, blockRow prog i + 3), dir := .right } by rfl]
    unfold step
    have hdec : decodeChar 'v' = .down := by unfold decodeChar; rfl
    simp only [hsm, hc4, hdec, stepState]
    rw [stepPos_down (playfieldWidth prog) (playfieldHeight prog) (entryColumn prog i + 5) (blockRow prog i + 3) (by omega) (by omega)]
  have h12 : run (1 + 1) s = some { s with stack := [counterVal c, n], pc := (entryColumn prog i + 4, blockRow prog i + 2), dir := .down } := by
    exact run_append s { s with stack := [n], pc := (entryColumn prog i + 4, blockRow prog i + 1), dir := .down }
      (some { s with stack := [counterVal c, n], pc := (entryColumn prog i + 4, blockRow prog i + 2), dir := .down }) 1 1 h1 h2
  have h123 : run (1 + 1 + 1) s = some { s with stack := [n / counterVal c], pc := (entryColumn prog i + 4, blockRow prog i + 3), dir := .down } := by
    exact run_append s { s with stack := [counterVal c, n], pc := (entryColumn prog i + 4, blockRow prog i + 2), dir := .down }
      (some { s with stack := [n / counterVal c], pc := (entryColumn prog i + 4, blockRow prog i + 3), dir := .down }) (1 + 1) 1 h12 h3
  have h1234 : run (1 + 1 + 1 + 1) s = some { s with stack := [n / counterVal c], pc := (entryColumn prog i + 5, blockRow prog i + 3), dir := .right } := by
    exact run_append s { s with stack := [n / counterVal c], pc := (entryColumn prog i + 4, blockRow prog i + 3), dir := .down }
      (some { s with stack := [n / counterVal c], pc := (entryColumn prog i + 5, blockRow prog i + 3), dir := .right }) (1 + 1 + 1) 1 h123 h4
  have h12345 : run (1 + 1 + 1 + 1 + 1) s =
      some { s with stack := [n / counterVal c], pc := (entryColumn prog i + 5, blockRow prog i + 4), dir := .down } := by
    exact run_append s { s with stack := [n / counterVal c], pc := (entryColumn prog i + 5, blockRow prog i + 3), dir := .right }
      (some { s with stack := [n / counterVal c], pc := (entryColumn prog i + 5, blockRow prog i + 4), dir := .down }) (1 + 1 + 1 + 1) 1 h1234 h5
  rw [show 5 = 1 + 1 + 1 + 1 + 1 by omega]
  rw [h12345]

/-- On an odd encoding the `decz` block sends the pointer up the corridor
    column with the value unchanged. -/
theorem deczBlock_jump (prog : CMProgram) (i : ℕ) (hi1 : i + 1 < prog.length)
    (hdecz : prog.getD i .halt = .decz c k)
    (s : State (playfieldWidth prog) (playfieldHeight prog))
    (hsm : s.stringMode = false) (hpc : s.pc = (entryColumn prog i + 4, blockRow prog i))
    (hstack : s.stack = [n % counterVal c, n])
    (hgrid : s.grid = playfieldOf prog) (hnz : n % counterVal c ≠ 0) :
    run 1 s = some { s with
      stack := [n],
      pc := (entryColumn prog i + 4, blockRow prog i - 1),
      dir := .up } := by
  have hW : entryColumn prog i + blockWidth (prog.getD i .halt) < playfieldWidth prog := by
    rw [playfieldWidth]
    rw [← entryColumn_succ]
    exact entryColumn_strict_mono prog hi1
  have hH : blockRow prog i + blockHeight (prog.getD i .halt) < playfieldHeight prog := by
    rw [playfieldHeight]
    rw [← blockRow_succ]
    exact blockRow_strict_mono prog hi1
  rw [hdecz] at hW
  rw [hdecz] at hH
  simp only [blockWidth] at hW
  simp only [blockHeight] at hH
  have hy0 : 0 < blockRow prog i := by
    have hle : prog.length ≤ blockRow prog i := blockRow_ge_length prog i
    omega
  have hc0 : s.grid.get (entryColumn prog i + 4) (blockRow prog i) = '|' := by
    rw [hgrid]
    have hpb := playfield_block_get prog i hi1 4 0 (by rw [hdecz]; norm_num [blockWidth]) (by exact blockHeight_pos _)
    rw [hdecz] at hpb
    simpa only [blockBodyAt] using hpb
  rw [show run 1 s = step s by rfl]
  rw [step_chooseV s hsm (by simpa only [hpc] using hc0) (n % counterVal c) [n] hstack]
  simp only [hpc, hnz, if_false]
  rw [stepPos_up (playfieldWidth prog) (playfieldHeight prog) (entryColumn prog i + 4) (blockRow prog i) (by omega) (by omega) (by omega)]

end Completeness

end LeanFunge
