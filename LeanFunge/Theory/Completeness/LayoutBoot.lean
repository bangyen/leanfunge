/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanFunge.Theory.Completeness.LayoutSimulation

/-!
# The Boot Prelude

`State.init` starts the interpreter at the origin, facing right, with an empty
stack; `playfieldStart` starts it at a block entry, facing down, carrying the
encoded machine state. The undecidability reduction has to begin from the
former (see `UNDECIDABILITY.md`), so the compiled playfield carries a prelude
that bridges the two.

The prelude is two cells on row 0: a `1` in column 0 — the boot column, which
`entryColumn` is re-based to leave free — and a `v` at block 0's entry column.
Running them pushes `1 = encodeState (startCM 0 0)` and turns the pointer down
into the shared descent that every corridor into block 0 already uses.

These lemmas need `wellPlaced` rather than `wellFormed`. A block's exit `v`
deliberately sits in its *successor's* entry column, so the strict column bound
holds only when the last instruction is a `halt` — which is exactly what
`wellPlaced` adds, and what `wellPlaced_normalize` supplies downstream.

## Theorems

* `blockCellList_col_lt`: Every block cell sits inside the playfield width.
* `playfield_boot_push`: Column zero of row zero holds the boot push.
* `boot_run`: The prelude carries `State.init` to `playfieldStart`.
* `boot_halts_iff`: The compiled playfield halts exactly when the machine does.
* `step_push_one`: Pushing the digit one.
-/

namespace LeanFunge

namespace Completeness

open Grid

/-- Every block cell of a well-placed program sits inside the playfield width.
    The exit `v` of an `inc` or `decz` block sits at its successor's entry
    column, so the bound is strict only because a well-placed program ends in a
    `halt` and those blocks are therefore never last. -/
theorem blockCellList_col_lt (prog : CMProgram) (j : ℕ) (c : (ℕ × ℕ) × Char)
    (hj : j < prog.length) (hwp : wellPlaced prog) (hc : c ∈ blockCellList prog j) :
    c.1.1 < playfieldWidth prog := by
  obtain ⟨hwell, hlast⟩ := hwp
  have hnext : entryColumn prog j + blockWidth (prog.getD j .halt)
      ≤ playfieldWidth prog := by
    rw [← entryColumn_succ]
    unfold playfieldWidth
    rcases Nat.lt_or_ge (j + 1) prog.length with hlt | hge
    · exact le_of_lt (entryColumn_strict_mono prog hlt)
    · have heq : j + 1 = prog.length := by omega
      rw [heq]
  have hep := entryColumn_pos prog j
  -- a non-halt block is never last, so its exit column is strictly inside
  have hstrict : prog.getD j .halt ≠ .halt →
      entryColumn prog j + blockWidth (prog.getD j .halt) < playfieldWidth prog := by
    intro hne
    have hj1 : j + 1 < prog.length := by
      rcases hlast j hj with h | h
      · exact absurd h hne
      · exact h
    rw [← entryColumn_succ]
    unfold playfieldWidth
    exact entryColumn_strict_mono prog hj1
  unfold blockCellList at hc
  cases hget : prog.getD j .halt with
  | inc cc =>
      have hs : entryColumn prog j + 3 < playfieldWidth prog := by
        have hst := hstrict (by rw [hget]; exact fun h => CMInstr.noConfusion h)
        rw [hget] at hst
        simpa only [blockWidth] using hst
      simp only [blockCellList, hget, blockWidth, List.mem_cons, List.not_mem_nil,
        or_false] at hc
      rcases hc with h | h | h | h <;> subst h <;> simp only [] <;> omega
  | halt =>
      rw [hget] at hnext
      simp only [blockWidth] at hnext
      simp only [blockCellList, hget, blockWidth, List.mem_cons, List.not_mem_nil,
        or_false] at hc
      rcases hc with h | h <;> subst h <;> simp only [] <;> omega
  | jump k =>
      have hk : k < prog.length := hwell j hj 0 k (Or.inr hget)
      have hek : entryColumn prog k < playfieldWidth prog := by
        unfold playfieldWidth; exact entryColumn_strict_mono prog hk
      rw [hget] at hnext
      simp only [blockWidth] at hnext
      simp only [blockCellList, hget, corridorCells, blockWidth, List.cons_append,
        List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with h | h | h | h <;> subst h <;> simp only [] <;> omega
  | decz cc k =>
      have hk : k < prog.length := hwell j hj cc k (Or.inl hget)
      have hek : entryColumn prog k < playfieldWidth prog := by
        unfold playfieldWidth; exact entryColumn_strict_mono prog hk
      have hs : entryColumn prog j + 5 < playfieldWidth prog := by
        have hst := hstrict (by rw [hget]; exact fun h => CMInstr.noConfusion h)
        rw [hget] at hst
        simpa only [blockWidth] using hst
      simp only [blockCellList, hget, corridorCells, blockWidth, List.cons_append,
        List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with h|h|h|h|h|h|h|h|h|h|h <;> subst h <;> simp only [] <;> omega

/-- Column zero of row zero holds the boot push. No block cell lands in column
    zero, so the prelude cell survives every later fold. -/
theorem playfield_boot_push (prog : CMProgram) (hne : prog ≠ [])
    (hwp : wellPlaced prog) :
    (playfieldOf prog).get 0 0 = '1' := by
  have hlen : 0 < prog.length := List.length_pos_of_ne_nil hne
  have he0 : entryColumn prog 0 = 1 := rfl
  have hw2 : 2 ≤ playfieldWidth prog := by
    have := entryColumn_strict_mono prog hlen
    unfold playfieldWidth
    omega
  rw [playfieldOf_get_eq_lastCellAt]
  unfold playfieldCells
  rw [lastCellAt_append]
  rw [lastCellAt_skip_col_mod _ _ _ _ 0
    (fun c hc => by
      rcases List.mem_flatMap.1 hc with ⟨j, hj, hcj⟩
      have hlt := blockCellList_col_lt prog j c (List.mem_range.1 hj) hwp hcj
      rw [Nat.zero_mod, Nat.mod_eq_of_lt hlt]
      exact blockCell_ne_zero prog j c hcj)]
  unfold bootCells lastCellAt
  simp only [List.foldl_cons, List.foldl_nil, he0, Nat.zero_mod]
  rw [if_neg (by
    rintro ⟨h1, -⟩
    rw [Nat.mod_eq_of_lt (by omega : 1 < playfieldWidth prog)] at h1
    omega)]
  simp only [and_self, ↓reduceIte, ↓Char.isValue]

/-- Pushing the digit one. -/
theorem step_push_one {gw gh : ℕ} (s : State gw gh)
    (hm : s.stringMode = false)
    (hcell : s.grid.get s.pc.1 s.pc.2 = '1') :
    step s = some { s with
      stack := Stack.push s.stack 1,
      pc := stepPos gw gh s.dir s.pc } := by
  unfold step
  simp only [decodeChar, stepState, Stack.push, hm, hcell]

/-- The boot prelude carries `State.init` to `playfieldStart` for the all-zero
    machine state. The run is: push `1` at the boot cell and move right; turn
    down at block zero's entry column; then descend the header rows, every one
    of which is a space or another edge's drop. -/
theorem boot_run (prog : CMProgram) (hne : prog ≠ []) (hwp : wellPlaced prog) :
    run (prog.length + 1) (State.init (playfieldOf prog))
      = some (playfieldStart prog (CMInstr.startCM 0 0)) := by
  have hwell := hwp.1
  have hlen : 0 < prog.length := List.length_pos_of_ne_nil hne
  have he0 : entryColumn prog 0 = 1 := rfl
  have hw : 1 < playfieldWidth prog := by
    have := entryColumn_strict_mono prog hlen
    unfold playfieldWidth; omega
  have hbr0 : blockRow prog 0 = prog.length := rfl
  have hh : prog.length < playfieldHeight prog := by
    have := blockRow_strict_mono prog hlen
    unfold playfieldHeight; omega
  -- step one: the push at the boot cell, moving right
  have hpush : step (State.init (playfieldOf prog))
      = some { State.init (playfieldOf prog) with
          stack := [1], pc := (1, 0) } := by
    rw [step_push_one _ rfl (playfield_boot_push prog hne hwp)]
    congr 1
    have hhpos : 0 < playfieldHeight prog := by omega
    simp only [State.init, stepPos, Stack.push,
      Nat.mod_eq_of_lt hw, Nat.mod_eq_of_lt hhpos]
  -- step two: the turn down at block zero's entry column
  have hhpos : 0 < playfieldHeight prog := by omega
  have hturn : step { State.init (playfieldOf prog) with
        stack := [1], pc := (1, 0) }
      = some { State.init (playfieldOf prog) with
          stack := [1], pc := (1, 1), dir := .down } := by
    rw [step_dir_down _ rfl (by
      have := playfield_boot_turn prog hne
      rwa [he0] at this)]
    congr 1
    simp only [stepPos, Nat.mod_eq_of_lt hw,
      Nat.mod_eq_of_lt (by omega : (1:ℕ) < playfieldHeight prog)]
  -- the remaining steps descend the header rows to block zero's entry
  have hdesc : run (prog.length - 1)
      { State.init (playfieldOf prog) with
        stack := [1], pc := (1, 1), dir := .down }
      = some { State.init (playfieldOf prog) with
          stack := [1], pc := (1, prog.length), dir := .down } := by
    have hrun := run_down
      (s := { State.init (playfieldOf prog) with
              stack := [1], pc := (1, 1), dir := .down })
      (n := prog.length - 1) (x := 1) (y := 1) rfl
      (by simp only [Nat.mod_eq_of_lt hw,
            Nat.mod_eq_of_lt (by omega : (1:ℕ) < playfieldHeight prog)])
      rfl
      (by
        intro k hk
        have hpos : runPos (playfieldWidth prog) (playfieldHeight prog) k .down
            (1 % playfieldWidth prog, 1 % playfieldHeight prog) = (1, 1 + k) := by
          have hstep := runPos_down_pos (playfieldWidth prog) (playfieldHeight prog) 1 1 k hw
            (by omega : 1 + k < playfieldHeight prog)
          simpa only [Nat.mod_eq_of_lt hw,
            Nat.mod_eq_of_lt (by omega : (1:ℕ) < playfieldHeight prog)] using hstep
        rw [hpos]
        have hlt : 1 + k < blockRow prog 0 := by rw [hbr0]; omega
        simpa only [he0] using
          corridorDown_cell prog 0 hlen hwell (1 + k) hlt)
    rw [hrun]
    congr 1
    have hpos : runPos (playfieldWidth prog) (playfieldHeight prog) (prog.length - 1) .down
        (1 % playfieldWidth prog, 1 % playfieldHeight prog) = (1, prog.length) := by
      have hstep := runPos_down_pos (playfieldWidth prog) (playfieldHeight prog) 1 1
        (prog.length - 1) hw (by omega)
      have hfix : (1 : ℕ) + (prog.length - 1) = prog.length := by omega
      rw [hfix] at hstep
      simpa only [Nat.mod_eq_of_lt hw,
        Nat.mod_eq_of_lt (by omega : (1:ℕ) < playfieldHeight prog)] using hstep
    rw [hpos]
  -- assemble: push, turn, then the descent
  have hstep2 : run 2 (State.init (playfieldOf prog))
      = some { State.init (playfieldOf prog) with
          stack := [1], pc := (1, 1), dir := .down } := by
    have h1 : run 1 (State.init (playfieldOf prog))
        = some { State.init (playfieldOf prog) with stack := [1], pc := (1, 0) } := by
      rw [run, run, Option.bind]
      exact hpush
    have h2 : run 1 { State.init (playfieldOf prog) with stack := [1], pc := (1, 0) }
        = some { State.init (playfieldOf prog) with
            stack := [1], pc := (1, 1), dir := .down } := by
      rw [run, run, Option.bind]
      exact hturn
    exact run_append _ _ _ 1 1 h1 h2
  have htotal := run_append _ _ _ 2 (prog.length - 1) hstep2 hdesc
  rw [show prog.length + 1 = 2 + (prog.length - 1) by omega]
  rw [htotal]
  unfold playfieldStart blockEntry
  have henc : encodeState { pc := 0, c1 := 0, c2 := 0 } = 1 := by
    simp only [encodeState, encode, pow_zero, mul_one,
      Int.ofNat_eq_natCast, Nat.cast_one]
  simp only [CMInstr.startCM, hbr0, henc, he0]

/-- The compiled playfield, started the ordinary way, halts exactly when the
    machine does. -/
theorem boot_halts_iff (prog : CMProgram) (hne : prog ≠ []) (hwp : wellPlaced prog) :
    halts (State.init (playfieldOf prog))
      ↔ CMInstr.halts prog (CMInstr.startCM 0 0) := by
  rw [halts_iff_of_run _ _ _ (boot_run prog hne hwp)]
  exact simulation_halts_iff prog hwp (CMInstr.startCM 0 0)
    (by
      have := List.length_pos_of_ne_nil hne
      simpa only [CMInstr.startCM, gt_iff_lt] using this)

end Completeness

end LeanFunge
