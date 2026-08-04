/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanFunge.Core.Semantics
import LeanFunge.Theory.Grid
import Mathlib.Data.Nat.Notation

/-!
# Program-Level Invariance

## Theorems

* `step_nop`: A space (`.nop`) only advances the instruction pointer.
* `stepState_grid_of_ne_put`: Every instruction except `p` leaves the playfield
  unchanged.
* `step_put_grid`: The `p` instruction stores its value at the addressed cell,
  so a subsequent fetch at that cell reads it back.
-/

namespace LeanFunge

/-- A space (`.nop`) only advances the instruction pointer, leaving the stack,
    playfield, and output untouched. -/
theorem step_nop (s : State w h) (hm : s.stringMode = false)
    (hcell : s.grid.get s.pc.1 s.pc.2 = ' ') :
    step s = some { s with pc := stepPos w h s.dir s.pc } := by
  unfold step
  have hd : decodeChar ' ' = Instruction.nop := by decide
  simp only [hd, stepState, hm, hcell]

/-- Every instruction except `p` leaves the playfield unchanged. -/
theorem stepState_grid_of_ne_put (s : State w h) (instr : Instruction) (hne : instr ≠ .put) :
    (stepState s instr).grid = s.grid := by
  cases instr with
  | put => exact (absurd rfl hne)
  | inputChar =>
      unfold stepState
      cases h : s.input <;> rfl
  | _ => rfl

/-- The `p` instruction stores its value at the addressed cell (modulo the
    playfield size), so a subsequent `g` reads it back. -/
theorem step_put_grid (s : State w h) (y x v : Int) (rest : Stack)
    (hstack : s.stack = y :: x :: v :: rest) :
    Grid.get (stepState s .put).grid (Int.toNat x) (Int.toNat y) = Char.ofNat (Int.toNat v) := by
  unfold stepState
  rw [hstack]
  change Grid.get (Grid.put s.grid (Int.toNat x) (Int.toNat y) (Char.ofNat (Int.toNat v)))
      (Int.toNat x) (Int.toNat y) = Char.ofNat (Int.toNat v)
  exact Grid.get_put_self s.grid (Int.toNat x) (Int.toNat y) (Char.ofNat (Int.toNat v))

end LeanFunge
