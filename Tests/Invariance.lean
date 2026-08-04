/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanFunge.Theory.Invariance

/-!
# Invariance Tests
-/

namespace LeanFunge.Tests

open LeanFunge

example {w h : ℕ} (s : State w h) (hm : s.stringMode = false)
    (hcell : s.grid.get s.pc.1 s.pc.2 = ' ') :
    step s = some { s with pc := stepPos w h s.dir s.pc } :=
  step_nop s hm hcell

example {w h : ℕ} (s : State w h) (instr : Instruction) (hne : instr ≠ .put) :
    (stepState s instr).grid = s.grid :=
  stepState_grid_of_ne_put s instr hne

example {w h : ℕ} (s : State w h) (y x v : Int) (rest : Stack)
    (hstack : s.stack = y :: x :: v :: rest) :
    Grid.get (stepState s .put).grid (Int.toNat x) (Int.toNat y) = Char.ofNat (Int.toNat v) :=
  step_put_grid s y x v rest hstack

end LeanFunge.Tests
