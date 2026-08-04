/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanFunge.Core.Direction
import LeanFunge.Core.Grid
import LeanFunge.Core.Instruction
import LeanFunge.Core.Stack
import Mathlib.Data.Nat.Notation

/-!
# The Interpreter State

## Main definitions

* `State`: The complete state of a running Befunge program.
* `State.init`: The initial state.
-/

namespace LeanFunge

/-- The state of a running Befunge program on a `w`×`h` playfield. -/
structure State (w h : ℕ) where
  /-- The playfield. -/
  grid : Grid w h
  /-- The data stack. -/
  stack : Stack
  /-- The instruction pointer `(x, y)`. -/
  pc : ℕ × ℕ
  /-- The current direction of travel. -/
  dir : Direction
  /-- Whether string mode is active. -/
  stringMode : Bool
  /-- The characters printed so far. -/
  output : String
  /-- The remaining character input stream. -/
  input : List Char

namespace State

/-- The initial state: pointer at the origin moving right. -/
def init (grid : Grid w h) : State w h :=
  { grid, stack := [], pc := (0, 0), dir := .right, stringMode := false,
    output := "", input := [] }

end State

end LeanFunge
