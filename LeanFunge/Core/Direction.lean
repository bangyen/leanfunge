/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import Mathlib.Data.Nat.Notation

/-!
# Directions

## Main definitions

* `Direction`: The four cardinal directions of the Befunge instruction pointer.
* `Direction.chooseH`: The direction selected by the `_` instruction.
* `Direction.chooseV`: The direction selected by the `|` instruction.
* `stepPos`: The toroidal position update rule.
-/

namespace LeanFunge

/-- The four cardinal directions of the Befunge instruction pointer. -/
inductive Direction where
  | up
  | down
  | left
  | right
  deriving DecidableEq, Repr

namespace Direction

/-- The direction selected by `_`: right when the top of the stack is zero,
    left otherwise. -/
def chooseH (v : Int) : Direction :=
  if v = 0 then .right else .left

/-- The direction selected by `|`: down when the top of the stack is zero,
    up otherwise. -/
def chooseV (v : Int) : Direction :=
  if v = 0 then .down else .up

end Direction

/-- Move a position one cell in direction `d` inside a `w`×`h` playfield,
    wrapping around the edges (the playfield is a torus). -/
def stepPos (w h : ℕ) (d : Direction) (pos : ℕ × ℕ) : ℕ × ℕ :=
  match d with
  | .up => (pos.1 % w, (pos.2 + h - 1) % h)
  | .down => (pos.1 % w, (pos.2 + 1) % h)
  | .left => ((pos.1 + w - 1) % w, pos.2 % h)
  | .right => ((pos.1 + 1) % w, pos.2 % h)

end LeanFunge
