/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanFunge.Core.Semantics
import LeanFunge.Theory.Step
import Mathlib.Data.Nat.Notation

/-!
# Remaining Step Semantics

Theorems for the instructions not covered in `LeanFunge.Theory.Step`:
the arithmetic `div`/`mod`, the comparison, the stack-manipulation
`dup`/`swap`/`drop`, and the input `~`/`&`. Also includes the
toroidal-wrapping instance of the `#` trampoline.

## Theorems

* `step_div`: `/` pushes the quotient of the top two values.
* `step_mod`: `%` pushes the remainder of the top two values.
* `step_greater`: the comparison instruction pushes `1` when the
  second-popped value exceeds the top, and 0 otherwise.
* `step_dup`: `:` duplicates the top of the stack.
* `step_swap`: `\` swaps the top two elements of the stack.
* `step_drop`: `$` discards the top of the stack.
* `step_inputChar`: `~` pushes the code of the next input character.
* `step_inputChar_eof`: At end of input, `~` pushes `0`.
* `step_inputInt`: `&` parses a decimal integer from the input stream.
* `step_trampoline_right_from_last`: `#` at the last column wraps to column 1.
-/

namespace LeanFunge

/-- `/` pushes the quotient of the top two values. -/
theorem step_div (s : State w h) (hm : s.stringMode = false)
    (hcell : s.grid.get s.pc.1 s.pc.2 = '/') (a b : Int) (rest : Stack)
    (hstack : s.stack = a :: b :: rest) :
    step s = some { s with stack := (b / a) :: rest, pc := stepPos w h s.dir s.pc } := by
  unfold step
  simp only [decodeChar, stepState, Stack.applyBinary, hm, hcell, hstack]

/-- `%` pushes the remainder of the top two values. -/
theorem step_mod (s : State w h) (hm : s.stringMode = false)
    (hcell : s.grid.get s.pc.1 s.pc.2 = '%') (a b : Int) (rest : Stack)
    (hstack : s.stack = a :: b :: rest) :
    step s = some { s with stack := (b % a) :: rest, pc := stepPos w h s.dir s.pc } := by
  unfold step
  simp only [decodeChar, stepState, Stack.applyBinary, hm, hcell, hstack]

/-- The comparison instruction pushes `1` when the second-popped value exceeds
    the top, and `0` otherwise. -/
theorem step_greater (s : State w h) (hm : s.stringMode = false)
    (hcell : s.grid.get s.pc.1 s.pc.2 = '`') (a b : Int) (rest : Stack)
    (hstack : s.stack = a :: b :: rest) :
    step s = some { s with
      stack := (if b > a then 1 else 0) :: rest,
      pc := stepPos w h s.dir s.pc } := by
  unfold step
  simp only [decodeChar, stepState, Stack.push, Stack.top, Stack.pop, Stack.drop, hm, hcell, hstack]

/-- `:` duplicates the top of the stack. -/
theorem step_dup (s : State w h) (hm : s.stringMode = false)
    (hcell : s.grid.get s.pc.1 s.pc.2 = ':') (v : Int) (rest : Stack)
    (hstack : s.stack = v :: rest) :
    step s = some { s with stack := v :: v :: rest, pc := stepPos w h s.dir s.pc } := by
  unfold step
  simp only [decodeChar, stepState, Stack.dup, hm, hcell, hstack]

/-- `\` swaps the top two elements of the stack. -/
theorem step_swap (s : State w h) (hm : s.stringMode = false)
    (hcell : s.grid.get s.pc.1 s.pc.2 = '\\') (a b : Int) (rest : Stack)
    (hstack : s.stack = a :: b :: rest) :
    step s = some { s with stack := b :: a :: rest, pc := stepPos w h s.dir s.pc } := by
  unfold step
  simp only [decodeChar, stepState, Stack.swap, hm, hcell, hstack]

/-- `$` discards the top of the stack. -/
theorem step_drop (s : State w h) (hm : s.stringMode = false)
    (hcell : s.grid.get s.pc.1 s.pc.2 = '$') (v : Int) (rest : Stack)
    (hstack : s.stack = v :: rest) :
    step s = some { s with stack := rest, pc := stepPos w h s.dir s.pc } := by
  unfold step
  simp only [decodeChar, stepState, Stack.drop, hm, hcell, hstack]

/-- `~` pushes the code of the next input character. -/
theorem step_inputChar (s : State w h) (hm : s.stringMode = false)
    (hcell : s.grid.get s.pc.1 s.pc.2 = '~') (c : Char) (rest : List Char)
    (hinput : s.input = c :: rest) :
    step s = some { s with
      stack := Stack.push s.stack (Int.ofNat c.toNat),
      input := rest,
      pc := stepPos w h s.dir s.pc } := by
  unfold step
  simp only [decodeChar, stepState, hm, hcell, hinput]

/-- At end of input, `~` pushes `0`. -/
theorem step_inputChar_eof (s : State w h) (hm : s.stringMode = false)
    (hcell : s.grid.get s.pc.1 s.pc.2 = '~') (hinput : s.input = []) :
    step s = some { s with stack := Stack.push s.stack 0, pc := stepPos w h s.dir s.pc } := by
  unfold step
  simp only [decodeChar, stepState, hm, hcell, hinput]

/-- `&` parses a decimal integer from the input stream, pushing its value and
    leaving the remaining input for later. -/
theorem step_inputInt (s : State w h) (hm : s.stringMode = false)
    (hcell : s.grid.get s.pc.1 s.pc.2 = '&') (rest : List Char) (v : Int)
    (hparse : parseInt s.input = (rest, v)) :
    step s = some { s with
      stack := Stack.push s.stack v,
      input := rest,
      pc := stepPos w h s.dir s.pc } := by
  unfold step
  simp only [decodeChar, stepState, hm, hcell, hparse]

/-- `#` at the last column, moving right, skips across the wrap and lands at
    column 1. -/
theorem step_trampoline_right_from_last {w h : ℕ} (hw : 2 ≤ w) (s : State w h) (y : ℕ)
    (hm : s.stringMode = false) (hcell : s.grid.get s.pc.1 s.pc.2 = '#')
    (hpc : s.pc = (w - 1, y)) (hdir : s.dir = .right) :
    step s = some { s with pc := (1, y % h) } := by
  have hmid : stepPos w h Direction.right (w - 1, y) = (0, y % h) := by
    unfold stepPos
    rw [Nat.sub_add_cancel (show 1 ≤ w by omega)]
    rw [Nat.mod_self]
  have hnext : stepPos w h Direction.right (0, y % h) = (1, y % h) := by
    unfold stepPos
    simp only [Nat.mod_eq_of_lt (show 1 < w by omega), Nat.mod_mod]
  rw [step_trampoline s hm hcell]
  simp only [hpc, hdir, hmid, hnext]

end LeanFunge
