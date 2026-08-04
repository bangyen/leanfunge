/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanFunge.Core.Semantics
import Mathlib.Data.Nat.Notation

/-!
# Step Semantics

## Theorems

* `run_zero`: Running zero steps returns the initial state.
* `run_succ`: One more step runs one more transition.
* `run_halts_mono`: Once a program halts, it stays halted.
* `halts_of_run_eq_none`: A `none` run witnesses halting.
* `step_halt_of_cell`: `@` halts the program.
* `step_push_digit`: A digit is pushed onto the stack.
* `step_add`: `+` pushes the sum of the top two values.
* `step_sub`: `-` pushes the difference of the top two values.
* `step_mul`: `*` pushes the product of the top two values.
* `step_not`: `!` pushes `1` when the top is `0` and `0` otherwise.
* `step_dir_right`: `>` sets the direction of travel to the right.
* `step_dir_left`: `<` sets the direction of travel to the left.
* `step_dir_up`: `^` sets the direction of travel up.
* `step_dir_down`: `v` sets the direction of travel down.
* `step_chooseH`: `_` chooses horizontally on the top of the stack.
* `step_chooseV`: `|` chooses vertically on the top of the stack.
* `step_string_enter`: `"` toggles string mode on.
* `step_string_push`: Inside string mode, characters are pushed as codes.
* `step_string_exit`: A second `"` toggles string mode off.
* `step_trampoline`: `#` skips the next cell.
* `step_put`: `p` stores a value in the playfield.
* `step_get`: `g` fetches a value from the playfield.
* `step_printChar`: `,` appends a character to the output.
* `step_printInt`: `.` appends the decimal form of an integer to the output.
-/

namespace LeanFunge

/-- Running zero steps returns the initial state. -/
theorem run_zero (s : State w h) : run 0 s = some s :=
  rfl

/-- One more step runs one more transition. -/
theorem run_succ (k : ℕ) (s : State w h) : run (Nat.succ k) s = (run k s).bind step :=
  rfl

/-- Once a program halts, it stays halted. -/
theorem run_halts_mono (s : State w h) {n m : ℕ} (h : run n s = none) :
    run (n + m) s = none := by
  induction m with
  | zero => rw [Nat.add_zero]; exact h
  | succ m ih =>
      rw [Nat.add_succ]
      rw [run_succ]
      rw [ih]
      rfl

/-- A `none` run witnesses halting. -/
theorem halts_of_run_eq_none (s : State w h) {n : ℕ} (h : run n s = none) : halts s :=
  ⟨n, h⟩

/-- `@` halts the program. -/
theorem step_halt_of_cell (s : State w h) (hm : s.stringMode = false)
    (hcell : s.grid.get s.pc.1 s.pc.2 = '@') : step s = none := by
  unfold step
  simp only [decodeChar, hm, hcell]

/-- A digit is pushed onto the stack. -/
theorem step_push_digit (s : State w h) (hm : s.stringMode = false)
    (hcell : s.grid.get s.pc.1 s.pc.2 = '5') :
    step s = some { s with stack := Stack.push s.stack 5, pc := stepPos w h s.dir s.pc } := by
  unfold step
  simp only [decodeChar, stepState, Stack.push, hm, hcell]

/-- `+` pushes the sum of the top two values. -/
theorem step_add (s : State w h) (hm : s.stringMode = false)
    (hcell : s.grid.get s.pc.1 s.pc.2 = '+') (a b : Int) (rest : Stack)
    (hstack : s.stack = a :: b :: rest) :
    step s = some { s with stack := (b + a) :: rest, pc := stepPos w h s.dir s.pc } := by
  unfold step
  simp only [decodeChar, stepState, Stack.applyBinary, hm, hcell, hstack]

/-- `-` pushes the difference of the top two values. -/
theorem step_sub (s : State w h) (hm : s.stringMode = false)
    (hcell : s.grid.get s.pc.1 s.pc.2 = '-') (a b : Int) (rest : Stack)
    (hstack : s.stack = a :: b :: rest) :
    step s = some { s with stack := (b - a) :: rest, pc := stepPos w h s.dir s.pc } := by
  unfold step
  simp only [decodeChar, stepState, Stack.applyBinary, hm, hcell, hstack]

/-- `*` pushes the product of the top two values. -/
theorem step_mul (s : State w h) (hm : s.stringMode = false)
    (hcell : s.grid.get s.pc.1 s.pc.2 = '*') (a b : Int) (rest : Stack)
    (hstack : s.stack = a :: b :: rest) :
    step s = some { s with stack := (b * a) :: rest, pc := stepPos w h s.dir s.pc } := by
  unfold step
  simp only [decodeChar, stepState, Stack.applyBinary, hm, hcell, hstack]

/-- `!` pushes `1` when the top is `0` and `0` otherwise. -/
theorem step_not (s : State w h) (hm : s.stringMode = false)
    (hcell : s.grid.get s.pc.1 s.pc.2 = '!') (v : Int) (rest : Stack)
    (hstack : s.stack = v :: rest) :
    step s = some { s with
      stack := (if v = 0 then 1 else 0) :: rest,
      pc := stepPos w h s.dir s.pc } := by
  unfold step
  simp only [decodeChar, stepState, Stack.push, Stack.top, Stack.pop, Stack.drop, hm, hcell, hstack]

/-- `>` sets the direction of travel to the right. -/
theorem step_dir_right (s : State w h) (hm : s.stringMode = false)
    (hcell : s.grid.get s.pc.1 s.pc.2 = '>') :
    step s = some { s with dir := .right, pc := stepPos w h .right s.pc } := by
  unfold step
  simp only [decodeChar, stepState, hm, hcell]

/-- `<` sets the direction of travel to the left. -/
theorem step_dir_left (s : State w h) (hm : s.stringMode = false)
    (hcell : s.grid.get s.pc.1 s.pc.2 = '<') :
    step s = some { s with dir := .left, pc := stepPos w h .left s.pc } := by
  unfold step
  simp only [decodeChar, stepState, hm, hcell]

/-- `^` sets the direction of travel up. -/
theorem step_dir_up (s : State w h) (hm : s.stringMode = false)
    (hcell : s.grid.get s.pc.1 s.pc.2 = '^') :
    step s = some { s with dir := .up, pc := stepPos w h .up s.pc } := by
  unfold step
  simp only [decodeChar, stepState, hm, hcell]

/-- `v` sets the direction of travel down. -/
theorem step_dir_down (s : State w h) (hm : s.stringMode = false)
    (hcell : s.grid.get s.pc.1 s.pc.2 = 'v') :
    step s = some { s with dir := .down, pc := stepPos w h .down s.pc } := by
  unfold step
  simp only [decodeChar, stepState, hm, hcell]

/-- `_` chooses horizontally on the top of the stack. -/
theorem step_chooseH (s : State w h) (hm : s.stringMode = false)
    (hcell : s.grid.get s.pc.1 s.pc.2 = '_') (v : Int) (rest : Stack)
    (hstack : s.stack = v :: rest) :
    step s = some { s with
      dir := if v = 0 then .right else .left,
      stack := rest,
      pc := stepPos w h (if v = 0 then .right else .left) s.pc } := by
  unfold step
  simp only [decodeChar, stepState, Direction.chooseH, Stack.top, Stack.pop,
    Stack.drop, hm, hcell, hstack]

/-- `|` chooses vertically on the top of the stack. -/
theorem step_chooseV (s : State w h) (hm : s.stringMode = false)
    (hcell : s.grid.get s.pc.1 s.pc.2 = '|') (v : Int) (rest : Stack)
    (hstack : s.stack = v :: rest) :
    step s = some { s with
      dir := if v = 0 then .down else .up,
      stack := rest,
      pc := stepPos w h (if v = 0 then .down else .up) s.pc } := by
  unfold step
  simp only [decodeChar, stepState, Direction.chooseV, Stack.top, Stack.pop,
    Stack.drop, hm, hcell, hstack]

/-- `"` toggles string mode on. -/
theorem step_string_enter (s : State w h) (hm : s.stringMode = false)
    (hcell : s.grid.get s.pc.1 s.pc.2 = '"') :
    step s = some { s with stringMode := true, pc := stepPos w h s.dir s.pc } := by
  unfold step
  simp only [decodeChar, stepState, hm, hcell]

/-- Inside string mode, characters are pushed as codes. -/
theorem step_string_push (s : State w h) (hm : s.stringMode = true)
    (hcell : s.grid.get s.pc.1 s.pc.2 = 'a') :
    step s = some { s with
      stack := Stack.push s.stack (Int.ofNat 'a'.toNat),
      pc := stepPos w h s.dir s.pc } := by
  unfold step
  have hq : ('a'.toNat == '"'.toNat) = false := by decide
  simp only [stepString, Stack.push, hq, hm, hcell]

/-- A second `"` toggles string mode off. -/
theorem step_string_exit (s : State w h) (hm : s.stringMode = true)
    (hcell : s.grid.get s.pc.1 s.pc.2 = '"') :
    step s = some { s with stringMode := false, pc := stepPos w h s.dir s.pc } := by
  unfold step
  have hq : ('"'.toNat == '"'.toNat) = true := by decide
  simp only [stepString, hq, hm, hcell]

/-- `#` skips the next cell. -/
theorem step_trampoline (s : State w h) (hm : s.stringMode = false)
    (hcell : s.grid.get s.pc.1 s.pc.2 = '#') :
    step s = some { s with pc := stepPos w h s.dir (stepPos w h s.dir s.pc) } := by
  unfold step
  simp only [decodeChar, stepState, hm, hcell]

/-- `p` stores a value in the playfield. -/
theorem step_put (s : State w h) (hm : s.stringMode = false)
    (hcell : s.grid.get s.pc.1 s.pc.2 = 'p') (y x v : Int) (rest : Stack)
    (hstack : s.stack = y :: x :: v :: rest) :
    step s = some { s with
      grid := Grid.put s.grid (Int.toNat x) (Int.toNat y) (Char.ofNat (Int.toNat v)),
      stack := rest, pc := stepPos w h s.dir s.pc } := by
  unfold step
  simp only [decodeChar, stepState, Stack.pop, hm, hcell, hstack]

/-- `g` fetches a value from the playfield. -/
theorem step_get (s : State w h) (hm : s.stringMode = false)
    (hcell : s.grid.get s.pc.1 s.pc.2 = 'g') (y x : Int) (rest : Stack)
    (hstack : s.stack = y :: x :: rest) :
    step s = some { s with
      stack := Stack.push rest (Int.ofNat (s.grid.get (Int.toNat x) (Int.toNat y)).toNat),
      pc := stepPos w h s.dir s.pc } := by
  unfold step
  simp only [decodeChar, stepState, Stack.pop, hm, hcell, hstack]

/-- `,` appends a character to the output. -/
theorem step_printChar (s : State w h) (hm : s.stringMode = false)
    (hcell : s.grid.get s.pc.1 s.pc.2 = ',') (v : Int) (rest : Stack)
    (hstack : s.stack = v :: rest) :
    step s = some { s with
      output := s.output.push (Char.ofNat (Int.toNat v)),
      stack := rest,
      pc := stepPos w h s.dir s.pc } := by
  unfold step
  simp only [decodeChar, stepState, Stack.top, Stack.pop, Stack.drop, hm, hcell, hstack]

/-- `.` appends the decimal form of an integer to the output. -/
theorem step_printInt (s : State w h) (hm : s.stringMode = false)
    (hcell : s.grid.get s.pc.1 s.pc.2 = '.') (v : Int) (rest : Stack)
    (hstack : s.stack = v :: rest) :
    step s = some { s with
      output := s.output ++ toString v,
      stack := rest,
      pc := stepPos w h s.dir s.pc } := by
  unfold step
  simp only [decodeChar, stepState, Stack.top, Stack.pop, Stack.drop, hm, hcell, hstack]

end LeanFunge
