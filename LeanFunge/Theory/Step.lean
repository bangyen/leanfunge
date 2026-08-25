/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanFunge.Core.Semantics
import LeanFunge.Theory.Direction
import Mathlib.Data.Nat.Notation

/-!
# Step Semantics

## Main definitions

* `instrChars`: The characters the instruction table assigns a meaning to.

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
* `decodeChar_nop_iff`: A character decodes to `nop` exactly when it is
  outside the instruction table.
* `step_eq_stepState`: Outside string mode, a non-halting step is the decoded
  instruction's state transition.
* `step_eq_stepString`: In string mode, a step is the string-mode transition.
* `decodeChar_ne_halt_of_step`: A step with a successor outside string mode
  did not execute the halt instruction.
* `stringMode_false_of_not`: Not being in string mode means string mode is
  off.
* `stepState_stringMode_of_ne`: Every instruction except the toggle leaves
  string mode unchanged.
* `stepState_stringMode_toggle`: The toggle instruction turns string mode on.
* `stepState_dir_of_ne`: Every instruction that does not turn leaves the
  direction unchanged.
* `stepState_pc_lt`: Every state transition leaves the pointer inside the
  playfield.
* `stepString_pc_lt`: A string-mode transition leaves the pointer inside the
  playfield.
* `step_pc_lt`: Every step leaves the pointer inside the playfield.
* `run_pc_lt`: After at least one step, the pointer is inside the
  playfield.
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
      output := s.output ++ String.ofList (formatInt v),
      stack := rest,
      pc := stepPos w h s.dir s.pc } := by
  unfold step
  simp only [decodeChar, stepState, Stack.top, Stack.pop, Stack.drop, hm, hcell, hstack]

/-- The characters the instruction table assigns a meaning to. -/
def instrChars : List Char :=
  ['0','1','2','3','4','5','6','7','8','9','+','-','*','/','%','!','`',
   '>','<','^','v','_','|','?','"',':','\\','$','.',',','#','p','g','&','~','@']

/-- A character decodes to `nop` exactly when it is outside the instruction
    table: every other character is a no-op. -/
theorem decodeChar_nop_iff (c : Char) : decodeChar c = .nop ↔ c ∉ instrChars := by
  constructor
  · intro hnop hmem
    revert hnop
    simp only [instrChars, List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h |
      h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;>
      subst h <;> simp only [decodeChar, reduceCtorEq] <;> exact id
  · intro hne
    unfold decodeChar
    split <;>
      first
        | rfl
        | (exfalso
           apply hne
           simp only [instrChars, List.mem_cons]
           decide)

/-! ### Reducing a step to its instruction

Most single-step proofs begin by unfolding `step` into the decoded
instruction's `stepState` transition, then reasoning about one field. These
lemmas do that unfolding once so the individual proofs do not each repeat the
instruction match. -/

/-- Outside string mode, a non-halting step is exactly the decoded
    instruction's state transition. -/
theorem step_eq_stepState (s : State w h) (hm : s.stringMode = false)
    (hne : decodeChar (s.grid.get s.pc.1 s.pc.2) ≠ .halt) :
    step s = some (stepState s (decodeChar (s.grid.get s.pc.1 s.pc.2))) := by
  unfold step
  dsimp only
  rw [hm]
  cases hins : decodeChar (s.grid.get s.pc.1 s.pc.2) with
  | halt => exact absurd hins hne
  | _ => rfl

/-- In string mode, a step is exactly the string-mode transition. -/
theorem step_eq_stepString (s : State w h) (hm : s.stringMode = true) :
    step s = some (stepString s (s.grid.get s.pc.1 s.pc.2)) := by
  unfold step
  dsimp only
  rw [hm]

/-- A step that produces a successor outside string mode did not execute the
    halt instruction. -/
theorem decodeChar_ne_halt_of_step {s s' : State w h} (hm : s.stringMode = false)
    (hstep : step s = some s') :
    decodeChar (s.grid.get s.pc.1 s.pc.2) ≠ .halt := by
  intro hc
  unfold step at hstep
  dsimp only at hstep
  rw [hm, hc] at hstep
  exact absurd hstep (by simp only [reduceCtorEq, not_false_eq_true])

/-- Not being in string mode means string mode is off. -/
theorem stringMode_false_of_not {s : State w h} (hs : ¬ s.stringMode = true) :
    s.stringMode = false := by
  cases hb : s.stringMode
  · rfl
  · exact absurd hb hs

/-- Every instruction except `"` leaves string mode unchanged. -/
theorem stepState_stringMode_of_ne (s : State w h) (instr : Instruction)
    (hne : instr ≠ .stringMode) :
    (stepState s instr).stringMode = s.stringMode := by
  cases instr with
  | stringMode => exact absurd rfl hne
  | inputChar =>
      unfold stepState
      cases h : s.input <;> rfl
  | _ => rfl

/-- The `"` instruction turns string mode on. -/
theorem stepState_stringMode_toggle (s : State w h) :
    (stepState s .stringMode).stringMode = true := rfl

/-- Every instruction that does not turn leaves the direction unchanged. -/
theorem stepState_dir_of_ne (s : State w h) (instr : Instruction)
    (hr : instr ≠ .right) (hl : instr ≠ .left) (hu : instr ≠ .up)
    (hd : instr ≠ .down) (hch : instr ≠ .chooseH) (hcv : instr ≠ .chooseV) :
    (stepState s instr).dir = s.dir := by
  cases instr with
  | right => exact absurd rfl hr
  | left => exact absurd rfl hl
  | up => exact absurd rfl hu
  | down => exact absurd rfl hd
  | chooseH => exact absurd rfl hch
  | chooseV => exact absurd rfl hcv
  | inputChar =>
      unfold stepState
      cases h : s.input <;> rfl
  | _ => rfl

/-! ### The pointer invariant

Every pointer update goes through `stepPos`, which reduces its coordinates
modulo the playfield size, so the interpreter never carries an out-of-range
pointer after a step. The initial pointer of `State.init` is `(0, 0)`, in
range whenever the playfield is non-empty. A hand-built out-of-range pointer
is harmless in any case, since `Grid.get` wraps its coordinates
(`get_eq_get_mod`). -/

/-- Every state transition leaves the pointer inside the playfield. -/
theorem stepState_pc_lt (hw : 0 < w) (hh : 0 < h) (s : State w h)
    (instr : Instruction) (hne : instr ≠ .halt) :
    (stepState s instr).pc.1 < w ∧ (stepState s instr).pc.2 < h := by
  cases instr with
  | halt => exact absurd rfl hne
  | inputChar =>
      unfold stepState
      cases s.input <;> exact stepPos_lt hw hh _ _
  | _ => exact stepPos_lt hw hh _ _

/-- A string-mode transition also leaves the pointer inside the playfield. -/
theorem stepString_pc_lt (hw : 0 < w) (hh : 0 < h) (s : State w h) (ch : Char) :
    (stepString s ch).pc.1 < w ∧ (stepString s ch).pc.2 < h := by
  unfold stepString
  cases (ch.toNat == '"'.toNat) <;> exact stepPos_lt hw hh _ _

/-- Every step leaves the pointer inside the playfield, whatever the pointer
    was before: the interpreter never carries an out-of-range pointer. -/
theorem step_pc_lt (hw : 0 < w) (hh : 0 < h) {s s' : State w h}
    (hstep : step s = some s') : s'.pc.1 < w ∧ s'.pc.2 < h := by
  by_cases hsm : s.stringMode = true
  · rw [step_eq_stepString s hsm] at hstep
    injection hstep with hs'
    rw [← hs']
    exact stepString_pc_lt hw hh s _
  · have hf : s.stringMode = false := stringMode_false_of_not hsm
    have hnh := decodeChar_ne_halt_of_step hf hstep
    rw [step_eq_stepState s hf hnh] at hstep
    injection hstep with hs'
    rw [← hs']
    exact stepState_pc_lt hw hh s _ hnh

/-- After at least one step, the pointer is inside the playfield. -/
theorem run_pc_lt (hw : 0 < w) (hh : 0 < h) (n : ℕ) {s s' : State w h}
    (hrun : run (n + 1) s = some s') : s'.pc.1 < w ∧ s'.pc.2 < h := by
  rcases hn : run n s with _ | sn
  · rw [run, hn] at hrun; cases hrun
  · rw [run, hn] at hrun
    exact step_pc_lt hw hh (by simpa only using hrun)

end LeanFunge
