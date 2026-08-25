/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanFunge.Theory.Step

/-!
# Step Semantics Tests
-/

namespace LeanFunge.Tests

open LeanFunge

example {w h : ℕ} (s : State w h) (hm : s.stringMode = false)
    (hcell : s.grid.get s.pc.1 s.pc.2 = '@') : step s = none :=
  step_halt_of_cell s hm hcell

example {w h : ℕ} (s : State w h) (hm : s.stringMode = false)
    (hcell : s.grid.get s.pc.1 s.pc.2 = '5') :
    step s = some { s with stack := Stack.push s.stack 5, pc := stepPos w h s.dir s.pc } :=
  step_push_digit s hm hcell

example {w h : ℕ} (s : State w h) (hm : s.stringMode = false)
    (hcell : s.grid.get s.pc.1 s.pc.2 = '+') (a b : Int) (rest : Stack)
    (hstack : s.stack = a :: b :: rest) :
    step s = some { s with stack := (b + a) :: rest, pc := stepPos w h s.dir s.pc } :=
  step_add s hm hcell a b rest hstack

example {w h : ℕ} (s : State w h) (hm : s.stringMode = false)
    (hcell : s.grid.get s.pc.1 s.pc.2 = '_') (v : Int) (rest : Stack)
    (hstack : s.stack = v :: rest) :
    step s = some { s with
      dir := if v = 0 then .right else .left,
      stack := rest,
      pc := stepPos w h (if v = 0 then .right else .left) s.pc } :=
  step_chooseH s hm hcell v rest hstack

example {w h : ℕ} (s : State w h) (hm : s.stringMode = false)
    (hcell : s.grid.get s.pc.1 s.pc.2 = '!') (v : Int) (rest : Stack)
    (hstack : s.stack = v :: rest) :
    step s = some { s with
      stack := (if v = 0 then 1 else 0) :: rest,
      pc := stepPos w h s.dir s.pc } :=
  step_not s hm hcell v rest hstack

example {w h : ℕ} (s : State w h) (hm : s.stringMode = true)
    (hcell : s.grid.get s.pc.1 s.pc.2 = 'a') :
    step s = some { s with
      stack := Stack.push s.stack (Int.ofNat 'a'.toNat),
      pc := stepPos w h s.dir s.pc } :=
  step_string_push s hm hcell

example {w h : ℕ} (s : State w h) (hm : s.stringMode = false)
    (hcell : s.grid.get s.pc.1 s.pc.2 = '#') :
    step s = some { s with pc := stepPos w h s.dir (stepPos w h s.dir s.pc) } :=
  step_trampoline s hm hcell

example {w h : ℕ} (s : State w h) (hm : s.stringMode = false)
    (hcell : s.grid.get s.pc.1 s.pc.2 = 'p') (y x v : Int) (rest : Stack)
    (hstack : s.stack = y :: x :: v :: rest) :
    step s = some { s with
      grid := Grid.put s.grid (Int.toNat x) (Int.toNat y) (Char.ofNat (Int.toNat v)),
      stack := rest, pc := stepPos w h s.dir s.pc } :=
  step_put s hm hcell y x v rest hstack

example {w h : ℕ} (s : State w h) (hm : s.stringMode = false)
    (hcell : s.grid.get s.pc.1 s.pc.2 = 'g') (y x : Int) (rest : Stack)
    (hstack : s.stack = y :: x :: rest) :
    step s = some { s with
      stack := Stack.push rest (Int.ofNat (s.grid.get (Int.toNat x) (Int.toNat y)).toNat),
      pc := stepPos w h s.dir s.pc } :=
  step_get s hm hcell y x rest hstack

example {w h : ℕ} (s : State w h) (hm : s.stringMode = false)
    (hcell : s.grid.get s.pc.1 s.pc.2 = ',') (v : Int) (rest : Stack)
    (hstack : s.stack = v :: rest) :
    step s = some { s with
      output := s.output.push (Char.ofNat (Int.toNat v)),
      stack := rest,
      pc := stepPos w h s.dir s.pc } :=
  step_printChar s hm hcell v rest hstack

example (c : Char) : decodeChar c = .nop ↔ c ∉ instrChars :=
  decodeChar_nop_iff c

example {w h : ℕ} (hw : 0 < w) (hh : 0 < h) (s : State w h) (instr : Instruction)
    (hne : instr ≠ .halt) :
    (stepState s instr).pc.1 < w ∧ (stepState s instr).pc.2 < h :=
  stepState_pc_lt hw hh s instr hne

example {w h : ℕ} (hw : 0 < w) (hh : 0 < h) (s : State w h) (ch : Char) :
    (stepString s ch).pc.1 < w ∧ (stepString s ch).pc.2 < h :=
  stepString_pc_lt hw hh s ch

example {w h : ℕ} (hw : 0 < w) (hh : 0 < h) {s s' : State w h}
    (hstep : step s = some s') : s'.pc.1 < w ∧ s'.pc.2 < h :=
  step_pc_lt hw hh hstep

example {w h : ℕ} (hw : 0 < w) (hh : 0 < h) (n : ℕ) {s s' : State w h}
    (hrun : run (n + 1) s = some s') : s'.pc.1 < w ∧ s'.pc.2 < h :=
  run_pc_lt hw hh n hrun

end LeanFunge.Tests
