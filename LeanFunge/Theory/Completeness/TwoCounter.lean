/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import Mathlib.Data.Nat.Notation

/-!
# Two-Counter Machines

A Minsky two-counter machine (2CM) is a finite program of instructions acting
on two natural-number counters and a program counter. 2CMs are one of the
standard "small" universal models: with two counters and the single
decrement-if-nonzero instruction the model is Turing complete.

## Main definitions

* `CMInstr`: The instruction set `inc`, `decz`, and `halt`.
* `CMProgram`: A 2CM program (a list of instructions indexed by the pc).
* `CMState`: The machine state `(pc, c1, c2)`.
* `CMInstr.read`: Read a named counter.
* `CMInstr.write`: Overwrite a named counter.
* `CMInstr.incCounter`: Increment a named counter.
* `CMInstr.decCounter`: Decrement a named counter (total).
* `CMInstr.instrAt`: The instruction at a program counter.
* `CMInstr.step`: The single-step transition.
* `CMInstr.run`: Run the machine for finitely many steps.
* `CMInstr.halts`: Whether a state halts.

## Theorems

* `read_write`: Writing a counter then reading it back recovers the value.
* `write_read`: Reading a counter then writing it back is the identity.
* `run_zero`: Running zero steps returns the initial state.
* `run_succ`: One more step runs one more transition.
* `step_inc`: `inc` increments the counter and advances the pc.
* `step_decz_zero`: `decz` jumps to its target when the counter is zero.
* `step_decz_nonzero`: `decz` decrements and advances when the counter is
  nonzero.
* `step_halt`: `halt` stops the machine.
* `run_halts_mono`: Once a machine halts, it stays halted.
* `halts_of_run_eq_none`: A `none` run witnesses halting.
-/

namespace LeanFunge

namespace Completeness

/-- A Minsky two-counter machine instruction. `decz c k` jumps to `k` when
    counter `c` is zero and otherwise decrements `c` and falls through. -/
inductive CMInstr where
  | inc (c : Fin 2)        -- increment counter `c`, advance
  | decz (c : Fin 2) (k : ℕ)  -- jump to `k` when counter `c` is zero, else decrement
  | halt                   -- stop
  deriving DecidableEq, Repr

/-- A 2CM program: a list of instructions indexed by the program counter. A pc
    past the end of the list behaves as `halt`. -/
abbrev CMProgram := List CMInstr

/-- The state of a two-counter machine: the program counter and the two
    natural counters. -/
structure CMState where
  /-- The program counter. -/
  pc : ℕ
  /-- The first counter. -/
  c1 : ℕ
  /-- The second counter. -/
  c2 : ℕ
  deriving DecidableEq

namespace CMInstr

/-- Read the value of counter `c`. -/
def read (c : Fin 2) (s : CMState) : ℕ :=
  if c.val = 0 then s.c1 else s.c2

/-- Write a value into counter `c`. -/
def write (c : Fin 2) (v : ℕ) (s : CMState) : CMState :=
  if c.val = 0 then { s with c1 := v } else { s with c2 := v }

/-- Increment counter `c`. -/
def incCounter (c : Fin 2) (s : CMState) : CMState :=
  write c (read c s + 1) s

/-- Decrement counter `c`, total: decrementing zero leaves it at zero. -/
def decCounter (c : Fin 2) (s : CMState) : CMState :=
  write c (read c s - 1) s

/-- The instruction at a program counter; a pc past the end of the program
    behaves as `halt`. -/
def instrAt (prog : CMProgram) (pc : ℕ) : CMInstr :=
  prog.getD pc halt

/-- Execute one instruction, returning `none` at `halt`. -/
def step (prog : CMProgram) (s : CMState) : Option CMState :=
  match instrAt prog s.pc with
  | .halt => none
  | .inc c => some { (incCounter c s) with pc := s.pc + 1 }
  | .decz c k =>
      if read c s = 0 then some { s with pc := k }
      else some { (decCounter c s) with pc := s.pc + 1 }

/-- Run the machine for `n` steps, threading `none` once it halts. -/
def run (prog : CMProgram) (n : ℕ) (s : CMState) : Option CMState :=
  match n with
  | 0 => some s
  | n + 1 => (run prog n s).bind (step prog)

/-- A state halts if it reaches `none` after finitely many steps. -/
def halts (prog : CMProgram) (s : CMState) : Prop :=
  ∃ n : ℕ, run prog n s = none

/-- Writing a counter then reading it back recovers the written value. -/
theorem read_write (c : Fin 2) (v : ℕ) (s : CMState) :
    read c (write c v s) = v := by
  by_cases h : c.val = 0 <;> simp only [read, write, h, if_true, if_false]

/-- Reading a counter then writing it back is the identity on the counters. -/
theorem write_read (c : Fin 2) (s : CMState) :
    write c (read c s) s = s := by
  by_cases h : c.val = 0 <;> simp only [read, write, h, if_true, if_false]

/-- Running zero steps returns the initial state. -/
theorem run_zero (prog : CMProgram) (s : CMState) : run prog 0 s = some s :=
  rfl

/-- One more step runs one more transition. -/
theorem run_succ (prog : CMProgram) (n : ℕ) (s : CMState) :
    run prog (n + 1) s = (run prog n s).bind (step prog) :=
  rfl

/-- `inc` increments the counter and advances the pc. -/
theorem step_inc (prog : CMProgram) (s : CMState) (c : Fin 2)
    (hget : instrAt prog s.pc = .inc c) :
    step prog s = some { (incCounter c s) with pc := s.pc + 1 } := by
  simp only [step, hget]

/-- `decz` jumps to its target when the counter is zero. -/
theorem step_decz_zero (prog : CMProgram) (s : CMState) (c : Fin 2) (k : ℕ)
    (hget : instrAt prog s.pc = .decz c k) (hzero : read c s = 0) :
    step prog s = some { s with pc := k } := by
  simp only [step, hget, hzero, if_true]

/-- `decz` decrements and advances when the counter is nonzero. -/
theorem step_decz_nonzero (prog : CMProgram) (s : CMState) (c : Fin 2) (k : ℕ)
    (hget : instrAt prog s.pc = .decz c k) (hpos : read c s ≠ 0) :
    step prog s = some { (decCounter c s) with pc := s.pc + 1 } := by
  simp only [step, hget, hpos, if_false]

/-- `halt` stops the machine. -/
theorem step_halt (prog : CMProgram) (s : CMState)
    (hget : instrAt prog s.pc = .halt) :
    step prog s = none := by
  simp only [step, hget]

/-- Once a machine halts, it stays halted. -/
theorem run_halts_mono (prog : CMProgram) (s : CMState) {n m : ℕ}
    (h : run prog n s = none) : run prog (n + m) s = none := by
  induction m with
  | zero => rw [Nat.add_zero]; exact h
  | succ m ih =>
      rw [Nat.add_succ]
      rw [run_succ]
      rw [ih]
      rfl

/-- A `none` run witnesses halting. -/
theorem halts_of_run_eq_none (prog : CMProgram) (s : CMState) {n : ℕ}
    (h : run prog n s = none) : halts prog s :=
  ⟨n, h⟩

end CMInstr

end Completeness

end LeanFunge
