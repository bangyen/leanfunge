/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanFunge.Theory.Completeness.TwoCounter

/-!
# Two-Counter Machine Tests
-/

namespace LeanFunge.Tests

open LeanFunge.Completeness

example (c : Fin 2) (v : ℕ) (s : CMState) : CMInstr.read c (CMInstr.write c v s) = v :=
  CMInstr.read_write c v s

example (c : Fin 2) (s : CMState) : CMInstr.write c (CMInstr.read c s) s = s :=
  CMInstr.write_read c s

example (prog : CMProgram) (s : CMState) : CMInstr.run prog 0 s = some s :=
  CMInstr.run_zero prog s

example (prog : CMProgram) (s : CMState) (n : ℕ) :
    CMInstr.run prog (n + 1) s = (CMInstr.run prog n s).bind (CMInstr.step prog) :=
  CMInstr.run_succ prog n s

example (prog : CMProgram) (s : CMState) (c : Fin 2)
    (hget : CMInstr.instrAt prog s.pc = .inc c) :
    CMInstr.step prog s = some { (CMInstr.incCounter c s) with pc := s.pc + 1 } :=
  CMInstr.step_inc prog s c hget

example (prog : CMProgram) (s : CMState) (c : Fin 2) (k : ℕ)
    (hget : CMInstr.instrAt prog s.pc = .decz c k) (hzero : CMInstr.read c s = 0) :
    CMInstr.step prog s = some { s with pc := k } :=
  CMInstr.step_decz_zero prog s c k hget hzero

example (prog : CMProgram) (s : CMState) (c : Fin 2) (k : ℕ)
    (hget : CMInstr.instrAt prog s.pc = .decz c k) (hpos : CMInstr.read c s ≠ 0) :
    CMInstr.step prog s = some { (CMInstr.decCounter c s) with pc := s.pc + 1 } :=
  CMInstr.step_decz_nonzero prog s c k hget hpos

example (prog : CMProgram) (s : CMState) (hget : CMInstr.instrAt prog s.pc = .halt) :
    CMInstr.step prog s = none :=
  CMInstr.step_halt prog s hget

example (prog : CMProgram) (s : CMState) {n m : ℕ}
    (h : CMInstr.run prog n s = none) : CMInstr.run prog (n + m) s = none :=
  CMInstr.run_halts_mono prog s h

example (prog : CMProgram) (s : CMState) {n : ℕ}
    (h : CMInstr.run prog n s = none) : CMInstr.halts prog s :=
  CMInstr.halts_of_run_eq_none prog s h

end LeanFunge.Tests
