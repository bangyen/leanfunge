/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanFunge.Theory.Completeness.LinearSimulation
import LeanFunge.Theory.Step
import Mathlib.Data.Nat.Notation

/-!
# The Branch-Free Simulation Theorems

The main results of the branch-free simulation: the interpreter reaches the
trailing `@` with the encoded final counters on the stack, then halts, and the
interpreter stack is exactly the encoding of the two-counter machine's final
counters.

## Theorems

* `linearRow_get_halt`: The cell at the trailing `@` of a branch-free program.
* `linear_stack`: The interpreter reaches the trailing `@` with the encoded
  final counters on the stack.
* `linear_halts`: The interpreter halts.
* `linear_simulation`: The interpreter stack is the encoding of the final
  two-counter machine counters.
-/

namespace LeanFunge

namespace Completeness

/-- The interpreter reaches the trailing `@` with the encoded final counters
    on the stack. -/
theorem linear_stack (prog : CMProgram) (c1 c2 : ℕ) (hpos : 0 < prog.length)
    (hinc : ∀ i, i + 1 < prog.length → prog.getD i .halt = .inc 0 ∨ prog.getD i .halt = .inc 1) :
    (run (1 + 2 * (prog.length - 1)) (linearStart prog c1 c2)).map (fun s => s.stack)
      = some [Int.ofNat (encode (foldIncs prog (prog.length - 1) (CMInstr.startCM c1 c2)).c1
                                 (foldIncs prog (prog.length - 1) (CMInstr.startCM c1 c2)).c2)] := by
  rw [linear_prefix prog c1 c2 (prog.length - 1) (by
      intro i hi
      exact hinc i (by omega))
      (by
        apply linearRow_length prog (prog.length - 1)
        intro i hi
        exact hinc i (by omega))]
  rfl

/-- The cell at the trailing `@` of a branch-free program. -/
theorem linearRow_get_halt (prog : CMProgram) (hpos : 0 < prog.length)
    (hinc : ∀ i, i + 1 < prog.length → prog.getD i .halt = .inc 0 ∨ prog.getD i .halt = .inc 1)
    (hlast : prog.getD (prog.length - 1) .halt = .halt) :
    (linearRow prog).getD (1 + 2 * (prog.length - 1)) ' ' = '@' := by
  unfold linearRow
  rw [show ('>' :: linearRowAux prog).getD (1 + 2 * (prog.length - 1)) ' '
      = (linearRowAux prog).getD (2 * (prog.length - 1)) ' ' by
        rw [show 1 + 2 * (prog.length - 1) = Nat.succ (2 * (prog.length - 1)) by omega]
        rfl]
  rw [getD_eq_drop_getD]
  rw [linearRowAux_drop prog (prog.length - 1) (by
      intro i hi
      exact hinc i (by omega))]
  rw [linearRowAux_cons]
  rw [show (prog.drop (prog.length - 1)).getD 0 .halt = prog.getD (prog.length - 1) .halt by
      rw [← getD_eq_drop_getD prog (prog.length - 1) .halt]]
  rw [hlast]
  have hdrop1 : (prog.drop (prog.length - 1)).drop 1 = [] := by
    apply List.drop_eq_nil_of_le
    rw [List.length_drop]
    omega
  rw [hdrop1]
  rfl

/-- The interpreter halts after the trailing `@`. -/
theorem linear_halts (prog : CMProgram) (c1 c2 : ℕ) (hpos : 0 < prog.length)
    (hinc : ∀ i, i + 1 < prog.length → prog.getD i .halt = .inc 0 ∨ prog.getD i .halt = .inc 1)
    (hlast : prog.getD (prog.length - 1) .halt = .halt) :
    run (2 + 2 * (prog.length - 1)) (linearStart prog c1 c2) = none := by
  rw [show 2 + 2 * (prog.length - 1) = (1 + 2 * (prog.length - 1)) + 1 by omega]
  rw [run_append (linearStart prog c1 c2)
      { linearStart prog c1 c2 with
        stack := [Int.ofNat (encode (foldIncs prog (prog.length - 1) (CMInstr.startCM c1 c2)).c1
                                     (foldIncs prog (prog.length - 1) (CMInstr.startCM c1 c2)).c2)],
        pc := (1 + 2 * (prog.length - 1), 0) } none (1 + 2 * (prog.length - 1)) 1]
  · rw [linear_prefix prog c1 c2 (prog.length - 1) (by
        intro i hi
        exact hinc i (by omega))
        (by
          apply linearRow_length prog (prog.length - 1)
          intro i hi
          exact hinc i (by omega))]
  · have hcell : { linearStart prog c1 c2 with
          stack := [Int.ofNat (encode (foldIncs prog (prog.length - 1) (CMInstr.startCM c1 c2)).c1
                                       (foldIncs prog (prog.length - 1) (CMInstr.startCM c1 c2)).c2)],
          pc := (1 + 2 * (prog.length - 1), 0) }.grid.get (1 + 2 * (prog.length - 1)) 0 = '@' := by
        change (linearGrid prog).get (1 + 2 * (prog.length - 1)) 0 = '@'
        rw [linearGrid_get prog (1 + 2 * (prog.length - 1)) (by
            apply linearRow_length prog (prog.length - 1)
            intro i hi
            exact hinc i (by omega))]
        exact linearRow_get_halt prog hpos hinc hlast
    rw [show run 1 { linearStart prog c1 c2 with
          stack := [Int.ofNat (encode (foldIncs prog (prog.length - 1) (CMInstr.startCM c1 c2)).c1
                                       (foldIncs prog (prog.length - 1) (CMInstr.startCM c1 c2)).c2)],
          pc := (1 + 2 * (prog.length - 1), 0) }
        = step { linearStart prog c1 c2 with
          stack := [Int.ofNat (encode (foldIncs prog (prog.length - 1) (CMInstr.startCM c1 c2)).c1
                                       (foldIncs prog (prog.length - 1) (CMInstr.startCM c1 c2)).c2)],
          pc := (1 + 2 * (prog.length - 1), 0) } by rfl]
    have hstep : step { linearStart prog c1 c2 with
          stack := [Int.ofNat (encode (foldIncs prog (prog.length - 1) (CMInstr.startCM c1 c2)).c1
                                       (foldIncs prog (prog.length - 1) (CMInstr.startCM c1 c2)).c2)],
          pc := (1 + 2 * (prog.length - 1), 0) } = none :=
      step_halt_of_cell { linearStart prog c1 c2 with
          stack := [Int.ofNat (encode (foldIncs prog (prog.length - 1) (CMInstr.startCM c1 c2)).c1
                                       (foldIncs prog (prog.length - 1) (CMInstr.startCM c1 c2)).c2)],
          pc := (1 + 2 * (prog.length - 1), 0) } (by rfl) hcell
    exact hstep

/-- The interpreter stack is the encoding of the final two-counter machine
    counters. -/
theorem linear_simulation (prog : CMProgram) (c1 c2 : ℕ) (hpos : 0 < prog.length)
    (hinc : ∀ i, i + 1 < prog.length → prog.getD i .halt = .inc 0 ∨ prog.getD i .halt = .inc 1) :
    (run (1 + 2 * (prog.length - 1)) (linearStart prog c1 c2)).map (fun s => s.stack)
      = (CMInstr.run prog (prog.length - 1) (CMInstr.startCM c1 c2)).map
          (fun s => [Int.ofNat (encode s.c1 s.c2)]) := by
  rw [linear_stack prog c1 c2 hpos hinc]
  rw [linear_prefix_2cm prog c1 c2 (prog.length - 1) (by
      intro i hi
      exact hinc i (by omega))]
  rfl

end Completeness

end LeanFunge
