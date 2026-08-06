/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanFunge.Theory.Completeness.Simulation

/-!
# Concrete Simulation Tests
-/

namespace LeanFunge.Tests

open LeanFunge.Completeness

example : CMInstr.run transferProgram 3 (startCM 1 0) = some { pc := 3, c1 := 1, c2 := 1 } :=
  program_end

example : CMInstr.run transferProgram 4 (startCM 1 0) = none :=
  program_halts

example : (run 39 (start 1 0)).map (fun s => s.stack) = some [Int.ofNat (encode 1 1)] :=
  transfer_stack

example : run 40 (start 1 0) = none :=
  transfer_halts

example :
    (run 8 (start 1 0)).map (fun s => (s.stack, s.pc)) = some ([Int.ofNat (encode 1 1)], (0, 5)) :=
  decz_entry_stack

example :
    (run 20 (start 1 0)).map (fun s => (s.stack, s.pc)) = some ([Int.ofNat (encode 0 1)], (0, 9)) :=
  decz_continue_entry

example : (run 23 (start 0 0)).map (fun s => s.stack) = some [Int.ofNat (encode 0 1)] :=
  transfer_stack_zero

example : run 24 (start 0 0) = none :=
  transfer_halts_zero

example :
    (run 22 (start 0 0)).map (fun s => (s.stack, s.pc)) = some ([Int.ofNat (encode 0 1)], (0, 1)) :=
  decz_jump_entry

example :
    (run 39 (start 1 0)).map (fun s => s.stack)
      = (CMInstr.run transferProgram 3 (startCM 1 0)).map
          (fun s => [Int.ofNat (encode s.c1 s.c2)]) :=
  transfer_simulation

end LeanFunge.Tests
