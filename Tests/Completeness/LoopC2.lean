/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanFunge.Theory.Completeness.LoopC2

/-!
# Counter-2 Loop Simulation Tests
-/

namespace LeanFunge.Tests

open LeanFunge.Completeness

example : CMInstr.run loop2Program 10 (CMInstr.startCM 0 3) = some { pc := 3, c1 := 3, c2 := 0 } :=
  loop2_program_end

example : CMInstr.run loop2Program 11 (CMInstr.startCM 0 3) = none :=
  loop2_program_halts

example : (run 127 (loop2Start 0 3)).map (fun s => s.stack) = some [Int.ofNat (encode 3 0)] :=
  loop2_stack

example : run 128 (loop2Start 0 3) = none :=
  loop2_halts

example :
    (run 38 (loop2Start 0 3)).map (fun s => (s.stack, s.pc)) = some ([Int.ofNat (encode 1 2)], (0, 3)) :=
  loop2_back_jump

example :
    (run 127 (loop2Start 0 3)).map (fun s => s.stack)
      = (CMInstr.run loop2Program 10 (CMInstr.startCM 0 3)).map
          (fun s => [Int.ofNat (encode s.c1 s.c2)]) :=
  loop2_simulation

end LeanFunge.Tests
