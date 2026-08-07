/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanFunge.Theory.Completeness.LayoutJump

/-!
# Generated Jump Corridor Tests
-/

namespace LeanFunge.Tests

open LeanFunge.Completeness

example : run 24 (jumpStart 0 0) = none :=
  transfer_jump_halts

example : (run 23 (jumpStart 0 0)).map (fun s => s.stack) = some [Int.ofNat (encode 0 1)] :=
  transfer_jump_stack

example : run 22 (jumpStart 1 0) = none :=
  transfer_fall_halts

example : (run 21 (jumpStart 1 0)).map (fun s => s.stack) = some [Int.ofNat (encode 1 1)] :=
  transfer_fall_stack

example :
    (run 23 (jumpStart 0 0)).map (fun s => s.stack)
      = (CMInstr.run layoutProgram 2 (CMInstr.startCM 0 0)).map
          (fun s => [Int.ofNat (encode s.c1 s.c2)]) :=
  transfer_simulation_jump

end LeanFunge.Tests
