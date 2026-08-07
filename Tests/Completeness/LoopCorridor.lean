/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanFunge.Theory.Completeness.LoopCorridor

/-!
# Generated Loop Corridor Tests
-/

namespace LeanFunge.Tests

open LeanFunge.Completeness

example :
    (run 36 (loopCorridorStart 3 0)).map (fun s => s.stack) = some [Int.ofNat (encode 2 1)] :=
  loop_corridor_back

example : run 137 (loopCorridorStart 3 0) = none :=
  loop_corridor_halts

example :
    (run 136 (loopCorridorStart 3 0)).map (fun s => s.stack) = some [Int.ofNat (encode 0 3)] :=
  loop_corridor_stack

example :
    (run 136 (loopCorridorStart 3 0)).map (fun s => s.stack)
      = (CMInstr.run loopProgram 10 (CMInstr.startCM 3 0)).map
          (fun s => [Int.ofNat (encode s.c1 s.c2)]) :=
  loop_corridor_simulation

end LeanFunge.Tests
