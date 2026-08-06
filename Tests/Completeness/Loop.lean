/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanFunge.Theory.Completeness.Loop

/-!
# Looping Simulation Tests
-/

namespace LeanFunge.Tests

open LeanFunge.Completeness

example : CMInstr.run loopProgram 10 (CMInstr.startCM 3 0) = some { pc := 3, c1 := 0, c2 := 3 } :=
  loop_program_end

example : CMInstr.run loopProgram 11 (CMInstr.startCM 3 0) = none :=
  loop_program_halts

example : (run 127 (loopStart 3 0)).map (fun s => s.stack) = some [Int.ofNat (encode 0 3)] :=
  loop_stack

example : run 128 (loopStart 3 0) = none :=
  loop_halts

example :
    (run 38 (loopStart 3 0)).map (fun s => (s.stack, s.pc)) = some ([Int.ofNat (encode 2 1)], (0, 3)) :=
  loop_back_jump

example (s : State 12 10)
    (hpc : s.pc = (0, 9)) (hsm : s.stringMode = false)
    (hgrid : s.grid = loopGrid) :
    run 18 s = some { s with pc := (0, 3), dir := .down } :=
  loop_routing_back s hpc hsm hgrid

example :
    (run 127 (loopStart 3 0)).map (fun s => s.stack)
      = (CMInstr.run loopProgram 10 (CMInstr.startCM 3 0)).map
          (fun s => [Int.ofNat (encode s.c1 s.c2)]) :=
  loop_simulation

end LeanFunge.Tests
