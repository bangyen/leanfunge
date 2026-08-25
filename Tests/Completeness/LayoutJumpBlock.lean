/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanFunge.Theory.Completeness.LayoutBlock

/-!
# Generated Jump and Halt Block Execution Tests
-/

namespace LeanFunge.Tests

open LeanFunge
open LeanFunge.Completeness

/-- The `jump` block of a generated playfield sends the pointer up its
    corridor column. -/
example :
    ((run 2 { State.init (playfieldOf ([.jump 0, .halt] : CMProgram)) with
        stack := [Int.ofNat 5], pc := (1, 2) }).map (fun s => (s.pc, s.dir)))
      = some ((2, 1), .up) := by
  let S : State (playfieldWidth ([.jump 0, .halt] : CMProgram))
      (playfieldHeight ([.jump 0, .halt] : CMProgram)) :=
    { State.init (playfieldOf ([.jump 0, .halt] : CMProgram)) with
      stack := [Int.ofNat 5], pc := (1, 2) }
  change ((run 2 S).map (fun s => (s.pc, s.dir))) = some ((2, 1), .up)
  have h := jumpBlock_run ([.jump 0, .halt] : CMProgram) 0 (by decide)
      (show ([.jump 0, .halt] : CMProgram).getD 0 .halt = .jump 0 by decide) S rfl rfl rfl
  simp only [h, Option.map]
  decide

end LeanFunge.Tests
