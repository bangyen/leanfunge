/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanFunge.Theory.Completeness.LayoutBlock

/-!
# Generated Block Execution Tests
-/

namespace LeanFunge.Tests

open LeanFunge
open LeanFunge.Completeness

/-- The first `inc` block of the generated transfer playfield multiplies the
    stack top by 3 and exits down its fall-through column. -/
example :
    ((run 4 { State.init (playfieldOf layoutProgram) with
        stack := [Int.ofNat 5], pc := (0, 4) }).map (fun s => (s.stack, s.pc)))
      = some ([Int.ofNat 15], (3, 5)) := by
  let S : State (playfieldWidth layoutProgram) (playfieldHeight layoutProgram) :=
    { State.init (playfieldOf layoutProgram) with stack := [Int.ofNat 5], pc := (0, 4) }
  change ((run 4 S).map (fun s => (s.stack, s.pc))) = some ([Int.ofNat 15], (3, 5))
  have h := incBlock_run layoutProgram 0 (by decide)
      (show layoutProgram.getD 0 .halt = .inc 1 by decide) S rfl rfl rfl rfl rfl
  simp [h, counterVal, Option.map]
  decide

/-- The `jump` block of a generated playfield sends the pointer up its
    corridor column. -/
example :
    ((run 2 { State.init (playfieldOf ([.jump 0, .halt] : CMProgram)) with
        stack := [Int.ofNat 5], pc := (0, 2) }).map (fun s => (s.pc, s.dir)))
      = some ((1, 1), .up) := by
  let S : State (playfieldWidth ([.jump 0, .halt] : CMProgram)) (playfieldHeight ([.jump 0, .halt] : CMProgram)) :=
    { State.init (playfieldOf ([.jump 0, .halt] : CMProgram)) with stack := [Int.ofNat 5], pc := (0, 2) }
  change ((run 2 S).map (fun s => (s.pc, s.dir))) = some ((1, 1), .up)
  have h := jumpBlock_run ([.jump 0, .halt] : CMProgram) 0 (by decide)
      (show ([.jump 0, .halt] : CMProgram).getD 0 .halt = .jump 0 by decide) S rfl rfl rfl rfl
  simp [h, Option.map]
  decide

end LeanFunge.Tests
