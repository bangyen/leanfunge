/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanFunge.Theory.Completeness.LayoutDecz

/-!
# Generated `decz` Block Execution Tests
-/

namespace LeanFunge.Tests

open LeanFunge
open LeanFunge.Completeness

/-- The `decz` test cells of the generated transfer playfield leave the
    remainder on top of the encoded pair at the branch cell. -/
example :
    ((run 4 { State.init (playfieldOf layoutProgram) with
        stack := [Int.ofNat 8], pc := (3, 6) }).map (fun s => (s.stack, s.pc)))
      = some ([Int.ofNat 0, Int.ofNat 8], (7, 6)) := by
  let S : State (playfieldWidth layoutProgram) (playfieldHeight layoutProgram) :=
    { State.init (playfieldOf layoutProgram) with stack := [Int.ofNat 8], pc := (3, 6) }
  change ((run 4 S).map (fun s => (s.stack, s.pc))) = some ([Int.ofNat 0, Int.ofNat 8], (7, 6))
  have h := deczBlock_prefix layoutProgram 1 (by decide)
      (show layoutProgram.getD 1 .halt = .decz 0 3 by decide) S rfl rfl rfl rfl rfl
  simp only [h, counterVal, Option.map]
  decide

end LeanFunge.Tests
