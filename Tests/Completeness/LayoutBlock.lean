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
      (show layoutProgram.getD 0 .halt = .inc 1 by decide) S rfl rfl rfl rfl
  simp only [h, counterVal, Option.map]
  decide

end LeanFunge.Tests
