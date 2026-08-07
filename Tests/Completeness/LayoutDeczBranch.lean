/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanFunge.Theory.Completeness.LayoutBlock

/-!
# Generated `decz` Branch Execution Tests
-/

namespace LeanFunge.Tests

open LeanFunge
open LeanFunge.Completeness

/-- On an even encoding the `decz` block divides the value and exits down. -/
example :
    ((run 5 { State.init (playfieldOf layoutProgram) with
        stack := [Int.ofNat 0, Int.ofNat 8], pc := (7, 6) }).map (fun s => (s.stack, s.pc)))
      = some ([Int.ofNat 4], (8, 10)) := by
  let S : State (playfieldWidth layoutProgram) (playfieldHeight layoutProgram) :=
    { State.init (playfieldOf layoutProgram) with stack := [Int.ofNat 0, Int.ofNat 8], pc := (7, 6) }
  change ((run 5 S).map (fun s => (s.stack, s.pc))) = some ([Int.ofNat 4], (8, 10))
  have h := deczBlock_decrement (prog := layoutProgram) (i := 1) (hi1 := by decide)
      (hdecz := (show layoutProgram.getD 1 .halt = .decz 0 3 by decide))
      (n := Int.ofNat 8) (s := S) (hsm := rfl) (hpc := rfl)
      (hstack := by decide) (hgrid := rfl) (hz := by decide)
  simp only [h, counterVal, Option.map]
  decide

/-- On an odd encoding the `decz` block sends the pointer up the corridor
    column. -/
example :
    ((run 1 { State.init (playfieldOf layoutProgram) with
        stack := [Int.ofNat 1, Int.ofNat 3], pc := (7, 6) }).map (fun s => (s.pc, s.dir)))
      = some ((7, 5), .up) := by
  let S : State (playfieldWidth layoutProgram) (playfieldHeight layoutProgram) :=
    { State.init (playfieldOf layoutProgram) with stack := [Int.ofNat 1, Int.ofNat 3], pc := (7, 6) }
  change ((run 1 S).map (fun s => (s.pc, s.dir))) = some ((7, 5), .up)
  have h := deczBlock_jump (prog := layoutProgram) (i := 1) (hi1 := by decide)
      (hdecz := (show layoutProgram.getD 1 .halt = .decz 0 3 by decide))
      (n := Int.ofNat 3) (s := S) (hsm := rfl) (hpc := rfl)
      (hstack := by decide) (hgrid := rfl) (hnz := by decide)
  simp only [h, counterVal, Option.map]
  decide

end LeanFunge.Tests
