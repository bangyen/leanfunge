/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanFunge.Theory.Completeness.LayoutRouting
import LeanFunge.Theory.Completeness.LayoutRouting

/-!
# Corridor Routing Foundation Tests
-/

namespace LeanFunge.Tests

open LeanFunge
open LeanFunge.Completeness

/-- A drop down the fall-through column reaches the next entry. -/
example :
    ((run 1 { State.init (playfieldOf layoutProgram) with
        pc := (4, 5), dir := .down }).map (fun s => s.pc))
      = some (4, 6) := by
  let S : State (playfieldWidth layoutProgram) (playfieldHeight layoutProgram) :=
    { State.init (playfieldOf layoutProgram) with pc := (4, 5), dir := .down }
  change ((run 1 S).map (fun s => s.pc)) = some (4, 6)
  have h := fallthrough_drop layoutProgram 0 (by decide) S rfl rfl rfl rfl
  simp only [h, Option.map]
  decide

end LeanFunge.Tests
