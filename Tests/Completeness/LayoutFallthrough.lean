/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanFunge.Theory.Completeness.LayoutFallthrough

/-!
# Generated Fall-Through Tests
-/

namespace LeanFunge.Tests

open LeanFunge.Completeness

example :
    ((run 6 { State.init (playfieldOf layoutProgram) with
        stack := [Int.ofNat (encode 1 0)], pc := (0, 4) }).map (fun s => (s.stack, s.pc)))
      = some ([Int.ofNat (encode 1 0) * 3], (4, 6)) :=
  layout_transfer_block0

example (s : State (playfieldWidth layoutProgram) (playfieldHeight layoutProgram))
    (hpc : s.pc = (3, 4)) (hsm : s.stringMode = false)
    (hgrid : s.grid = playfieldOf layoutProgram) :
    run 3 s = some { s with dir := .right, pc := (4, 6) } :=
  layout_fallthrough_0 s hpc hsm hgrid

example (s : State (playfieldWidth layoutProgram) (playfieldHeight layoutProgram))
    (hpc : s.pc = (8, 9)) (hsm : s.stringMode = false)
    (hgrid : s.grid = playfieldOf layoutProgram) :
    run 3 s = some { s with dir := .right, pc := (9, 11) } :=
  layout_fallthrough_decz s hpc hsm hgrid

end LeanFunge.Tests
