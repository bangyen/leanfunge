/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanFunge.Theory.Memory

/-!
# Memory Model Tests
-/

namespace LeanFunge.Tests

open LeanFunge LeanFunge.Examples

example : gridNoPut quineGrid :=
  quine_gridNoPut

example (n : ℕ) (s' : State 45 1) (h : run n quineState = some s') :
    s'.grid = quineGrid :=
  quine_grid_invariant n s' h

example : runWrites 8 selfmodState = [selfmodWrite] :=
  selfmod_runWrites

example (s : State 10 1) (h : run 8 selfmodState = some s) :
    s.grid = Grid.put selfmodGrid 8 0 '@' :=
  selfmod_grid s h

example (s : State 10 1) (h : run 8 selfmodState = some s) (x y : ℕ)
    (hne : x % 10 ≠ 8 % 10 ∨ y % 1 ≠ 0 % 1) :
    s.grid.get x y = selfmodGrid.get x y :=
  selfmod_grid_other s h x y hne

example : runWrites 7 execState = [execWrite] :=
  exec_runWrites

example (s : State 10 1) (h : run 7 execState = some s) :
    s.grid = Grid.put execGrid 7 0 '1' :=
  exec_grid s h

example (s : State 10 1) (h : run 7 execState = some s) (x y : ℕ)
    (hne : x % 10 ≠ 7 % 10 ∨ y % 1 ≠ 0 % 1) :
    s.grid.get x y = execGrid.get x y :=
  exec_grid_other s h x y hne

end LeanFunge.Tests
