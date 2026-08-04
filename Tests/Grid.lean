/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanFunge.Theory.Grid

/-!
# Grid Tests
-/

namespace LeanFunge.Tests

open LeanFunge

example (g : Grid w h) (x y : ℕ) (c : Char) :
    Grid.get (Grid.put g x y c) x y = c :=
  Grid.get_put_self g x y c

example (g : Grid w h) (x y : ℕ) (c1 c2 : Char) :
    Grid.put (Grid.put g x y c1) x y c2 = Grid.put g x y c2 :=
  Grid.put_put g x y c1 c2

example (g : Grid w h) (x1 y1 x2 y2 : ℕ) (c : Char)
    (hdist : x1 % w ≠ x2 % w ∨ y1 % h ≠ y2 % h) :
    Grid.get (Grid.put g x2 y2 c) x1 y1 = Grid.get g x1 y1 :=
  Grid.get_put_other g x1 y1 x2 y2 c hdist

example (g : Grid w h) (x y : ℕ) (hx : x < w) :
    (Grid.prependSpace g).get (x + 1) y = g.get x y :=
  Grid.get_prependSpace_succ g x y hx

end LeanFunge.Tests
