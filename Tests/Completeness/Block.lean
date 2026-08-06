/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanFunge.Theory.Completeness.Block
import LeanFunge.Theory.Completeness.BlockC2

/-!
# `decz` Block Snippet Tests
-/

namespace LeanFunge.Tests

open LeanFunge.Completeness

example (s : State w h) (p : ℕ) (n : Int)
    (hsm : s.stringMode = false) (hdir : s.dir = Direction.right)
    (hpc : s.pc = (p, 0)) (hno : p + 3 < w)
    (hstack : s.stack = [n])
    (hc1 : s.grid.get p 0 = ':') (hc2 : s.grid.get (p + 1) 0 = '2')
    (hc3 : s.grid.get (p + 2) 0 = '%') (hc4 : s.grid.get (p + 3) 0 = '|')
    (hn : n % 2 = 0) :
    run 4 s = some { s with
      dir := Direction.down,
      stack := [n], pc := stepPos w h Direction.down (p + 3, 0) } :=
  decz_test_c1_even s p n hsm hdir hpc hno hstack hc1 hc2 hc3 hc4 hn

example (s : State w h) (p : ℕ) (n : Int)
    (hsm : s.stringMode = false) (hdir : s.dir = Direction.right)
    (hpc : s.pc = (p, 0)) (hno : p + 3 < w)
    (hstack : s.stack = [n])
    (hc1 : s.grid.get p 0 = ':') (hc2 : s.grid.get (p + 1) 0 = '2')
    (hc3 : s.grid.get (p + 2) 0 = '%') (hc4 : s.grid.get (p + 3) 0 = '|')
    (hn : n % 2 ≠ 0) :
    run 4 s = some { s with
      dir := Direction.up,
      stack := [n], pc := stepPos w h Direction.up (p + 3, 0) } :=
  decz_test_c1_odd s p n hsm hdir hpc hno hstack hc1 hc2 hc3 hc4 hn

example (s : State w h) (p : ℕ) (n : Int)
    (hsm : s.stringMode = false) (hdir : s.dir = Direction.right)
    (hpc : s.pc = (p, 0)) (hno : p + 2 < w)
    (hstack : s.stack = [n])
    (hc1 : s.grid.get p 0 = '2') (hc2 : s.grid.get (p + 1) 0 = '/') :
    run 2 s = some { s with stack := [n / 2], pc := (p + 2, 0) } :=
  decz_dec_c1 s p n hsm hdir hpc hno hstack hc1 hc2

example (s : State w h) (p : ℕ) (n : Int)
    (hsm : s.stringMode = false) (hdir : s.dir = Direction.right)
    (hpc : s.pc = (p, 0)) (hno : p + 3 < w)
    (hstack : s.stack = [n])
    (hc1 : s.grid.get p 0 = ':') (hc2 : s.grid.get (p + 1) 0 = '3')
    (hc3 : s.grid.get (p + 2) 0 = '%') (hc4 : s.grid.get (p + 3) 0 = '|')
    (hn : n % 3 = 0) :
    run 4 s = some { s with
      dir := Direction.down,
      stack := [n], pc := stepPos w h Direction.down (p + 3, 0) } :=
  decz_test_c2_even s p n hsm hdir hpc hno hstack hc1 hc2 hc3 hc4 hn

example (s : State w h) (p : ℕ) (n : Int)
    (hsm : s.stringMode = false) (hdir : s.dir = Direction.right)
    (hpc : s.pc = (p, 0)) (hno : p + 3 < w)
    (hstack : s.stack = [n])
    (hc1 : s.grid.get p 0 = ':') (hc2 : s.grid.get (p + 1) 0 = '3')
    (hc3 : s.grid.get (p + 2) 0 = '%') (hc4 : s.grid.get (p + 3) 0 = '|')
    (hn : n % 3 ≠ 0) :
    run 4 s = some { s with
      dir := Direction.up,
      stack := [n], pc := stepPos w h Direction.up (p + 3, 0) } :=
  decz_test_c2_odd s p n hsm hdir hpc hno hstack hc1 hc2 hc3 hc4 hn

example (s : State w h) (p : ℕ) (n : Int)
    (hsm : s.stringMode = false) (hdir : s.dir = Direction.right)
    (hpc : s.pc = (p, 0)) (hno : p + 2 < w)
    (hstack : s.stack = [n])
    (hc1 : s.grid.get p 0 = '3') (hc2 : s.grid.get (p + 1) 0 = '/') :
    run 2 s = some { s with stack := [n / 3], pc := (p + 2, 0) } :=
  decz_dec_c2 s p n hsm hdir hpc hno hstack hc1 hc2

end LeanFunge.Tests
