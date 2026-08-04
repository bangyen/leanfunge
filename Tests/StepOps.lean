/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanFunge.Theory.StepOps

/-!
# Remaining Step Semantics Tests
-/

namespace LeanFunge.Tests

open LeanFunge

example {w h : ℕ} (s : State w h) (hm : s.stringMode = false)
    (hcell : s.grid.get s.pc.1 s.pc.2 = '/') (a b : Int) (rest : Stack)
    (hstack : s.stack = a :: b :: rest) :
    step s = some { s with stack := (b / a) :: rest, pc := stepPos w h s.dir s.pc } :=
  step_div s hm hcell a b rest hstack

example {w h : ℕ} (s : State w h) (hm : s.stringMode = false)
    (hcell : s.grid.get s.pc.1 s.pc.2 = '%') (a b : Int) (rest : Stack)
    (hstack : s.stack = a :: b :: rest) :
    step s = some { s with stack := (b % a) :: rest, pc := stepPos w h s.dir s.pc } :=
  step_mod s hm hcell a b rest hstack

example {w h : ℕ} (s : State w h) (hm : s.stringMode = false)
    (hcell : s.grid.get s.pc.1 s.pc.2 = '`') (a b : Int) (rest : Stack)
    (hstack : s.stack = a :: b :: rest) :
    step s = some { s with
      stack := (if b > a then 1 else 0) :: rest,
      pc := stepPos w h s.dir s.pc } :=
  step_greater s hm hcell a b rest hstack

example {w h : ℕ} (s : State w h) (hm : s.stringMode = false)
    (hcell : s.grid.get s.pc.1 s.pc.2 = ':') (v : Int) (rest : Stack)
    (hstack : s.stack = v :: rest) :
    step s = some { s with stack := v :: v :: rest, pc := stepPos w h s.dir s.pc } :=
  step_dup s hm hcell v rest hstack

example {w h : ℕ} (s : State w h) (hm : s.stringMode = false)
    (hcell : s.grid.get s.pc.1 s.pc.2 = '\\') (a b : Int) (rest : Stack)
    (hstack : s.stack = a :: b :: rest) :
    step s = some { s with stack := b :: a :: rest, pc := stepPos w h s.dir s.pc } :=
  step_swap s hm hcell a b rest hstack

example {w h : ℕ} (s : State w h) (hm : s.stringMode = false)
    (hcell : s.grid.get s.pc.1 s.pc.2 = '$') (v : Int) (rest : Stack)
    (hstack : s.stack = v :: rest) :
    step s = some { s with stack := rest, pc := stepPos w h s.dir s.pc } :=
  step_drop s hm hcell v rest hstack

example {w h : ℕ} (s : State w h) (hm : s.stringMode = false)
    (hcell : s.grid.get s.pc.1 s.pc.2 = '~') (c : Char) (rest : List Char)
    (hinput : s.input = c :: rest) :
    step s = some { s with
      stack := Stack.push s.stack (Int.ofNat c.toNat),
      input := rest,
      pc := stepPos w h s.dir s.pc } :=
  step_inputChar s hm hcell c rest hinput

example {w h : ℕ} (s : State w h) (hm : s.stringMode = false)
    (hcell : s.grid.get s.pc.1 s.pc.2 = '~') (hinput : s.input = []) :
    step s = some { s with stack := Stack.push s.stack 0, pc := stepPos w h s.dir s.pc } :=
  step_inputChar_eof s hm hcell hinput

example {w h : ℕ} (s : State w h) (hm : s.stringMode = false)
    (hcell : s.grid.get s.pc.1 s.pc.2 = '&') (rest : List Char) (v : Int)
    (hparse : parseInt s.input = (rest, v)) :
    step s = some { s with
      stack := Stack.push s.stack v,
      input := rest,
      pc := stepPos w h s.dir s.pc } :=
  step_inputInt s hm hcell rest v hparse

end LeanFunge.Tests
