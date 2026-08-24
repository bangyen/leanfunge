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

example {w h : ℕ} (hw : 2 ≤ w) (s : State w h) (y : ℕ)
    (hm : s.stringMode = false) (hcell : s.grid.get s.pc.1 s.pc.2 = '#')
    (hpc : s.pc = (w - 1, y)) (hdir : s.dir = .right) :
    step s = some { s with pc := (1, y % h) } :=
  step_trampoline_right_from_last hw s y hm hcell hpc hdir

example {w h : ℕ} (hw : 2 ≤ w) (s : State w h) (y : ℕ)
    (hm : s.stringMode = false) (hcell : s.grid.get s.pc.1 s.pc.2 = '#')
    (hpc : s.pc = (0, y)) (hdir : s.dir = .left) :
    step s = some { s with pc := (w - 2, y % h) } :=
  step_trampoline_left_from_first hw s y hm hcell hpc hdir

example {w h : ℕ} (hh : 2 ≤ h) (s : State w h) (x : ℕ)
    (hm : s.stringMode = false) (hcell : s.grid.get s.pc.1 s.pc.2 = '#')
    (hpc : s.pc = (x, h - 1)) (hdir : s.dir = .down) :
    step s = some { s with pc := (x % w, 1) } :=
  step_trampoline_down_from_last hh s x hm hcell hpc hdir

example {w h : ℕ} (hh : 2 ≤ h) (s : State w h) (x : ℕ)
    (hm : s.stringMode = false) (hcell : s.grid.get s.pc.1 s.pc.2 = '#')
    (hpc : s.pc = (x, 0)) (hdir : s.dir = .up) :
    step s = some { s with pc := (x % w, h - 2) } :=
  step_trampoline_up_from_first hh s x hm hcell hpc hdir

example {w h : ℕ} (s : State w h) (hm : s.stringMode = false)
    (hcell : s.grid.get s.pc.1 s.pc.2 = '/') (b : Int) (rest : Stack)
    (hstack : s.stack = 0 :: b :: rest) :
    step s = some { s with stack := 0 :: rest, pc := stepPos w h s.dir s.pc } :=
  step_div_zero s hm hcell b rest hstack

example {w h : ℕ} (s : State w h) (hm : s.stringMode = false)
    (hcell : s.grid.get s.pc.1 s.pc.2 = '%') (b : Int) (rest : Stack)
    (hstack : s.stack = 0 :: b :: rest) :
    step s = some { s with stack := b :: rest, pc := stepPos w h s.dir s.pc } :=
  step_mod_zero s hm hcell b rest hstack

end LeanFunge.Tests
