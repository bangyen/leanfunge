/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanFunge.Core.Direction
import LeanFunge.Core.Grid
import LeanFunge.Core.Instruction
import LeanFunge.Core.Parser
import LeanFunge.Core.Stack
import LeanFunge.Core.State
import Mathlib.Data.Nat.Notation

/-!
# Semantics

## Main definitions

* `stepString`: The string-mode step.
* `stepState`: The non-string-mode step for a decoded instruction.
* `step`: The single-step transition function.
* `run`: Run the interpreter for finitely many steps.
* `halts`: Whether a program halts.
* `stepRel`: The nondeterministic transition relation.
-/

namespace LeanFunge

/-- The string-mode step: every character is pushed as its code, except `"`,
    which toggles string mode off. -/
def stepString (s : State w h) (ch : Char) : State w h :=
  let pc' := stepPos w h s.dir s.pc
  match ch.toNat == '"'.toNat with
  | true => { s with stringMode := false, pc := pc' }
  | false => { s with stack := Stack.push s.stack (Int.ofNat ch.toNat), pc := pc' }

/-- The non-string-mode step for a decoded instruction. -/
def stepState (s : State w h) (instr : Instruction) : State w h :=
  match instr with
  | .push n => { s with stack := Stack.push s.stack n, pc := stepPos w h s.dir s.pc }
  | .add => { s with stack := Stack.applyBinary (· + ·) s.stack, pc := stepPos w h s.dir s.pc }
  | .sub => { s with stack := Stack.applyBinary (· - ·) s.stack, pc := stepPos w h s.dir s.pc }
  | .mul => { s with stack := Stack.applyBinary (· * ·) s.stack, pc := stepPos w h s.dir s.pc }
  | .div => { s with stack := Stack.applyBinary (· / ·) s.stack, pc := stepPos w h s.dir s.pc }
  | .mod => { s with stack := Stack.applyBinary (· % ·) s.stack, pc := stepPos w h s.dir s.pc }
  | .not =>
      let v := Stack.top s.stack
      { s with
        stack := Stack.push (Stack.drop s.stack) (if v = 0 then 1 else 0),
        pc := stepPos w h s.dir s.pc }
  | .greater =>
      let b := Stack.top s.stack
      let a := Stack.top (Stack.drop s.stack)
      { s with
        stack := Stack.push (Stack.drop (Stack.drop s.stack)) (if a > b then 1 else 0),
        pc := stepPos w h s.dir s.pc }
  | .right => { s with dir := .right, pc := stepPos w h .right s.pc }
  | .left => { s with dir := .left, pc := stepPos w h .left s.pc }
  | .up => { s with dir := .up, pc := stepPos w h .up s.pc }
  | .down => { s with dir := .down, pc := stepPos w h .down s.pc }
  | .chooseH =>
      let v := Stack.top s.stack
      { s with
        dir := Direction.chooseH v,
        stack := Stack.drop s.stack,
        pc := stepPos w h (Direction.chooseH v) s.pc }
  | .chooseV =>
      let v := Stack.top s.stack
      { s with
        dir := Direction.chooseV v,
        stack := Stack.drop s.stack,
        pc := stepPos w h (Direction.chooseV v) s.pc }
  | .random => { s with pc := stepPos w h s.dir s.pc }
  | .stringMode => { s with stringMode := true, pc := stepPos w h s.dir s.pc }
  | .dup => { s with stack := Stack.dup s.stack, pc := stepPos w h s.dir s.pc }
  | .swap => { s with stack := Stack.swap s.stack, pc := stepPos w h s.dir s.pc }
  | .drop => { s with stack := Stack.drop s.stack, pc := stepPos w h s.dir s.pc }
  | .printInt =>
      { s with
        output := s.output ++ toString (Stack.top s.stack),
        stack := Stack.drop s.stack,
        pc := stepPos w h s.dir s.pc }
  | .printChar =>
      { s with
        output := s.output.push (Char.ofNat (Int.toNat (Stack.top s.stack))),
        stack := Stack.drop s.stack,
        pc := stepPos w h s.dir s.pc }
  | .put =>
      let (s1, y) := Stack.pop s.stack
      let (s2, x) := Stack.pop s1
      let (s3, v) := Stack.pop s2
      { s with
        grid := Grid.put s.grid (Int.toNat x) (Int.toNat y) (Char.ofNat (Int.toNat v)),
        stack := s3,
        pc := stepPos w h s.dir s.pc }
  | .get =>
      let (s1, y) := Stack.pop s.stack
      let (s2, x) := Stack.pop s1
      { s with
        stack := Stack.push s2 (Int.ofNat (s.grid.get (Int.toNat x) (Int.toNat y)).toNat),
        pc := stepPos w h s.dir s.pc }
  | .inputInt =>
      let (rest, v) := parseInt s.input
      { s with
        stack := Stack.push s.stack v,
        input := rest,
        pc := stepPos w h s.dir s.pc }
  | .inputChar =>
      match s.input with
      | [] => { s with stack := Stack.push s.stack 0, pc := stepPos w h s.dir s.pc }
      | c :: rest =>
          { s with
            stack := Stack.push s.stack (Int.ofNat c.toNat),
            input := rest,
            pc := stepPos w h s.dir s.pc }
  | .trampoline =>
      let mid := stepPos w h s.dir s.pc
      { s with pc := stepPos w h s.dir mid }
  | .halt => s
  | .nop => { s with pc := stepPos w h s.dir s.pc }

/-- Execute one instruction. Returns `none` when the `@` instruction is
    executed (outside string mode), and `some` the resulting state otherwise. -/
def step (s : State w h) : Option (State w h) :=
  let ch := s.grid.get s.pc.1 s.pc.2
  match (s.stringMode, decodeChar ch) with
  | (true, _) => some (stepString s ch)
  | (false, .halt) => none
  | (false, instr) => some (stepState s instr)

/-- Run the interpreter for `n` steps, threading `none` once the program
    halts. -/
def run (n : ℕ) (s : State w h) : Option (State w h) :=
  match n with
  | 0 => some s
  | n + 1 => (run n s).bind step

/-- A program halts if it reaches `none` after finitely many steps. -/
def halts (s : State w h) : Prop :=
  ∃ n : ℕ, run n s = none

/-- The nondeterministic transition relation: a step is either the
    deterministic one, or — at a `?` outside string mode — any of the four
    directions may be chosen. The deterministic interpreter is a sound
    refinement of this relation (see `LeanFunge.Theory.Random`). -/
def stepRel (s : State w h) (s' : Option (State w h)) : Prop :=
  s' = step s ∨
    (∃ d : Direction, ¬ s.stringMode ∧
      decodeChar (s.grid.get s.pc.1 s.pc.2) = .random ∧
      s' = some { s with dir := d, pc := stepPos w h d s.pc })

end LeanFunge
