/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanFunge.Core.Semantics
import LeanFunge.Theory.Direction
import LeanFunge.Theory.Run.Relational
import LeanFunge.Theory.Step
import Mathlib.Data.Nat.Notation

/-!
# String-Mode Block Semantics

Between two `"` cells the interpreter is in string mode: every character is
pushed as its code and nothing else happens. This module proves the run-level
semantics of such a block. `run_string` moves the pointer through `n` non-quote
cells pushing their codes, and `run_string_block` composes the opening quote,
the string run, and the closing quote into the full block transition.

Printing the pushed codes with `,` recovers the block's characters. `run_print`
pops `n` codes and appends their characters, and `run_string_block_print`
composes the string block with the print run so the output round-trips: the
string block's characters come back out (in reverse order, as the codes are
popped most recent first).

## Main definitions

* `StringRun`: All cells on a straight path of `n` steps are not the string
  toggle `"`.
* `stringCodes`: The character codes pushed by a string run, in traversal
  order.
* `PrintRun`: All cells on a straight path of `n` steps to the right are the
  print-char `,`.

## Theorems

* `step_string_general`: In string mode, a non-quote cell pushes its code and
  advances the pointer.
* `run_string`: A string-mode run of `n` steps over non-quote cells pushes the
  `n` codes and moves the pointer by `runPos`.
* `run_string_block`: An opening `"`, a string run, and a closing `"` push the
  block's codes, leave string mode, and land the pointer past the closing
  quote.
* `step_printChar_general`: A `,` cell outside string mode pops the top value
  and prints its character.
* `run_print`: A run of `n` `,` cells pops `n` codes and appends their
  characters to the output.
* `run_string_block_print`: A string block followed by `n` print cells outputs
  the block's characters in reverse, restoring the stack.
-/

namespace LeanFunge

/-- The characters on the straight path of `n` steps in direction `d` from the
    reduced position are not the string-mode toggle `"`. -/
def StringRun (g : Grid w h) (d : Direction) (x y n : ℕ) : Prop :=
  ∀ k : ℕ, k < n → g.get (runPos w h k d (x % w, y % h)).1 (runPos w h k d (x % w, y % h)).2 ≠ '"'

/-- The character codes pushed by a string-mode run of `n` steps, in traversal
    order. -/
def stringCodes (g : Grid w h) (d : Direction) (x y n : ℕ) : List Int :=
  (List.range n).map (fun k =>
    Int.ofNat (g.get (runPos w h k d (x % w, y % h)).1 (runPos w h k d (x % w, y % h)).2).toNat)

/-- The cells on the straight path of `n` steps to the right are the
    print-char `,`. -/
def PrintRun (g : Grid w h) (x y n : ℕ) : Prop :=
  ∀ k : ℕ, k < n → g.get (runPos w h k Direction.right (x % w, y % h)).1
    (runPos w h k Direction.right (x % w, y % h)).2 = ','

/-- In string mode, a step at a non-quote cell pushes the character code and
    advances the pointer. -/
theorem step_string_general (s : State w h) (hsm : s.stringMode = true)
    (hcell : s.grid.get s.pc.1 s.pc.2 ≠ '"') :
    step s = some { s with
      stack := Stack.push s.stack (Int.ofNat (s.grid.get s.pc.1 s.pc.2).toNat),
      pc := stepPos w h s.dir s.pc } := by
  unfold step
  have hq : ((s.grid.get s.pc.1 s.pc.2).toNat == '"'.toNat) = false := by
    by_cases h : (s.grid.get s.pc.1 s.pc.2).toNat = '"'.toNat
    · exfalso
      apply hcell
      unfold Char.toNat at h
      exact Char.ext (UInt32.toNat_inj.mp h)
    · simpa [h] -- no_squeeze: string
  simp only [stepString, Stack.push, hq, hsm]

/-- A string-mode run of `n` steps over non-quote cells pushes the `n` codes
    (most recent on top) and moves the pointer by `runPos`, preserving the rest
    of the state. -/
theorem run_string (x y n : ℕ) (s : State w h)
    (hpc : s.pc = (x % w, y % h))
    (hsm : s.stringMode = true)
    (hstr : StringRun s.grid s.dir x y n) :
    run n s = some { s with
      stack := List.reverse (stringCodes s.grid s.dir x y n) ++ s.stack,
      pc := runPos w h n s.dir (x % w, y % h) } := by
  induction n with
  | zero =>
      rw [run]
      congr 1
      simp [stringCodes, runPos] -- no_squeeze: string
      rw [← hpc]
  | succ n ih =>
      have hrun : run n s = some { s with
          stack := List.reverse (stringCodes s.grid s.dir x y n) ++ s.stack,
          pc := runPos w h n s.dir (x % w, y % h) } :=
        ih (fun k hk => hstr k (Nat.lt_trans hk (Nat.lt_succ_self n)))
      rw [show run (n + 1) s = (run n s).bind step by rfl]
      rw [hrun]
      let mid : State w h := { s with
        stack := List.reverse (stringCodes s.grid s.dir x y n) ++ s.stack,
        pc := runPos w h n s.dir (x % w, y % h) }
      change step mid = some { s with
        stack := List.reverse (stringCodes s.grid s.dir x y (n + 1)) ++ s.stack,
        pc := runPos w h (n + 1) s.dir (x % w, y % h) }
      have hcell : mid.grid.get mid.pc.1 mid.pc.2 ≠ '"' := by
        simp [mid] -- no_squeeze: string
        exact hstr n (Nat.lt_succ_self n)
      have hstep : step mid = some { mid with
          stack := Stack.push mid.stack (Int.ofNat (mid.grid.get mid.pc.1 mid.pc.2).toNat),
          pc := stepPos w h mid.dir mid.pc } := by
        exact step_string_general mid (by simpa [mid] using hsm) hcell -- no_squeeze: string
      rw [hstep]
      congr 1
      simp [mid, stringCodes, Stack.push, List.range_succ, List.reverse_append, runPos] -- no_squeeze: string

/-- An opening `"`, a string run over `n` non-quote cells, and a closing `"`
    push the block's codes, return to non-string mode, and land the pointer
    past the closing quote. -/
theorem run_string_block (x y n : ℕ) (s : State w h)
    (hpc : s.pc = (x % w, y % h))
    (hm : s.stringMode = false)
    (hdir : s.dir = Direction.right)
    (henter : s.grid.get (x % w) (y % h) = '"')
    (hstr : StringRun s.grid Direction.right (x + 1) y n)
    (hexit : s.grid.get (runPos w h n Direction.right ((x + 1) % w, y % h)).1
        (runPos w h n Direction.right ((x + 1) % w, y % h)).2 = '"') :
    run (n + 2) s = some { s with
      stack := List.reverse (stringCodes s.grid Direction.right (x + 1) y n) ++ s.stack,
      pc := stepPos w h Direction.right
        (runPos w h n Direction.right ((x + 1) % w, y % h)) } := by
  have h1 : run 1 s = some { s with
      stringMode := true, pc := stepPos w h Direction.right (x % w, y % h) } := by
    rw [run, run]
    change step s = some { s with stringMode := true, pc := stepPos w h Direction.right (x % w, y % h) }
    rw [step_string_enter s hm (by simpa [hpc] using henter)] -- no_squeeze: string
    simp [hpc, hdir] -- no_squeeze: string
  let s₁ : State w h := { s with
    stringMode := true, pc := stepPos w h Direction.right (x % w, y % h) }
  have hpc₁ : s₁.pc = ((x + 1) % w, y % h) := by
    simp [s₁] -- no_squeeze: string
    have hrun := runPos_right w h 1 x y
    simpa [runPos] using hrun -- no_squeeze: string
  have hstr₁ : StringRun s₁.grid s₁.dir (x + 1) y n := by
    simpa [s₁, hdir] using hstr -- no_squeeze: string
  have hsm₁ : s₁.stringMode = true := by simp [s₁] -- no_squeeze: string
  have hn : run n s₁ = some { s₁ with
      stack := List.reverse (stringCodes s₁.grid s₁.dir (x + 1) y n) ++ s₁.stack,
      pc := runPos w h n s₁.dir ((x + 1) % w, y % h) } :=
    run_string (x + 1) y n s₁ hpc₁ hsm₁ hstr₁
  let s₂ : State w h := { s with
    stack := List.reverse (stringCodes s.grid Direction.right (x + 1) y n) ++ s.stack,
    stringMode := true, pc := runPos w h n Direction.right ((x + 1) % w, y % h) }
  have hs₂ : { s₁ with
      stack := List.reverse (stringCodes s₁.grid s₁.dir (x + 1) y n) ++ s₁.stack,
      pc := runPos w h n s₁.dir ((x + 1) % w, y % h) } = s₂ := by
    simp [s₁, s₂, hdir] -- no_squeeze: string
  have h2 : run n s₁ = some s₂ := by
    rw [hn, hs₂]
  have hexit₁ : s₂.grid.get s₂.pc.1 s₂.pc.2 = '"' := by
    simp [s₂] -- no_squeeze: string
    exact hexit
  have hsm₂ : s₂.stringMode = true := by simp [s₂] -- no_squeeze: string
  have h3 : run 1 s₂ = some { s₂ with stringMode := false, pc := stepPos w h Direction.right s₂.pc } := by
    rw [run, run]
    change step s₂ = some { s₂ with stringMode := false, pc := stepPos w h Direction.right s₂.pc }
    rw [step_string_exit s₂ hsm₂ hexit₁]
    simp [s₂, hdir] -- no_squeeze: string
  have h12 := run_append s { s with stringMode := true, pc := stepPos w h Direction.right (x % w, y % h) }
    (some s₂) 1 n h1 (by
      simpa [s₁] using h2) -- no_squeeze: string
  let s₃ : State w h := { s with
    stack := List.reverse (stringCodes s.grid Direction.right (x + 1) y n) ++ s.stack,
    pc := stepPos w h Direction.right (runPos w h n Direction.right ((x + 1) % w, y % h)) }
  have h3' : run 1 s₂ = some s₃ := by
    rw [h3]
    congr 1
    simp [s₂, s₃, hm] -- no_squeeze: string
  have h23 := run_append s s₂ (some s₃) (1 + n) 1 h12 h3'
  have hlen : 1 + n + 1 = n + 2 := by omega
  have hfinal : run (n + 2) s = some s₃ := by
    simpa [hlen] using h23 -- no_squeeze: string
  simpa [s₃, hm] using hfinal -- no_squeeze: string

/-- `String.ofList` distributes over a cons: `String.ofList (c :: l)` is the
    single character `c` followed by `l`. -/
theorem String_ofList_cons (c : Char) (l : List Char) :
    String.ofList (c :: l) = String.singleton c ++ String.ofList l := by
  rw [show String.singleton c = String.ofList [c] by rfl]
  rw [← String.ofList_append]
  rfl

/-- Appending a pushed character before a string is the same as printing the
    character then the rest. -/
theorem push_ofList_cons (s : String) (c : Char) (l : List Char) :
    s.push c ++ String.ofList l = s ++ String.ofList (c :: l) := by
  calc
    s.push c ++ String.ofList l = (s ++ String.singleton c) ++ String.ofList l := by
      exact congrArg (fun x : String => x ++ String.ofList l) (String.push_eq_append c)
    _ = s ++ (String.singleton c ++ String.ofList l) := by
      simp only [String.append_assoc]
    _ = s ++ String.ofList (c :: l) := by
      rw [String_ofList_cons]

/-- A step at a `,` cell outside string mode pops the top value and prints its
    character. -/
theorem step_printChar_general (s : State w h) (hm : s.stringMode = false)
    (hcell : s.grid.get s.pc.1 s.pc.2 = ',') :
    step s = some { s with
      output := s.output.push (Char.ofNat (Int.toNat (Stack.top s.stack))),
      stack := Stack.drop s.stack,
      pc := stepPos w h s.dir s.pc } := by
  unfold step
  have hdec : decodeChar ',' = .printChar := by unfold decodeChar; rfl
  simp only [hdec, stepState, Stack.top, Stack.pop, Stack.drop, hm, hcell]

/-- A run of `n` `,` cells pops `n` codes (in order) and appends their
    characters to the output, restoring the rest of the stack. -/
theorem run_print (cs : List Int) (rest : Stack) (x y n : ℕ) (s : State w h)
    (hpc : s.pc = (x % w, y % h))
    (hm : s.stringMode = false)
    (hdir : s.dir = Direction.right)
    (hlen : cs.length = n)
    (hprint : PrintRun s.grid x y n)
    (hstack : s.stack = cs ++ rest) :
    run n s = some { s with
      output := s.output ++ String.ofList (cs.map (fun v : Int => Char.ofNat (Int.toNat v))),
      stack := rest,
      pc := runPos w h n Direction.right (x % w, y % h) } := by
  induction cs generalizing x y n rest s with
  | nil =>
      rw [← hlen]
      simp [run, runPos] -- no_squeeze: string
      have hrest : rest = s.stack := by
        rw [hstack]
        simp -- no_squeeze: string
      subst rest
      rw [hpc.symm]
  | cons c cs' ih =>
      have htop : Stack.top s.stack = c := by
        rw [hstack]
        rfl
      have hdrop : Stack.drop s.stack = cs' ++ rest := by
        rw [hstack]
        rfl
      have hcell : s.grid.get (x % w) (y % h) = ',' := by
        have h0 : 0 < n := by
          rw [← hlen]
          simp -- no_squeeze: string
        exact hprint 0 h0
      have hstep : step s = some { s with
          output := s.output.push (Char.ofNat (Int.toNat c)),
          stack := cs' ++ rest,
          pc := stepPos w h Direction.right s.pc } := by
        rw [hdir]
        rw [step_printChar_general s hm (by simpa [hpc] using hcell)] -- no_squeeze: string
        simp [htop, hdrop, hdir] -- no_squeeze: string
      let s₁ : State w h := { s with
        output := s.output ++ String.singleton (Char.ofNat (Int.toNat c)),
        stack := cs' ++ rest,
        pc := runPos w h 1 Direction.right (x % w, y % h) }
      have h1 : run 1 s = some s₁ := by
        rw [run, run]
        change step s = some s₁
        rw [hstep]
        simp [s₁, hpc, runPos] -- no_squeeze: string
      have hpc₁ : s₁.pc = ((x + 1) % w, y % h) := by
        simp [s₁] -- no_squeeze: string
        have hrun := runPos_right w h 1 x y
        simpa [runPos] using hrun -- no_squeeze: string
      have hsm₁ : s₁.stringMode = false := by simp [s₁, hm] -- no_squeeze: string
      have hprint₁ : PrintRun s₁.grid (x + 1) y cs'.length := by
        intro k hk
        have hk' : k + 1 < n := by
          rw [← hlen]
          simp -- no_squeeze: string
          omega
        have hpath := hprint (k + 1) hk'
        have hpos : runPos w h (k + 1) Direction.right (x % w, y % h) =
            runPos w h k Direction.right ((x + 1) % w, y % h) := by
          rw [runPos_right w h (k + 1) x y]
          rw [runPos_right w h k (x + 1) y]
          simp [Nat.add_comm, Nat.add_left_comm] -- no_squeeze: string
        simpa [s₁, hpos] using hpath -- no_squeeze: string
      let s₂ : State w h := { s₁ with
        output := s₁.output ++ String.ofList (cs'.map (fun v : Int => Char.ofNat (Int.toNat v))),
        stack := rest,
        pc := runPos w h cs'.length Direction.right ((x + 1) % w, y % h) }
      have hrun' : run cs'.length s₁ = some s₂ := by
        exact ih rest (x + 1) y cs'.length s₁ hpc₁ hsm₁ (by simp [s₁, hdir]) rfl hprint₁ rfl -- no_squeeze: string
      have hn : n = 1 + cs'.length := by
        rw [← hlen]
        simp [Nat.add_comm] -- no_squeeze: string
      have htotal := run_append s s₁ (some s₂) 1 cs'.length h1 hrun'
      rw [hn]
      rw [htotal]
      congr 1
      simp [s₂, s₁, runPos_right, List.map_cons, push_ofList_cons,
        Nat.add_comm, Nat.add_left_comm] -- no_squeeze: print composition

/-- A string block followed by `n` print cells outputs the block's characters
    in reverse (the codes are popped most recent first), restoring the stack
    and landing the pointer after the prints. -/
theorem run_string_block_print (x y n : ℕ) (s : State w h)
    (hpc : s.pc = (x % w, y % h))
    (hm : s.stringMode = false)
    (hdir : s.dir = Direction.right)
    (henter : s.grid.get (x % w) (y % h) = '"')
    (hstr : StringRun s.grid Direction.right (x + 1) y n)
    (hexit : s.grid.get (runPos w h n Direction.right ((x + 1) % w, y % h)).1
        (runPos w h n Direction.right ((x + 1) % w, y % h)).2 = '"')
    (hprint : PrintRun s.grid (x + n + 2) y n) :
    run (2 * n + 2) s = some { s with
      output := s.output ++ String.ofList ((stringCodes s.grid Direction.right (x + 1) y n).map
        (fun v : Int => Char.ofNat (Int.toNat v))).reverse,
      stack := s.stack,
      pc := runPos w h (2 * n + 2) Direction.right (x % w, y % h) } := by
  let codes : List Int := stringCodes s.grid Direction.right (x + 1) y n
  let s₀ : State w h := { s with
    stack := List.reverse codes ++ s.stack,
    pc := stepPos w h Direction.right (runPos w h n Direction.right ((x + 1) % w, y % h)) }
  have hblock : run (n + 2) s = some s₀ := by
    have h := run_string_block x y n s hpc hm hdir henter hstr hexit
    simpa [s₀, codes] using h -- no_squeeze: string
  have hpc₀ : s₀.pc = ((x + n + 2) % w, y % h) := by
    simp [s₀] -- no_squeeze: string
    rw [runPos_right w h n (x + 1) y]
    rw [show stepPos w h Direction.right ((x + 1 + n) % w, y % h) =
        runPos w h 1 Direction.right ((x + 1 + n) % w, y % h) by
          rw [runPos]
          rfl]
    rw [runPos_right w h 1 (x + 1 + n) y]
    have hx : x + 1 + n + 1 = x + n + 2 := by omega
    rw [hx]
  have hsm₀ : s₀.stringMode = false := by simp [s₀, hm] -- no_squeeze: string
  have hdir₀ : s₀.dir = Direction.right := by simp [s₀, hdir] -- no_squeeze: string
  have hlen : (List.reverse codes).length = n := by
    simp [codes, stringCodes, List.length_map, List.length_reverse, List.length_range] -- no_squeeze: string
  have hp := run_print (List.reverse codes) s.stack (x + n + 2) y n s₀ hpc₀ hsm₀ hdir₀ hlen hprint rfl
  let s₂ : State w h := { s with
    output := s.output ++ String.ofList (codes.map (fun v : Int => Char.ofNat (Int.toNat v))).reverse,
    stack := s.stack,
    pc := runPos w h (2 * n + 2) Direction.right (x % w, y % h) }
  have hprintrun : run n s₀ = some s₂ := by
    have hpc_eq : runPos w h n Direction.right ((x + n + 2) % w, y % h) =
        runPos w h (2 * n + 2) Direction.right (x % w, y % h) := by
      rw [runPos_right w h n (x + n + 2) y]
      rw [runPos_right w h (2 * n + 2) x y]
      have hx : x + n + 2 + n = x + (2 * n + 2) := by omega
      rw [hx]
    have h : { s₀ with
        output := s₀.output ++ String.ofList ((List.reverse codes).map (fun v : Int => Char.ofNat (Int.toNat v))),
        stack := s.stack,
        pc := runPos w h n Direction.right ((x + n + 2) % w, y % h) } = s₂ := by
      simp [s₂, s₀, List.map_reverse, hpc_eq] -- no_squeeze: string
    rw [hp, h]
  have hsum : (n + 2) + n = 2 * n + 2 := by omega
  have htotal := run_append s s₀ (some s₂) (n + 2) n hblock hprintrun
  simpa [hsum, s₂] using htotal -- no_squeeze: string

end LeanFunge
