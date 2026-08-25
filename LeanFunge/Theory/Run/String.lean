/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanFunge.Core.Semantics
import LeanFunge.Theory.Direction
import LeanFunge.Theory.Run.IO
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

String mode also takes precedence over the instruction set: `step_string_mode`
and `run_string_mode` show that while string mode is on, the interpreter never
halts, writes the playfield, consumes input, produces output, or turns — the
cells are data, not code.

Finally, string mode is exactly a parity: `run_stringMode_parity` shows the
mode after a run is the initial mode toggled once per executed `"`. The count
is over cells the pointer *executes*, not cells it passes over — `#` skips a
cell without executing it, and a cell skipped that way is never counted. The
count is also taken against each step's own playfield, so a `"` written by `p`
partway through a run is counted correctly once the pointer reaches it.

## Main definitions

* `StringRun`: All cells on a straight path of `n` steps are not the string
  toggle `"`.
* `stringCodes`: The character codes pushed by a string run, in traversal
  order.
* `PrintRun`: All cells on a straight path of `n` steps to the right are the
  print-char `,`.
* `quoteSteps`: The number of steps of a run whose executed cell is a double
  quote.

## Theorems

* `step_string_general`: In string mode, a non-quote cell pushes its code and
  advances the pointer.
* `run_string`: A string-mode run over non-quote cells pushes each character's
  code and moves the pointer by the position iterate.
* `run_string_block`: An opening `"`, a string run, and a closing `"` push the
  block's codes, leave string mode, and land the pointer past the closing
  quote.
* `String_ofList_cons`: `String.ofList` distributes over a cons.
* `push_ofList_cons`: Appending a pushed character before a string is the same
  as printing the character then the rest.
* `step_printChar_general`: A `,` cell outside string mode pops the top value
  and prints its character.
* `run_print`: A run of `,` cells pops each code and appends its character to
  the output.
* `run_string_block_print`: A string block followed by print cells outputs the
  block's characters in reverse, restoring the stack.
* `step_string_mode`: A string-mode step never halts, writes the playfield,
  consumes input, produces output, or turns.
* `run_string_mode`: A run that stays in string mode throughout leaves the
  playfield, input, output, and direction untouched.
* `decodeChar_stringMode_iff`: A character decodes to the string-mode toggle
  exactly when it is a double quote.
* `step_stringMode_xor`: Every step toggles string mode exactly when the
  executed cell is a double quote.
* `run_stringMode_parity`: String mode after a run is the initial mode toggled
  by the parity of the executed quote count.
* `run_stringMode_even`: Starting outside string mode, string mode is off
  exactly when an even number of quotes were executed.
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
    · simpa only [h, ↓Char.isValue, Char.reduceToNat, beq_eq_false_iff_ne, ne_eq]
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
      simp only [stringCodes, Int.ofNat_eq_natCast, List.range_zero, List.map_nil, List.reverse_nil,
      List.nil_append, runPos]
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
        simp only [↓Char.isValue, ne_eq, mid]
        exact hstr n (Nat.lt_succ_self n)
      have hstep : step mid = some { mid with
          stack := Stack.push mid.stack (Int.ofNat (mid.grid.get mid.pc.1 mid.pc.2).toNat),
          pc := stepPos w h mid.dir mid.pc } := by
        exact step_string_general mid (by simpa only [mid] using hsm) hcell
      rw [hstep]
      congr 1
      simp only [mid, stringCodes, Stack.push, List.range_succ, List.reverse_append, runPos,
        Int.ofNat_eq_natCast, List.map_append, List.map_cons, List.map_nil, List.reverse_cons,
        List.reverse_nil, List.nil_append, List.cons_append]

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
    change step s = some { s with
      stringMode := true, pc := stepPos w h Direction.right (x % w, y % h) }
    rw [step_string_enter s hm (by simpa only [hpc, ↓Char.isValue] using henter)]
    simp only [hpc, hdir]
  let s₁ : State w h := { s with
    stringMode := true, pc := stepPos w h Direction.right (x % w, y % h) }
  have hpc₁ : s₁.pc = ((x + 1) % w, y % h) := by
    simp only [s₁]
    have hrun := runPos_right w h 1 x y
    simpa only [runPos] using hrun
  have hstr₁ : StringRun s₁.grid s₁.dir (x + 1) y n := by
    simpa only [s₁, hdir] using hstr
  have hsm₁ : s₁.stringMode = true := by simp only [s₁]
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
    simp only [s₁, s₂, hdir]
  have h2 : run n s₁ = some s₂ := by
    rw [hn, hs₂]
  have hexit₁ : s₂.grid.get s₂.pc.1 s₂.pc.2 = '"' := by
    simp only [↓Char.isValue, s₂]
    exact hexit
  have hsm₂ : s₂.stringMode = true := by simp only [s₂]
  have h3 : run 1 s₂ = some { s₂ with
      stringMode := false, pc := stepPos w h Direction.right s₂.pc } := by
    rw [run, run]
    change step s₂ = some { s₂ with
      stringMode := false, pc := stepPos w h Direction.right s₂.pc }
    rw [step_string_exit s₂ hsm₂ hexit₁]
    simp only [s₂, hdir]
  have h12 := run_append s { s with
      stringMode := true, pc := stepPos w h Direction.right (x % w, y % h) }
    (some s₂) 1 n h1 (by
      simpa only [s₁] using h2)
  let s₃ : State w h := { s with
    stack := List.reverse (stringCodes s.grid Direction.right (x + 1) y n) ++ s.stack,
    pc := stepPos w h Direction.right (runPos w h n Direction.right ((x + 1) % w, y % h)) }
  have h3' : run 1 s₂ = some s₃ := by
    rw [h3]
    congr 1
    simp only [s₂, s₃, hm]
  have h23 := run_append s s₂ (some s₃) (1 + n) 1 h12 h3'
  have hlen : 1 + n + 1 = n + 2 := by omega
  have hfinal : run (n + 2) s = some s₃ := by
    simpa only [hlen] using h23
  simpa only [s₃, hm] using hfinal

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
      simp only [List.length_nil, run, runPos, List.map_nil, String.ofList_nil, String.append_empty,
      Option.some.injEq]
      have hrest : rest = s.stack := by
        rw [hstack]
        simp only [List.nil_append]
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
          simp only [List.length_cons, Nat.zero_lt_succ]
        exact hprint 0 h0
      have hstep : step s = some { s with
          output := s.output.push (Char.ofNat (Int.toNat c)),
          stack := cs' ++ rest,
          pc := stepPos w h Direction.right s.pc } := by
        rw [hdir]
        rw [step_printChar_general s hm (by simpa only [hpc, ↓Char.isValue] using hcell)]
        simp only [htop, hdrop, hdir]
      let s₁ : State w h := { s with
        output := s.output ++ String.singleton (Char.ofNat (Int.toNat c)),
        stack := cs' ++ rest,
        pc := runPos w h 1 Direction.right (x % w, y % h) }
      have h1 : run 1 s = some s₁ := by
        rw [run, run]
        change step s = some s₁
        rw [hstep]
        simp only [s₁, hpc, runPos, String.append_singleton]
      have hpc₁ : s₁.pc = ((x + 1) % w, y % h) := by
        simp only [s₁]
        have hrun := runPos_right w h 1 x y
        simpa only [runPos] using hrun
      have hsm₁ : s₁.stringMode = false := by simp only [s₁, hm]
      have hprint₁ : PrintRun s₁.grid (x + 1) y cs'.length := by
        intro k hk
        have hk' : k + 1 < n := by
          rw [← hlen]
          simp only [List.length_cons, Nat.add_lt_add_iff_right]
          omega
        have hpath := hprint (k + 1) hk'
        have hpos : runPos w h (k + 1) Direction.right (x % w, y % h) =
            runPos w h k Direction.right ((x + 1) % w, y % h) := by
          rw [runPos_right w h (k + 1) x y]
          rw [runPos_right w h k (x + 1) y]
          simp only [Nat.add_comm, Nat.add_left_comm]
        simpa only [s₁, hpos, ↓Char.isValue] using hpath
      let s₂ : State w h := { s₁ with
        output := s₁.output ++ String.ofList (cs'.map (fun v : Int => Char.ofNat (Int.toNat v))),
        stack := rest,
        pc := runPos w h cs'.length Direction.right ((x + 1) % w, y % h) }
      have hrun' : run cs'.length s₁ = some s₂ := by
        exact ih rest (x + 1) y cs'.length s₁ hpc₁ hsm₁
          (by simp only [s₁, hdir] ) rfl hprint₁ rfl
      have hn : n = 1 + cs'.length := by
        rw [← hlen]
        simp only [Nat.add_comm, List.length_cons,]
      have htotal := run_append s s₁ (some s₂) 1 cs'.length h1 hrun'
      rw [hn]
      rw [htotal]
      congr 1
      simp only [s₂, s₁, runPos_right, List.map_cons, push_ofList_cons, Nat.add_comm,
        Nat.add_left_comm, String.append_singleton]

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
    simpa only [s₀, codes] using h
  have hpc₀ : s₀.pc = ((x + n + 2) % w, y % h) := by
    simp only [s₀]
    rw [runPos_right w h n (x + 1) y]
    rw [show stepPos w h Direction.right ((x + 1 + n) % w, y % h) =
        runPos w h 1 Direction.right ((x + 1 + n) % w, y % h) by
          rw [runPos]
          rfl]
    rw [runPos_right w h 1 (x + 1 + n) y]
    have hx : x + 1 + n + 1 = x + n + 2 := by omega
    rw [hx]
  have hsm₀ : s₀.stringMode = false := by simp only [s₀, hm]
  have hdir₀ : s₀.dir = Direction.right := by simp only [s₀, hdir]
  have hlen : (List.reverse codes).length = n := by
    simp only [codes, stringCodes, List.length_map, List.length_reverse, List.length_range,
      Int.ofNat_eq_natCast]
  have hp := run_print (List.reverse codes) s.stack (x + n + 2) y n s₀ hpc₀ hsm₀ hdir₀ hlen
    hprint rfl
  let s₂ : State w h := { s with
    output := s.output ++
      String.ofList (codes.map (fun v : Int => Char.ofNat (Int.toNat v))).reverse,
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
        output := s₀.output ++
          String.ofList ((List.reverse codes).map (fun v : Int => Char.ofNat (Int.toNat v))),
        stack := s.stack,
        pc := runPos w h n Direction.right ((x + n + 2) % w, y % h) } = s₂ := by
      simp only [s₂, s₀, List.map_reverse, hpc_eq]
    rw [hp, h]
  have hsum : (n + 2) + n = 2 * n + 2 := by omega
  have htotal := run_append s s₀ (some s₂) (n + 2) n hblock hprintrun
  simpa only [hsum, s₂] using htotal

/-- In string mode the instruction set is ignored: the step never halts, never
    writes the playfield, never consumes input, never produces output, and
    never turns. Only the stack, the mode toggle, and the pointer move. -/
theorem step_string_mode (s : State w h) (hsm : s.stringMode = true) :
    ∃ s', step s = some s' ∧ s'.grid = s.grid ∧ s'.input = s.input ∧
      s'.output = s.output ∧ s'.dir = s.dir := by
  refine ⟨stepString s (s.grid.get s.pc.1 s.pc.2), ?_, ?_, ?_, ?_, ?_⟩
  · unfold step
    dsimp only
    rw [hsm]
  · exact stepString_grid _ _
  · exact stepString_input _ _
  · exact stepString_output _ _
  · exact stepString_dir _ _

/-- A run that stays in string mode throughout never halts, and leaves the
    playfield, input, output, and direction untouched: string mode is data,
    not code. The hypothesis is necessary — a closing `"` leaves string mode,
    after which the instruction set applies again. -/
theorem run_string_mode (n : ℕ) (s : State w h)
    (hin : ∀ k < n, ∀ sₖ, run k s = some sₖ → sₖ.stringMode = true) :
    ∃ s', run n s = some s' ∧ s'.grid = s.grid ∧ s'.input = s.input ∧
      s'.output = s.output ∧ s'.dir = s.dir := by
  induction n with
  | zero => exact ⟨s, rfl, rfl, rfl, rfl, rfl⟩
  | succ n ih =>
      obtain ⟨sₙ, hrun, hg, hi, ho, hd⟩ := ih (fun k hk sₖ hsₖ =>
        hin k (Nat.lt_succ_of_lt hk) sₖ hsₖ)
      have hsm : sₙ.stringMode = true := hin n (Nat.lt_succ_self n) sₙ hrun
      obtain ⟨s', hstep, hg', hi', ho', hd'⟩ := step_string_mode sₙ hsm
      refine ⟨s', ?_, ?_, ?_, ?_, ?_⟩
      · rw [run, hrun]; exact hstep
      · rw [hg', hg]
      · rw [hi', hi]
      · rw [ho', ho]
      · rw [hd', hd]

/-- A character decodes to the string-mode toggle exactly when it is `"`. -/
theorem decodeChar_stringMode_iff (c : Char) :
    decodeChar c = .stringMode ↔ c = '"' := by
  constructor
  · intro h
    unfold decodeChar at h
    split at h <;> simp only [reduceCtorEq] at h
    rfl
  · intro h
    rw [h]
    rfl

/-- Every step toggles string mode exactly when the executed cell is `"`. -/
theorem step_stringMode_xor {s s' : State w h} (hstep : step s = some s') :
    s'.stringMode = xor s.stringMode (s.grid.get s.pc.1 s.pc.2 == '"') := by
  by_cases hsm : s.stringMode = true
  · rw [step_eq_stepString s hsm] at hstep
    injection hstep with hs'
    rw [← hs', hsm]
    unfold stepString
    by_cases hq : (s.grid.get s.pc.1 s.pc.2) = '"'
    · rw [hq]
      simp only [beq_self_eq_true, Bool.true_xor, Bool.not_true]
    · have hb : ((s.grid.get s.pc.1 s.pc.2).toNat == '"'.toNat) = false := by
        by_cases hc : (s.grid.get s.pc.1 s.pc.2).toNat = '"'.toNat
        · exfalso
          apply hq
          unfold Char.toNat at hc
          exact Char.ext (UInt32.toNat_inj.mp hc)
        · simpa only [beq_eq_false_iff_ne, ne_eq]
      have hb2 : ((s.grid.get s.pc.1 s.pc.2) == '"') = false := by
        simpa only [beq_eq_false_iff_ne, ne_eq]
      rw [hb, hb2, hsm]
      simp only [Bool.true_xor, Bool.not_false]
  · have hf : s.stringMode = false := stringMode_false_of_not hsm
    rw [step_eq_stepState s hf (decodeChar_ne_halt_of_step hf hstep)] at hstep
    injection hstep with hs'
    rw [← hs', hf]
    by_cases hq : (s.grid.get s.pc.1 s.pc.2) = '"'
    · have hd : decodeChar (s.grid.get s.pc.1 s.pc.2) = .stringMode :=
        (decodeChar_stringMode_iff _).mpr hq
      rw [hd, hq]
      simp only [beq_self_eq_true, Bool.false_xor]
      exact stepState_stringMode_toggle s
    · have hd : decodeChar (s.grid.get s.pc.1 s.pc.2) ≠ .stringMode := by
        intro hc
        exact hq ((decodeChar_stringMode_iff _).mp hc)
      have hb2 : ((s.grid.get s.pc.1 s.pc.2) == '"') = false := by
        simpa only [beq_eq_false_iff_ne, ne_eq]
      rw [hb2]
      simp only [Bool.false_xor]
      rw [stepState_stringMode_of_ne s _ hd]
      exact hf

/-- The number of steps among the first `n` whose executed cell is `"`. -/
def quoteSteps (n : ℕ) (s : State w h) : ℕ :=
  match n with
  | 0 => 0
  | n + 1 =>
      match run n s with
      | none => quoteSteps n s
      | some sn =>
          if sn.grid.get sn.pc.1 sn.pc.2 = '"' then quoteSteps n s + 1
          else quoteSteps n s

/-- String mode after `n` steps is the initial mode toggled by the parity of
    the number of executed `"` cells. -/
theorem run_stringMode_parity (n : ℕ) (s : State w h) (s' : State w h)
    (hrun : run n s = some s') :
    s'.stringMode = xor s.stringMode (decide (quoteSteps n s % 2 = 1)) := by
  induction n generalizing s' with
  | zero =>
      rw [run] at hrun
      injection hrun with hs'
      rw [← hs']
      simp only [quoteSteps, Nat.zero_mod, Nat.zero_ne_one, decide_false,
        Bool.bne_false]
  | succ n ih =>
      rcases hn : run n s with _ | sn
      · rw [run, hn] at hrun; cases hrun
      · rw [run, hn] at hrun
        have hstep : step sn = some s' := by simpa only using hrun
        have hprev := ih sn hn
        have hq := step_stringMode_xor hstep
        have hcount : quoteSteps (n + 1) s =
            if sn.grid.get sn.pc.1 sn.pc.2 = '"' then quoteSteps n s + 1
            else quoteSteps n s := by
          rw [quoteSteps, hn]
        rw [hq, hprev, hcount]
        by_cases hc : sn.grid.get sn.pc.1 sn.pc.2 = '"'
        · rw [if_pos hc, hc]
          have hmod : decide ((quoteSteps n s + 1) % 2 = 1)
              = !decide (quoteSteps n s % 2 = 1) := by
            by_cases hp : quoteSteps n s % 2 = 1
            · simp only [hp, decide_true, Bool.not_true]
              exact decide_eq_false (by omega)
            · simp only [hp, decide_false, Bool.not_false]
              exact decide_eq_true (by omega)
          simp only [beq_self_eq_true, hmod, Bool.xor_not, Bool.xor_true]
        · have hb : (sn.grid.get sn.pc.1 sn.pc.2 == '"') = false := by
            simpa only [beq_eq_false_iff_ne, ne_eq]
          rw [if_neg hc, hb]
          simp only [Bool.xor_false]

/-- Starting outside string mode, string mode is off after `n` steps exactly
    when an even number of `"` cells were executed. -/
theorem run_stringMode_even (n : ℕ) (s : State w h) (s' : State w h)
    (hsm : s.stringMode = false) (hrun : run n s = some s') :
    s'.stringMode = false ↔ quoteSteps n s % 2 = 0 := by
  rw [run_stringMode_parity n s s' hrun, hsm]
  simp only [Bool.false_xor, decide_eq_false_iff_not]
  omega

end LeanFunge
