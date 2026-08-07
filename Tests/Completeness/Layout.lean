/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanFunge.Theory.Completeness.Layout

/-!
# Block Layout Geometry Tests
-/

namespace LeanFunge.Tests

open LeanFunge.Completeness

example (instr : CMInstr) : 1 ≤ blockWidth instr :=
  blockWidth_pos instr

example (instr : CMInstr) : 1 ≤ blockHeight instr :=
  blockHeight_pos instr

example (prog : CMProgram) (i : ℕ) :
    entryColumn prog (i + 1) = entryColumn prog i + blockWidth (prog.getD i .halt) :=
  entryColumn_succ prog i

example (prog : CMProgram) (i : ℕ) :
    blockRow prog (i + 1) = blockRow prog i + blockHeight (prog.getD i .halt) :=
  blockRow_succ prog i

example (prog : CMProgram) {i j : ℕ} (h : i < j) : entryColumn prog i < entryColumn prog j :=
  entryColumn_strict_mono prog h

example (prog : CMProgram) {i j : ℕ} (h : i < j) : blockRow prog i < blockRow prog j :=
  blockRow_strict_mono prog h

example : (playfieldOf layoutProgram).get 0 4 = '>' :=
  layout_entry

example : (playfieldOf layoutProgram).get 7 6 = '|' :=
  layout_decz_branch

example : (playfieldOf layoutProgram).get 8 9 = 'v' :=
  layout_jog

example : (playfieldOf layoutProgram).get 12 13 = '@' :=
  layout_halt

end LeanFunge.Tests
