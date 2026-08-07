/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanFunge.Theory.Completeness.LayoutCells

/-!
# Generated Playfield Row Range Tests
-/

namespace LeanFunge.Tests

open LeanFunge.Completeness

example (instr : CMInstr) (D y : ℕ) (c : (ℕ × ℕ) × Char)
    (hc : c ∈ blockBodyCells instr D y) :
    y ≤ c.1.2 ∧ c.1.2 < y + blockHeight instr :=
  blockBodyCells_row_range instr D y c hc

example (prog : CMProgram) (i : ℕ) : prog.length ≤ blockRow prog i :=
  blockRow_ge_length prog i

end LeanFunge.Tests
