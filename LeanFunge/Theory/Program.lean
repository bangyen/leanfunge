/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanFunge.Core.Semantics

/-!
# Program Equivalence

## Main definitions

* `Program`: A playfield considered as an executable program.
* `Program.equiv`: Two programs produce the same interpreter state (or both
  halt) after every finite number of steps from their standard initial states.

The definition compares the complete state, rather than only output, so later
rewrite theorems can preserve stack, instruction-pointer, and self-modifying
playfield behavior as well.
-/

namespace LeanFunge

/-- A program is a playfield with a fixed width and height. -/
def Program (w h : ℕ) := Grid w h

namespace Program

/-- Two programs are equivalent when all bounded runs from `State.init` agree. -/
def equiv (p q : Program w h) : Prop :=
  ∀ n, run n (State.init p) = run n (State.init q)

/-- Program equivalence is reflexive. -/
theorem equiv_refl (p : Program w h) : equiv p p := by
  intro n
  rfl

/-- Program equivalence is symmetric. -/
theorem equiv_symm {p q : Program w h} (h : equiv p q) : equiv q p := by
  intro n
  exact (h n).symm

/-- Program equivalence is transitive. -/
theorem equiv_trans {p q r : Program w h} (hpq : equiv p q) (hqr : equiv q r) :
    equiv p r := by
  intro n
  exact (hpq n).trans (hqr n)

end Program

end LeanFunge
