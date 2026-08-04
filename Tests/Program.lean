/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanFunge.Examples.Program

/-!
# Program Equivalence Tests
-/

namespace LeanFunge.Tests

open LeanFunge

example (p : Program w h) : Program.equiv p p :=
  Program.equiv_refl p

example {p q : Program w h} (h : Program.equiv p q) : Program.equiv q p :=
  Program.equiv_symm h

example {p q r : Program w h} (hpq : Program.equiv p q) (hqr : Program.equiv q r) :
    Program.equiv p r :=
  Program.equiv_trans hpq hqr

example {p q : Program w h} (h : Program.equiv p q) :
    Program.observational_equiv p q :=
  Program.equiv_observational_equiv h

example (p : Program w h) : Program.observational_equiv p p :=
  Program.observational_equiv_refl p

example {p q : Program w h} (h : Program.observational_equiv p q) :
    Program.observational_equiv q p :=
  Program.observational_equiv_symm h

example {p q r : Program w h}
    (hpq : Program.observational_equiv p q)
    (hqr : Program.observational_equiv q r) :
    Program.observational_equiv p r :=
  Program.observational_equiv_trans hpq hqr

example {p q : Program w h} (h : Program.observational_equiv p q) :
    Program.trace_equiv p q :=
  Program.observational_equiv_trace_equiv h

example (p : Program w h) : Program.trace_equiv p p :=
  Program.trace_equiv_refl p

example {p q : Program w h} (h : Program.trace_equiv p q) : Program.trace_equiv q p :=
  Program.trace_equiv_symm h

example {p q r : Program w h}
    (hpq : Program.trace_equiv p q) (hqr : Program.trace_equiv q r) :
    Program.trace_equiv p r :=
  Program.trace_equiv_trans hpq hqr

example {p q : Program w h} (h : Program.observational_equiv p q) :
    Program.ordered_trace_equiv p q :=
  Program.observational_equiv_ordered_trace_equiv h

example (p : Program w h) : Program.ordered_trace_equiv p p :=
  Program.ordered_trace_equiv_refl p

example {p q : Program w h} (h : Program.ordered_trace_equiv p q) :
    Program.ordered_trace_equiv q p :=
  Program.ordered_trace_equiv_symm h

example {p q r : Program w h}
    (hpq : Program.ordered_trace_equiv p q)
    (hqr : Program.ordered_trace_equiv q r) :
    Program.ordered_trace_equiv p r :=
  Program.ordered_trace_equiv_trans hpq hqr

example {w h : ℕ} (s : State w h) (hm : s.stringMode = false)
    (hcell : s.grid.get s.pc.1 s.pc.2 = ' ') :
    Program.observe (step s) = some (s.stack, s.output) :=
  Program.step_nop_observe s hm hcell

example {w h : ℕ} (s : State w h) (n : ℕ) (s' : State w h)
    (h : run n s = some s')
    (hn : ∀ k, k ≤ n → ∀ sₖ, run k s = some sₖ →
      sₖ.stringMode = false ∧ decodeChar (sₖ.grid.get sₖ.pc.1 sₖ.pc.2) = .nop) :
    Program.observe (run n s) = some (s.stack, s.output) :=
  Program.run_nop_observe s n s' h hn

example {w h : ℕ} (s s' : State w h) (hstep : step s = some s') (n : ℕ) :
    run (n + 1) s = run n s' :=
  Program.run_succ_eq_run_from_step hstep n

example {w h : ℕ} {p q : Program w h} (q' : State w h)
    (hstep : step (State.init q) = some q')
    (h₀ : Program.observe (run 0 (State.init p)) =
      Program.observe (run 0 (State.init q)))
    (hcont : ∀ n, Program.observe (run n (State.init p)) = Program.observe (run n q')) :
    Program.ordered_trace_equiv p q :=
  Program.ordered_trace_equiv_of_step_continuation q' hstep h₀ hcont

end LeanFunge.Tests
