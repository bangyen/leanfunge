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

example {p : Program w h} {q : Program w' h'}
    (h : Program.observational_equiv_between p q) :
    Program.ordered_trace_equiv_between p q :=
  Program.observational_equiv_between_ordered_trace_equiv_between h

example {R : State w h → State w' h' → Prop}
    (hR : Program.state_simulation R) {s : State w h} {t : State w' h'}
    (hst : R s t) : Program.observe (some s) = Program.observe (some t) :=
  Program.state_simulation_observe hR hst

example {R : State w h → State w' h' → Prop}
    (hR : Program.state_simulation R) {s : State w h} {t : State w' h'}
    (hst : R s t) : step s = none ↔ step t = none :=
  Program.state_simulation_halts hR hst

example (s : State w h) :
    Program.observe (some s) = Program.observe (some (Program.prependSpaceState s)) :=
  Program.prependSpaceState_observe s

example (s : State w h) (hx : s.pc.1 < w) :
    (Program.prependSpaceState s).grid.get (Program.prependSpaceState s).pc.1
      (Program.prependSpaceState s).pc.2 = s.grid.get s.pc.1 s.pc.2 :=
  Program.prependSpaceState_cell s hx

example (s : State w h) (k : ℕ) (hx : s.pc.1 < w) :
    (Program.prependSpacesState s k).grid.get (Program.prependSpacesState s k).pc.1
      (Program.prependSpacesState s k).pc.2 = s.grid.get s.pc.1 s.pc.2 :=
  Program.prependSpacesState_cell s k hx

example (s : State w h) :
    Program.observe (some s) = Program.observe (some (Program.rotateCWState s)) :=
  Program.rotateCWState_observe s

example (s : State w h) (hdir : s.dir = .right) (hm : s.stringMode = false)
    (hcell : s.grid.get s.pc.1 s.pc.2 = ' ') (hx : s.pc.1 + 1 < w) :
    step (Program.prependSpaceState s) =
      some (Program.prependSpaceState { s with pc := stepPos w h .right s.pc }) :=
  Program.step_prependSpaceState_nop_right s hdir hm hcell hx

example (s : State w h) (k : ℕ) (hdir : s.dir = .right)
    (hm : s.stringMode = false)
    (hcell : s.grid.get s.pc.1 s.pc.2 = ' ') (hx : s.pc.1 + 1 < w) :
    step (Program.prependSpacesState s k) = some (Program.prependSpacesState
      { s with pc := stepPos w h .right s.pc } k) :=
  Program.step_prependSpacesState_nop_right s k hdir hm hcell hx

example (s : State w h) (k : ℕ) (n : Int) (hdir : s.dir = .right)
    (hm : s.stringMode = false)
    (hdecode : decodeChar (s.grid.get s.pc.1 s.pc.2) = .push n)
    (hx : s.pc.1 + 1 < w) :
    step (Program.prependSpacesState s k) = some (Program.prependSpacesState
      (stepState s (.push n)) k) :=
  Program.step_prependSpacesState_push_right s k n hdir hm hdecode hx

example (s : State w h) (k : ℕ) (hdir : s.dir = .right)
    (hm : s.stringMode = false)
    (hdecode : decodeChar (s.grid.get s.pc.1 s.pc.2) = .add)
    (hx : s.pc.1 + 1 < w) :
    step (Program.prependSpacesState s k) = some (Program.prependSpacesState
      (stepState s .add) k) :=
  Program.step_prependSpacesState_add_right s k hdir hm hdecode hx

example (s : State w h) (k : ℕ) (hdir : s.dir = .right)
    (hm : s.stringMode = false)
    (hdecode : decodeChar (s.grid.get s.pc.1 s.pc.2) = .printInt)
    (hx : s.pc.1 + 1 < w) :
    step (Program.prependSpacesState s k) = some (Program.prependSpacesState
      (stepState s .printInt) k) :=
  Program.step_prependSpacesState_printInt_right s k hdir hm hdecode hx

example (s : State w h) (k : ℕ) (hm : s.stringMode = false)
    (hdecode : decodeChar (s.grid.get s.pc.1 s.pc.2) = .halt)
    (hx : s.pc.1 + 1 < w) :
    step (Program.prependSpacesState s k) = none :=
  Program.step_prependSpacesState_halt_right s k hm hdecode hx

example (s : State w h) (n : Int) (hdir : s.dir = .right)
    (hm : s.stringMode = false)
    (hdecode : decodeChar (s.grid.get s.pc.1 s.pc.2) = .push n)
    (hx : s.pc.1 + 1 < w) :
    step (Program.prependSpaceState s) = some (Program.prependSpaceState
      { s with stack := Stack.push s.stack n, pc := stepPos w h .right s.pc }) :=
  Program.step_prependSpaceState_push_right s n hdir hm hdecode hx

example (s : State w h) (hdir : s.dir = .right) (hm : s.stringMode = false)
    (hdecode : decodeChar (s.grid.get s.pc.1 s.pc.2) = .add)
    (hx : s.pc.1 + 1 < w) :
    step (Program.prependSpaceState s) =
      some (Program.prependSpaceState (stepState s .add)) :=
  Program.step_prependSpaceState_add_right s hdir hm hdecode hx

example (s : State w h) (hdir : s.dir = .right) (hm : s.stringMode = false)
    (hdecode : decodeChar (s.grid.get s.pc.1 s.pc.2) = .printInt)
    (hx : s.pc.1 + 1 < w) :
    step (Program.prependSpaceState s) =
      some (Program.prependSpaceState (stepState s .printInt)) :=
  Program.step_prependSpaceState_printInt_right s hdir hm hdecode hx

example (s : State w h) (hm : s.stringMode = false)
    (hdecode : decodeChar (s.grid.get s.pc.1 s.pc.2) = .halt)
    (hx : s.pc.1 + 1 < w) :
    step (Program.prependSpaceState s) = none :=
  Program.step_prependSpaceState_halt_right s hm hdecode hx

example {R : State w h → State w' h' → Prop}
    (hR : Program.state_simulation R) {s : State w h} {t : State w' h'}
    (hst : R s t) (n : ℕ) :
    Program.option_state_related R (run n s) (run n t) :=
  Program.run_related_of_state_simulation hR hst n

example {R : State w h → State w' h' → Prop}
    (hR : Program.state_simulation R) {s : State w h} {t : State w' h'}
    (hst : R s t) (n : ℕ) :
    Program.observe (run n s) = Program.observe (run n t) :=
  Program.run_observations_of_state_simulation hR hst n

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

example {p : Program w h} {q : Program w' h'}
    (h₀ : Program.observe (run 0 (State.init p)) =
      Program.observe (run 0 (State.init q)))
    (hshift : ∀ n, Program.observe (run n (State.init p)) =
      Program.observe (run (n + 1) (State.init q))) :
  Program.ordered_trace_equiv_between p q :=
  Program.ordered_trace_equiv_between_one_step_prefix h₀ hshift

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

example {w h : ℕ} {p q : Program w h}
    (hm : (State.init q).stringMode = false)
    (hcell : (State.init q).grid.get (State.init q).pc.1 (State.init q).pc.2 = ' ')
    (h₀ : Program.observe (run 0 (State.init p)) =
      Program.observe (run 0 (State.init q)))
    (hcont : ∀ n, Program.observe (run n (State.init p)) =
      Program.observe (run n (Program.nop_successor (State.init q)))) :
    Program.ordered_trace_equiv p q :=
  Program.ordered_trace_equiv_of_nop_continuation hm hcell h₀ hcont

example {w h : ℕ} (s t : State w h) (k : ℕ)
    (hs : ∀ d, run (k + d) s = none)
    (ht : ∀ d, run (k + d) t = none)
    (hobs : ∀ n, n < k → Program.observe (run n s) = Program.observe (run n t)) :
    ∀ n, Program.observe (run n s) = Program.observe (run n t) :=
  Program.run_observe_eq_of_finite_prefix s t k hs ht hobs

end LeanFunge.Tests
