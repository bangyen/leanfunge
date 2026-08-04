/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanFunge.Core.Semantics
import LeanFunge.Theory.Invariance
import Mathlib.Order.Nat
import Mathlib.Order.Monotone.Defs

/-!
# Program Equivalence

## Main definitions

* `Program`: A playfield considered as an executable program.
* `Program.equiv`: Two programs produce the same interpreter state (or both
  halt) after every finite number of steps from their standard initial states.
* `Program.observe`: The externally relevant part of a run result.
* `Program.observational_equiv`: Two programs agree on stack, output, and
  halting at every finite run length.
* `Program.trace_equiv`: Two programs have the same observable checkpoints,
  allowing different numbers of internal steps between checkpoints.
* `Program.ordered_trace_equiv`: The same, with monotone step-index
  alignments that preserve checkpoint order.
* `step_nop_observe`: A space preserves the observable state for one step.
* `run_nop_observe`: A run of no-ops preserves the observable state.

The definition compares the complete state, rather than only output, so later
rewrite theorems can preserve stack, instruction-pointer, and self-modifying
playfield behavior as well.
-/

namespace LeanFunge

/-- A program is a playfield with a fixed width and height. -/
def Program (w h : ℕ) := Grid w h

namespace Program

/-- The observable result of a bounded run: `none` means halted, while `some`
    retains the stack and output of a running state. -/
def observe (result : Option (State w h)) : Option (Stack × String) :=
  match result with
  | none => none
  | some s => some (s.stack, s.output)

/-- Two programs are equivalent when all bounded runs from `State.init` agree. -/
def equiv (p q : Program w h) : Prop :=
  ∀ n, run n (State.init p) = run n (State.init q)

/-- Two programs are observationally equivalent when their bounded runs agree
    on stack, output, and whether they have halted. -/
def observational_equiv (p q : Program w h) : Prop :=
  ∀ n, observe (run n (State.init p)) = observe (run n (State.init q))

/-- Two programs are trace-equivalent when every observable checkpoint of one
    run occurs at some finite step of the other, in both directions. -/
def trace_equiv (p q : Program w h) : Prop :=
  (∀ n, ∃ m, observe (run n (State.init p)) = observe (run m (State.init q))) ∧
    (∀ m, ∃ n, observe (run m (State.init q)) = observe (run n (State.init p)))

/-- Trace equivalence with monotone functions aligning the step indices in
    both directions. Unlike `trace_equiv`, this preserves checkpoint order. -/
def ordered_trace_equiv (p q : Program w h) : Prop :=
  ∃ f g : ℕ → ℕ,
    Monotone f ∧ Monotone g ∧
      (∀ n, observe (run n (State.init p)) =
        observe (run (f n) (State.init q))) ∧
      (∀ m, observe (run m (State.init q)) =
        observe (run (g m) (State.init p)))

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

/-- Strict program equivalence implies observational equivalence. -/
theorem equiv_observational_equiv {p q : Program w h} (h : equiv p q) :
    observational_equiv p q := by
  intro n
  rw [h n]

/-- Observational program equivalence is reflexive. -/
theorem observational_equiv_refl (p : Program w h) : observational_equiv p p := by
  intro n
  rfl

/-- Observational program equivalence is symmetric. -/
theorem observational_equiv_symm {p q : Program w h} (h : observational_equiv p q) :
    observational_equiv q p := by
  intro n
  exact (h n).symm

/-- Observational program equivalence is transitive. -/
theorem observational_equiv_trans {p q r : Program w h}
    (hpq : observational_equiv p q) (hqr : observational_equiv q r) :
    observational_equiv p r := by
  intro n
  exact (hpq n).trans (hqr n)

/-- Same-step observational equivalence implies trace equivalence. -/
theorem observational_equiv_trace_equiv {p q : Program w h}
    (h : observational_equiv p q) : trace_equiv p q := by
  constructor
  · intro n
    exact ⟨n, h n⟩
  · intro m
    exact ⟨m, (h m).symm⟩

/-- Trace equivalence is reflexive. -/
theorem trace_equiv_refl (p : Program w h) : trace_equiv p p := by
  constructor <;> intro n <;> exact ⟨n, rfl⟩

/-- Trace equivalence is symmetric. -/
theorem trace_equiv_symm {p q : Program w h} (h : trace_equiv p q) :
    trace_equiv q p := by
  constructor
  · intro m
    rcases h.2 m with ⟨n, hn⟩
    exact ⟨n, hn⟩
  · intro n
    rcases h.1 n with ⟨m, hm⟩
    exact ⟨m, hm⟩

/-- Trace equivalence is transitive. -/
theorem trace_equiv_trans {p q r : Program w h}
    (hpq : trace_equiv p q) (hqr : trace_equiv q r) : trace_equiv p r := by
  constructor
  · intro n
    rcases hpq.1 n with ⟨m, hm⟩
    rcases hqr.1 m with ⟨l, hl⟩
    exact ⟨l, hm.trans hl⟩
  · intro l
    rcases hqr.2 l with ⟨m, hm⟩
    rcases hpq.2 m with ⟨n, hn⟩
    exact ⟨n, hm.trans hn⟩

/-- Same-step observational equivalence implies ordered trace equivalence. -/
theorem observational_equiv_ordered_trace_equiv {p q : Program w h}
    (h : observational_equiv p q) : ordered_trace_equiv p q := by
  refine ⟨id, id, monotone_id, monotone_id, ?_, ?_⟩
  · intro n
    exact h n
  · intro m
    exact (h m).symm

/-- Ordered trace equivalence is reflexive. -/
theorem ordered_trace_equiv_refl (p : Program w h) : ordered_trace_equiv p p := by
  exact observational_equiv_ordered_trace_equiv (observational_equiv_refl p)

/-- Ordered trace equivalence is symmetric. -/
theorem ordered_trace_equiv_symm {p q : Program w h}
    (h : ordered_trace_equiv p q) : ordered_trace_equiv q p := by
  rcases h with ⟨f, g, hf, hg, hfg, hgf⟩
  exact ⟨g, f, hg, hf, hgf, hfg⟩

/-- Ordered trace equivalence is transitive. -/
theorem ordered_trace_equiv_trans {p q r : Program w h}
    (hpq : ordered_trace_equiv p q) (hqr : ordered_trace_equiv q r) :
    ordered_trace_equiv p r := by
  rcases hpq with ⟨f, g, hf, hg, hfg, hgf⟩
  rcases hqr with ⟨u, v, hu, hv, huv, hvu⟩
  refine ⟨u ∘ f, g ∘ v, hu.comp hf, hg.comp hv, ?_, ?_⟩
  · intro n
    exact (hfg n).trans (huv (f n))
  · intro l
    exact (hvu l).trans (hgf (v l))

/-- A non-string-mode space preserves stack and output for one step. -/
theorem step_nop_observe_of_decoded (s : State w h) (hm : s.stringMode = false)
    (hnop : decodeChar (s.grid.get s.pc.1 s.pc.2) = .nop) :
    observe (step s) = some (s.stack, s.output) := by
  unfold step
  dsimp only
  rw [hm, hnop]
  rfl

/-- A non-string-mode space preserves stack and output for one step. -/
theorem step_nop_observe (s : State w h) (hm : s.stringMode = false)
    (hcell : s.grid.get s.pc.1 s.pc.2 = ' ') :
    observe (step s) = some (s.stack, s.output) := by
  apply step_nop_observe_of_decoded s hm
  rw [hcell]
  rfl

/-- A run whose every reached state executes a no-op preserves its initial
    stack and output, and remains running. -/
theorem run_nop_observe (s : State w h) (n : ℕ) (s' : State w h)
    (h : run n s = some s')
    (hn : ∀ k, k ≤ n → ∀ sₖ, run k s = some sₖ →
      sₖ.stringMode = false ∧ decodeChar (sₖ.grid.get sₖ.pc.1 sₖ.pc.2) = .nop) :
    observe (run n s) = some (s.stack, s.output) := by
  induction n generalizing s' with
  | zero =>
      rw [run] at h
      injection h with hs'
      rw [run, hs']
      rfl
  | succ n ih =>
      rcases hrun : run n s with _ | sₙ
      · rw [run, hrun] at h
        cases h
      · rw [run, hrun] at h
        have hstep : step sₙ = some s' := by simpa only using h
        have hprev : observe (some sₙ) = some (s.stack, s.output) := by
          rw [← hrun]
          apply ih sₙ hrun
          intro k hk sₖ hsₖ
          exact hn k (Nat.le_trans hk (Nat.le_succ n)) sₖ hsₖ
        have hnext : observe (some s') = observe (some sₙ) := by
          rw [← hstep]
          simpa only using step_nop_observe_of_decoded sₙ
            (hn n (Nat.le_succ n) sₙ hrun).1
            (hn n (Nat.le_succ n) sₙ hrun).2
        rw [run, hrun]
        change observe (step sₙ) = some (s.stack, s.output)
        rw [hstep]
        exact hnext.trans hprev

end Program

end LeanFunge
