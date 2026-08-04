/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanFunge.Core.Semantics
import LeanFunge.Theory.Invariance
import LeanFunge.Theory.Run.Relational
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

/-- The I/O behavior of a bounded run: `none` means halted, while `some`
    retains the remaining input stream and the output produced so far. -/
def ioBehavior (s : State w h) (n : ℕ) : Option (List Char × String) :=
  (run n s).map (fun s' => (s'.input, s'.output))

/-- Composing a run with a continuation preserves its I/O behavior. -/
theorem ioBehavior_append (s s' : State w h) (n m : ℕ)
    (h₁ : run n s = some s') :
    ioBehavior s (n + m) = ioBehavior s' m := by
  unfold ioBehavior
  rw [run_append s s' (run m s') n m h₁ rfl]

/-- Two programs are equivalent when all bounded runs from `State.init` agree. -/
def equiv (p q : Program w h) : Prop :=
  ∀ n, run n (State.init p) = run n (State.init q)

/-- Two programs are observationally equivalent when their bounded runs agree
    on stack, output, and whether they have halted. -/
def observational_equiv (p q : Program w h) : Prop :=
  ∀ n, observe (run n (State.init p)) = observe (run n (State.init q))

/-- Observational equivalence for programs whose playfields may have different
    dimensions. -/
def observational_equiv_between (p : Program w h) (q : Program w' h') : Prop :=
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

/-- Ordered trace equivalence for programs whose playfields may have different
    dimensions. -/
def ordered_trace_equiv_between (p : Program w h) (q : Program w' h') : Prop :=
  ∃ f g : ℕ → ℕ,
    Monotone f ∧ Monotone g ∧
      (∀ n, observe (run n (State.init p)) =
        observe (run (f n) (State.init q))) ∧
      (∀ m, observe (run m (State.init q)) =
        observe (run (g m) (State.init p)))

/-- A bisimulation between states on possibly different playfields. Related
    states have equal observations, agree on halting, and have related
    successors in both directions. -/
def state_simulation (R : State w h → State w' h' → Prop) : Prop :=
  ∀ s t, R s t →
    observe (some s) = observe (some t) ∧
      (step s = none ↔ step t = none) ∧
      (∀ s', step s = some s' → ∃ t', step t = some t' ∧ R s' t') ∧
      (∀ t', step t = some t' → ∃ s', step s = some s' ∧ R s' t')

/-- Shift a state into a playfield with a leading-space column. -/
def prependSpaceState (s : State w h) : State (w + 1) h :=
  { s with
    grid := Grid.prependSpace s.grid
    pc := (s.pc.1 + 1, s.pc.2) }

/-- Shift a state into a playfield with `k` leading-space columns. -/
def prependSpacesState (s : State w h) (k : ℕ) : State (w + k) h :=
  { s with
    grid := Grid.prependSpaces s.grid k
    pc := (s.pc.1 + k, s.pc.2) }

/-- Rotate a state clockwise, including its instruction-pointer coordinates and
    direction. -/
def rotateCWDirection : Direction → Direction
  | .right => .down
  | .down => .left
  | .left => .up
  | .up => .right

def rotateCWState (s : State w h) : State h w :=
  { s with
    grid := Grid.rotateCW s.grid
    pc := (h - 1 - s.pc.2, s.pc.1)
    dir := rotateCWDirection s.dir }

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

/-- Same-step cross-dimension equivalence implies ordered trace equivalence. -/
theorem observational_equiv_between_ordered_trace_equiv_between
    {p : Program w h} {q : Program w' h'}
    (h : observational_equiv_between p q) : ordered_trace_equiv_between p q := by
  refine ⟨id, id, monotone_id, monotone_id, ?_, ?_⟩
  · intro n
    exact h n
  · intro m
    exact (h m).symm

/-- A state simulation preserves observations of related states. -/
theorem state_simulation_observe {R : State w h → State w' h' → Prop}
    (hR : state_simulation R) {s t} (hst : R s t) :
    observe (some s) = observe (some t) :=
  (hR s t hst).1

/-- A state simulation preserves halting at related states. -/
theorem state_simulation_halts {R : State w h → State w' h' → Prop}
    (hR : state_simulation R) {s t} (hst : R s t) :
    step s = none ↔ step t = none :=
  (hR s t hst).2.1

/-- Leading-space state mapping preserves the observable state. -/
theorem prependSpaceState_observe (s : State w h) :
    observe (some s) = observe (some (prependSpaceState s)) := by
  rfl

/-- The leading-space state mapping preserves the fetched cell before the new
    toroidal boundary. -/
theorem prependSpaceState_cell (s : State w h) (hx : s.pc.1 < w) :
    (prependSpaceState s).grid.get (prependSpaceState s).pc.1
      (prependSpaceState s).pc.2 = s.grid.get s.pc.1 s.pc.2 := by
  change (Grid.prependSpace s.grid).get (s.pc.1 + 1) s.pc.2 =
    s.grid.get s.pc.1 s.pc.2
  exact Grid.get_prependSpace_succ s.grid s.pc.1 s.pc.2 hx

/-- Arbitrary leading-space state mapping preserves the fetched cell before the
    new toroidal boundary. -/
theorem prependSpacesState_cell (s : State w h) (k : ℕ) (hx : s.pc.1 < w) :
    (prependSpacesState s k).grid.get (prependSpacesState s k).pc.1
      (prependSpacesState s k).pc.2 = s.grid.get s.pc.1 s.pc.2 := by
  change (Grid.prependSpaces s.grid k).get (s.pc.1 + k) s.pc.2 =
    s.grid.get s.pc.1 s.pc.2
  exact Grid.get_prependSpaces_add s.grid k s.pc.1 s.pc.2 hx

/-- Clockwise state rotation preserves the observable state. -/
theorem rotateCWState_observe (s : State w h) :
    observe (some s) = observe (some (rotateCWState s)) := by
  rfl

/-- Clockwise rotation maps a right-moving no-op step to a down-moving no-op
    step before either playfield boundary. -/
theorem step_rotateCWState_nop_right (s : State w h)
    (hm : s.stringMode = false) (hdir : s.dir = .right)
    (hcell : s.grid.get s.pc.1 s.pc.2 = ' ')
    (hx : s.pc.1 + 1 < w) (hy : s.pc.2 < h) :
    step (rotateCWState s) = some (rotateCWState
      { s with pc := stepPos w h .right s.pc }) := by
  have hpc : s.pc.1 < w := by omega
  have hcell' : (rotateCWState s).grid.get (rotateCWState s).pc.1
      (rotateCWState s).pc.2 = ' ' := by
    change (Grid.rotateCW s.grid).get (h - 1 - s.pc.2) s.pc.1 = ' '
    rw [Grid.get_rotateCW s.grid s.pc.1 s.pc.2 hpc hy]
    exact hcell
  have hm' : (rotateCWState s).stringMode = false := hm
  rw [step_nop (rotateCWState s) hm' hcell']
  have hrotx : h - 1 - s.pc.2 < h := by omega
  simp [rotateCWState, rotateCWDirection, stepPos, hdir,
    Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy, Nat.mod_eq_of_lt hrotx]

/-- Clockwise rotation maps a right-moving push step to a down-moving push
    step before either playfield boundary. -/
theorem step_rotateCWState_push_right (s : State w h) (n : Int)
    (hm : s.stringMode = false) (hdir : s.dir = .right)
    (hdecode : decodeChar (s.grid.get s.pc.1 s.pc.2) = .push n)
    (hx : s.pc.1 + 1 < w) (hy : s.pc.2 < h) :
    step (rotateCWState s) = some (rotateCWState (stepState s (.push n))) := by
  have hpc : s.pc.1 < w := by omega
  have hcell : (rotateCWState s).grid.get (rotateCWState s).pc.1
      (rotateCWState s).pc.2 = s.grid.get s.pc.1 s.pc.2 := by
    change (Grid.rotateCW s.grid).get (h - 1 - s.pc.2) s.pc.1 = _
    rw [Grid.get_rotateCW s.grid s.pc.1 s.pc.2 hpc hy]
  have hdecode' : decodeChar ((rotateCWState s).grid.get
      (rotateCWState s).pc.1 (rotateCWState s).pc.2) = .push n := by
    rw [hcell]
    exact hdecode
  unfold step
  dsimp only
  have hm' : (rotateCWState s).stringMode = false := hm
  rw [hdecode', hm']
  have hrotx : h - 1 - s.pc.2 < h := by omega
  simp [rotateCWState, rotateCWDirection, stepState, stepPos, hdir,
    Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy, Nat.mod_eq_of_lt hrotx]

/-- Clockwise rotation maps a right-moving addition step to a down-moving
    addition step before either playfield boundary. -/
theorem step_rotateCWState_add_right (s : State w h)
    (hm : s.stringMode = false) (hdir : s.dir = .right)
    (hdecode : decodeChar (s.grid.get s.pc.1 s.pc.2) = .add)
    (hx : s.pc.1 + 1 < w) (hy : s.pc.2 < h) :
    step (rotateCWState s) = some (rotateCWState (stepState s .add)) := by
  have hpc : s.pc.1 < w := by omega
  have hcell : (rotateCWState s).grid.get (rotateCWState s).pc.1
      (rotateCWState s).pc.2 = s.grid.get s.pc.1 s.pc.2 := by
    change (Grid.rotateCW s.grid).get (h - 1 - s.pc.2) s.pc.1 = _
    rw [Grid.get_rotateCW s.grid s.pc.1 s.pc.2 hpc hy]
  have hdecode' : decodeChar ((rotateCWState s).grid.get
      (rotateCWState s).pc.1 (rotateCWState s).pc.2) = .add := by
    rw [hcell]
    exact hdecode
  unfold step
  dsimp only
  have hm' : (rotateCWState s).stringMode = false := hm
  rw [hdecode', hm']
  have hrotx : h - 1 - s.pc.2 < h := by omega
  simp [rotateCWState, rotateCWDirection, stepState, stepPos, hdir,
    Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy, Nat.mod_eq_of_lt hrotx]

/-- Clockwise rotation maps a right-moving integer-output step to a down-moving
    integer-output step before either playfield boundary. -/
theorem step_rotateCWState_printInt_right (s : State w h)
    (hm : s.stringMode = false) (hdir : s.dir = .right)
    (hdecode : decodeChar (s.grid.get s.pc.1 s.pc.2) = .printInt)
    (hx : s.pc.1 + 1 < w) (hy : s.pc.2 < h) :
    step (rotateCWState s) = some (rotateCWState (stepState s .printInt)) := by
  have hpc : s.pc.1 < w := by omega
  have hdecode' : decodeChar ((rotateCWState s).grid.get
      (rotateCWState s).pc.1 (rotateCWState s).pc.2) = .printInt := by
    change decodeChar ((Grid.rotateCW s.grid).get (h - 1 - s.pc.2) s.pc.1) = .printInt
    rw [Grid.get_rotateCW s.grid s.pc.1 s.pc.2 hpc hy]
    exact hdecode
  unfold step
  dsimp only
  have hm' : (rotateCWState s).stringMode = false := hm
  rw [hdecode', hm']
  have hrotx : h - 1 - s.pc.2 < h := by omega
  simp [rotateCWState, rotateCWDirection, stepState, stepPos, hdir,
    Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy, Nat.mod_eq_of_lt hrotx]

/-- Clockwise rotation maps a right-moving halt step to a down-moving halt
    step before either playfield boundary. -/
theorem step_rotateCWState_halt_right (s : State w h)
    (hm : s.stringMode = false)
    (hdecode : decodeChar (s.grid.get s.pc.1 s.pc.2) = .halt)
    (hx : s.pc.1 + 1 < w) (hy : s.pc.2 < h) :
    step (rotateCWState s) = none := by
  have hpc : s.pc.1 < w := by omega
  have hdecode' : decodeChar ((rotateCWState s).grid.get
      (rotateCWState s).pc.1 (rotateCWState s).pc.2) = .halt := by
    change decodeChar ((Grid.rotateCW s.grid).get (h - 1 - s.pc.2) s.pc.1) = .halt
    rw [Grid.get_rotateCW s.grid s.pc.1 s.pc.2 hpc hy]
    exact hdecode
  unfold step
  dsimp only
  have hm' : (rotateCWState s).stringMode = false := hm
  rw [hdecode', hm']

/-- Clockwise rotation maps a right-moving duplication step to a down-moving
    duplication step before either playfield boundary. -/
theorem step_rotateCWState_dup_right (s : State w h)
    (hm : s.stringMode = false) (hdir : s.dir = .right)
    (hdecode : decodeChar (s.grid.get s.pc.1 s.pc.2) = .dup)
    (hx : s.pc.1 + 1 < w) (hy : s.pc.2 < h) :
    step (rotateCWState s) = some (rotateCWState (stepState s .dup)) := by
  have hpc : s.pc.1 < w := by omega
  have hdecode' : decodeChar ((rotateCWState s).grid.get
      (rotateCWState s).pc.1 (rotateCWState s).pc.2) = .dup := by
    change decodeChar ((Grid.rotateCW s.grid).get (h - 1 - s.pc.2) s.pc.1) = .dup
    rw [Grid.get_rotateCW s.grid s.pc.1 s.pc.2 hpc hy]
    exact hdecode
  unfold step
  dsimp only
  have hm' : (rotateCWState s).stringMode = false := hm
  rw [hdecode', hm']
  have hrotx : h - 1 - s.pc.2 < h := by omega
  simp [rotateCWState, rotateCWDirection, stepState, stepPos, hdir,
    Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy, Nat.mod_eq_of_lt hrotx]

/-- Clockwise rotation maps a right-moving swap step to a down-moving swap step
    before either playfield boundary. -/
theorem step_rotateCWState_swap_right (s : State w h)
    (hm : s.stringMode = false) (hdir : s.dir = .right)
    (hdecode : decodeChar (s.grid.get s.pc.1 s.pc.2) = .swap)
    (hx : s.pc.1 + 1 < w) (hy : s.pc.2 < h) :
    step (rotateCWState s) = some (rotateCWState (stepState s .swap)) := by
  have hpc : s.pc.1 < w := by omega
  have hdecode' : decodeChar ((rotateCWState s).grid.get
      (rotateCWState s).pc.1 (rotateCWState s).pc.2) = .swap := by
    change decodeChar ((Grid.rotateCW s.grid).get (h - 1 - s.pc.2) s.pc.1) = .swap
    rw [Grid.get_rotateCW s.grid s.pc.1 s.pc.2 hpc hy]
    exact hdecode
  unfold step
  dsimp only
  have hm' : (rotateCWState s).stringMode = false := hm
  rw [hdecode', hm']
  have hrotx : h - 1 - s.pc.2 < h := by omega
  simp [rotateCWState, rotateCWDirection, stepState, stepPos, hdir,
    Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy, Nat.mod_eq_of_lt hrotx]

/-- Clockwise rotation maps a right-moving drop step to a down-moving drop step
    before either playfield boundary. -/
theorem step_rotateCWState_drop_right (s : State w h)
    (hm : s.stringMode = false) (hdir : s.dir = .right)
    (hdecode : decodeChar (s.grid.get s.pc.1 s.pc.2) = .drop)
    (hx : s.pc.1 + 1 < w) (hy : s.pc.2 < h) :
    step (rotateCWState s) = some (rotateCWState (stepState s .drop)) := by
  have hpc : s.pc.1 < w := by omega
  have hdecode' : decodeChar ((rotateCWState s).grid.get
      (rotateCWState s).pc.1 (rotateCWState s).pc.2) = .drop := by
    change decodeChar ((Grid.rotateCW s.grid).get (h - 1 - s.pc.2) s.pc.1) = .drop
    rw [Grid.get_rotateCW s.grid s.pc.1 s.pc.2 hpc hy]
    exact hdecode
  unfold step
  dsimp only
  have hm' : (rotateCWState s).stringMode = false := hm
  rw [hdecode', hm']
  have hrotx : h - 1 - s.pc.2 < h := by omega
  simp [rotateCWState, rotateCWDirection, stepState, stepPos, hdir,
    Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy, Nat.mod_eq_of_lt hrotx]

/-- Clockwise rotation maps a right-moving character-output step to a
    down-moving character-output step before either playfield boundary. -/
theorem step_rotateCWState_printChar_right (s : State w h)
    (hm : s.stringMode = false) (hdir : s.dir = .right)
    (hdecode : decodeChar (s.grid.get s.pc.1 s.pc.2) = .printChar)
    (hx : s.pc.1 + 1 < w) (hy : s.pc.2 < h) :
    step (rotateCWState s) = some (rotateCWState (stepState s .printChar)) := by
  have hpc : s.pc.1 < w := by omega
  have hdecode' : decodeChar ((rotateCWState s).grid.get
      (rotateCWState s).pc.1 (rotateCWState s).pc.2) = .printChar := by
    change decodeChar ((Grid.rotateCW s.grid).get (h - 1 - s.pc.2) s.pc.1) = .printChar
    rw [Grid.get_rotateCW s.grid s.pc.1 s.pc.2 hpc hy]
    exact hdecode
  unfold step
  dsimp only
  have hm' : (rotateCWState s).stringMode = false := hm
  rw [hdecode', hm']
  have hrotx : h - 1 - s.pc.2 < h := by omega
  simp [rotateCWState, rotateCWDirection, stepState, stepPos, hdir,
    Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy, Nat.mod_eq_of_lt hrotx]

/-- Clockwise rotation maps a right-moving subtraction step to a down-moving
    subtraction step before either playfield boundary. -/
theorem step_rotateCWState_sub_right (s : State w h)
    (hm : s.stringMode = false) (hdir : s.dir = .right)
    (hdecode : decodeChar (s.grid.get s.pc.1 s.pc.2) = .sub)
    (hx : s.pc.1 + 1 < w) (hy : s.pc.2 < h) :
    step (rotateCWState s) = some (rotateCWState (stepState s .sub)) := by
  have hpc : s.pc.1 < w := by omega
  have hdecode' : decodeChar ((rotateCWState s).grid.get
      (rotateCWState s).pc.1 (rotateCWState s).pc.2) = .sub := by
    change decodeChar ((Grid.rotateCW s.grid).get (h - 1 - s.pc.2) s.pc.1) = .sub
    rw [Grid.get_rotateCW s.grid s.pc.1 s.pc.2 hpc hy]
    exact hdecode
  unfold step
  dsimp only
  have hm' : (rotateCWState s).stringMode = false := hm
  rw [hdecode', hm']
  have hrotx : h - 1 - s.pc.2 < h := by omega
  simp [rotateCWState, rotateCWDirection, stepState, stepPos, hdir,
    Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy, Nat.mod_eq_of_lt hrotx]

/-- Clockwise rotation maps a right-moving multiplication step to a down-moving
    multiplication step before either playfield boundary. -/
theorem step_rotateCWState_mul_right (s : State w h)
    (hm : s.stringMode = false) (hdir : s.dir = .right)
    (hdecode : decodeChar (s.grid.get s.pc.1 s.pc.2) = .mul)
    (hx : s.pc.1 + 1 < w) (hy : s.pc.2 < h) :
    step (rotateCWState s) = some (rotateCWState (stepState s .mul)) := by
  have hpc : s.pc.1 < w := by omega
  have hdecode' : decodeChar ((rotateCWState s).grid.get
      (rotateCWState s).pc.1 (rotateCWState s).pc.2) = .mul := by
    change decodeChar ((Grid.rotateCW s.grid).get (h - 1 - s.pc.2) s.pc.1) = .mul
    rw [Grid.get_rotateCW s.grid s.pc.1 s.pc.2 hpc hy]
    exact hdecode
  unfold step
  dsimp only
  have hm' : (rotateCWState s).stringMode = false := hm
  rw [hdecode', hm']
  have hrotx : h - 1 - s.pc.2 < h := by omega
  simp [rotateCWState, rotateCWDirection, stepState, stepPos, hdir,
    Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy, Nat.mod_eq_of_lt hrotx]

/-- Clockwise rotation maps a right-moving division step to a down-moving
    division step before either playfield boundary. -/
theorem step_rotateCWState_div_right (s : State w h)
    (hm : s.stringMode = false) (hdir : s.dir = .right)
    (hdecode : decodeChar (s.grid.get s.pc.1 s.pc.2) = .div)
    (hx : s.pc.1 + 1 < w) (hy : s.pc.2 < h) :
    step (rotateCWState s) = some (rotateCWState (stepState s .div)) := by
  have hpc : s.pc.1 < w := by omega
  have hdecode' : decodeChar ((rotateCWState s).grid.get
      (rotateCWState s).pc.1 (rotateCWState s).pc.2) = .div := by
    change decodeChar ((Grid.rotateCW s.grid).get (h - 1 - s.pc.2) s.pc.1) = .div
    rw [Grid.get_rotateCW s.grid s.pc.1 s.pc.2 hpc hy]
    exact hdecode
  unfold step
  dsimp only
  have hm' : (rotateCWState s).stringMode = false := hm
  rw [hdecode', hm']
  have hrotx : h - 1 - s.pc.2 < h := by omega
  simp [rotateCWState, rotateCWDirection, stepState, stepPos, hdir,
    Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy, Nat.mod_eq_of_lt hrotx]

/-- Clockwise rotation maps a right-moving modulo step to a down-moving modulo
    step before either playfield boundary. -/
theorem step_rotateCWState_mod_right (s : State w h)
    (hm : s.stringMode = false) (hdir : s.dir = .right)
    (hdecode : decodeChar (s.grid.get s.pc.1 s.pc.2) = .mod)
    (hx : s.pc.1 + 1 < w) (hy : s.pc.2 < h) :
    step (rotateCWState s) = some (rotateCWState (stepState s .mod)) := by
  have hpc : s.pc.1 < w := by omega
  have hdecode' : decodeChar ((rotateCWState s).grid.get
      (rotateCWState s).pc.1 (rotateCWState s).pc.2) = .mod := by
    change decodeChar ((Grid.rotateCW s.grid).get (h - 1 - s.pc.2) s.pc.1) = .mod
    rw [Grid.get_rotateCW s.grid s.pc.1 s.pc.2 hpc hy]
    exact hdecode
  unfold step
  dsimp only
  have hm' : (rotateCWState s).stringMode = false := hm
  rw [hdecode', hm']
  have hrotx : h - 1 - s.pc.2 < h := by omega
  simp [rotateCWState, rotateCWDirection, stepState, stepPos, hdir,
    Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy, Nat.mod_eq_of_lt hrotx]

/-- Clockwise rotation maps a right-moving logical-not step to a down-moving
    logical-not step before either playfield boundary. -/
theorem step_rotateCWState_not_right (s : State w h)
    (hm : s.stringMode = false) (hdir : s.dir = .right)
    (hdecode : decodeChar (s.grid.get s.pc.1 s.pc.2) = .not)
    (hx : s.pc.1 + 1 < w) (hy : s.pc.2 < h) :
    step (rotateCWState s) = some (rotateCWState (stepState s .not)) := by
  have hpc : s.pc.1 < w := by omega
  have hdecode' : decodeChar ((rotateCWState s).grid.get
      (rotateCWState s).pc.1 (rotateCWState s).pc.2) = .not := by
    change decodeChar ((Grid.rotateCW s.grid).get (h - 1 - s.pc.2) s.pc.1) = .not
    rw [Grid.get_rotateCW s.grid s.pc.1 s.pc.2 hpc hy]
    exact hdecode
  unfold step
  dsimp only
  have hm' : (rotateCWState s).stringMode = false := hm
  rw [hdecode', hm']
  have hrotx : h - 1 - s.pc.2 < h := by omega
  simp [rotateCWState, rotateCWDirection, stepState, stepPos, hdir,
    Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy, Nat.mod_eq_of_lt hrotx]

/-- Clockwise rotation maps a right-moving comparison step to a down-moving
    comparison step before either playfield boundary. -/
theorem step_rotateCWState_greater_right (s : State w h)
    (hm : s.stringMode = false) (hdir : s.dir = .right)
    (hdecode : decodeChar (s.grid.get s.pc.1 s.pc.2) = .greater)
    (hx : s.pc.1 + 1 < w) (hy : s.pc.2 < h) :
    step (rotateCWState s) = some (rotateCWState (stepState s .greater)) := by
  have hpc : s.pc.1 < w := by omega
  have hdecode' : decodeChar ((rotateCWState s).grid.get
      (rotateCWState s).pc.1 (rotateCWState s).pc.2) = .greater := by
    change decodeChar ((Grid.rotateCW s.grid).get (h - 1 - s.pc.2) s.pc.1) = .greater
    rw [Grid.get_rotateCW s.grid s.pc.1 s.pc.2 hpc hy]
    exact hdecode
  unfold step
  dsimp only
  have hm' : (rotateCWState s).stringMode = false := hm
  rw [hdecode', hm']
  have hrotx : h - 1 - s.pc.2 < h := by omega
  simp [rotateCWState, rotateCWDirection, stepState, stepPos, hdir,
    Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy, Nat.mod_eq_of_lt hrotx]

/-- Clockwise rotation maps a right-moving string-mode step to a down-moving
    string-mode step before either playfield boundary. -/
theorem step_rotateCWState_stringMode_right (s : State w h)
    (hm : s.stringMode = false) (hdir : s.dir = .right)
    (hdecode : decodeChar (s.grid.get s.pc.1 s.pc.2) = .stringMode)
    (hx : s.pc.1 + 1 < w) (hy : s.pc.2 < h) :
    step (rotateCWState s) = some (rotateCWState (stepState s .stringMode)) := by
  have hpc : s.pc.1 < w := by omega
  have hdecode' : decodeChar ((rotateCWState s).grid.get
      (rotateCWState s).pc.1 (rotateCWState s).pc.2) = .stringMode := by
    change decodeChar ((Grid.rotateCW s.grid).get (h - 1 - s.pc.2) s.pc.1) = .stringMode
    rw [Grid.get_rotateCW s.grid s.pc.1 s.pc.2 hpc hy]
    exact hdecode
  unfold step
  dsimp only
  have hm' : (rotateCWState s).stringMode = false := hm
  rw [hdecode', hm']
  have hrotx : h - 1 - s.pc.2 < h := by omega
  simp [rotateCWState, rotateCWDirection, stepState, stepPos, hdir,
    Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy, Nat.mod_eq_of_lt hrotx]

/-- Clockwise rotation maps a right-moving random step to a down-moving random
    step before either playfield boundary. -/
theorem step_rotateCWState_random_right (s : State w h)
    (hm : s.stringMode = false) (hdir : s.dir = .right)
    (hdecode : decodeChar (s.grid.get s.pc.1 s.pc.2) = .random)
    (hx : s.pc.1 + 1 < w) (hy : s.pc.2 < h) :
    step (rotateCWState s) = some (rotateCWState (stepState s .random)) := by
  have hpc : s.pc.1 < w := by omega
  have hdecode' : decodeChar ((rotateCWState s).grid.get
      (rotateCWState s).pc.1 (rotateCWState s).pc.2) = .random := by
    change decodeChar ((Grid.rotateCW s.grid).get (h - 1 - s.pc.2) s.pc.1) = .random
    rw [Grid.get_rotateCW s.grid s.pc.1 s.pc.2 hpc hy]
    exact hdecode
  unfold step
  dsimp only
  have hm' : (rotateCWState s).stringMode = false := hm
  rw [hdecode', hm']
  have hrotx : h - 1 - s.pc.2 < h := by omega
  simp [rotateCWState, rotateCWDirection, stepState, stepPos, hdir,
    Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy, Nat.mod_eq_of_lt hrotx]

/-- Clockwise rotation maps a right-moving integer-input step to a down-moving
    integer-input step before either playfield boundary. -/
theorem step_rotateCWState_inputInt_right (s : State w h)
    (hm : s.stringMode = false) (hdir : s.dir = .right)
    (hdecode : decodeChar (s.grid.get s.pc.1 s.pc.2) = .inputInt)
    (hx : s.pc.1 + 1 < w) (hy : s.pc.2 < h) :
    step (rotateCWState s) = some (rotateCWState (stepState s .inputInt)) := by
  have hpc : s.pc.1 < w := by omega
  have hdecode' : decodeChar ((rotateCWState s).grid.get
      (rotateCWState s).pc.1 (rotateCWState s).pc.2) = .inputInt := by
    change decodeChar ((Grid.rotateCW s.grid).get (h - 1 - s.pc.2) s.pc.1) = .inputInt
    rw [Grid.get_rotateCW s.grid s.pc.1 s.pc.2 hpc hy]
    exact hdecode
  unfold step
  dsimp only
  have hm' : (rotateCWState s).stringMode = false := hm
  rw [hdecode', hm']
  have hrotx : h - 1 - s.pc.2 < h := by omega
  simp [rotateCWState, rotateCWDirection, stepState, stepPos, hdir,
    Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy, Nat.mod_eq_of_lt hrotx]

/-- Clockwise rotation maps a right-moving character-input step to a down-moving
    character-input step before either playfield boundary. -/
theorem step_rotateCWState_inputChar_right (s : State w h)
    (hm : s.stringMode = false) (hdir : s.dir = .right)
    (hdecode : decodeChar (s.grid.get s.pc.1 s.pc.2) = .inputChar)
    (hx : s.pc.1 + 1 < w) (hy : s.pc.2 < h) :
    step (rotateCWState s) = some (rotateCWState (stepState s .inputChar)) := by
  have hpc : s.pc.1 < w := by omega
  have hdecode' : decodeChar ((rotateCWState s).grid.get
      (rotateCWState s).pc.1 (rotateCWState s).pc.2) = .inputChar := by
    change decodeChar ((Grid.rotateCW s.grid).get (h - 1 - s.pc.2) s.pc.1) = .inputChar
    rw [Grid.get_rotateCW s.grid s.pc.1 s.pc.2 hpc hy]
    exact hdecode
  unfold step
  dsimp only
  have hm' : (rotateCWState s).stringMode = false := hm
  rw [hdecode', hm']
  have hrotx : h - 1 - s.pc.2 < h := by omega
  cases h : s.input with
  | nil =>
      simp [rotateCWState, rotateCWDirection, stepState, stepPos, hdir, h,
        Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy, Nat.mod_eq_of_lt hrotx]
  | cons c rest =>
      simp [rotateCWState, rotateCWDirection, stepState, stepPos, hdir, h,
        Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy, Nat.mod_eq_of_lt hrotx]

/-- Clockwise rotation maps a right-moving trampoline step to a down-moving
    trampoline step before either playfield boundary, with room for two
    horizontal cells. -/
theorem step_rotateCWState_trampoline_right (s : State w h)
    (hm : s.stringMode = false) (hdir : s.dir = .right)
    (hdecode : decodeChar (s.grid.get s.pc.1 s.pc.2) = .trampoline)
    (hx : s.pc.1 + 2 < w) (hy : s.pc.2 < h) :
    step (rotateCWState s) = some (rotateCWState (stepState s .trampoline)) := by
  have hpc : s.pc.1 < w := by omega
  have hdecode' : decodeChar ((rotateCWState s).grid.get
      (rotateCWState s).pc.1 (rotateCWState s).pc.2) = .trampoline := by
    change decodeChar ((Grid.rotateCW s.grid).get (h - 1 - s.pc.2) s.pc.1) = .trampoline
    rw [Grid.get_rotateCW s.grid s.pc.1 s.pc.2 hpc hy]
    exact hdecode
  unfold step
  dsimp only
  have hm' : (rotateCWState s).stringMode = false := hm
  rw [hdecode', hm']
  have hrotx : h - 1 - s.pc.2 < h := by omega
  have hmid : (s.pc.1 + 1) % w = s.pc.1 + 1 := by
    apply Nat.mod_eq_of_lt
    omega
  have hnew : (s.pc.1 + 2) % w = s.pc.1 + 2 := Nat.mod_eq_of_lt hx
  simp [rotateCWState, rotateCWDirection, stepState, stepPos, hdir,
    hmid, hnew, Nat.mod_eq_of_lt hy, Nat.mod_eq_of_lt hrotx]

/-- A right-moving no-op step commutes with leading-space state padding before
    the original playfield boundary. -/
theorem step_prependSpaceState_nop_right (s : State w h)
    (hdir : s.dir = .right) (hm : s.stringMode = false)
    (hcell : s.grid.get s.pc.1 s.pc.2 = ' ')
    (hx : s.pc.1 + 1 < w) :
    step (prependSpaceState s) =
      some (prependSpaceState { s with pc := stepPos w h .right s.pc }) := by
  have hpc : s.pc.1 < w := by omega
  have hcell' : (prependSpaceState s).grid.get
      (prependSpaceState s).pc.1 (prependSpaceState s).pc.2 = ' ' := by
    rw [prependSpaceState_cell s hpc]
    exact hcell
  rw [step_nop (prependSpaceState s) hm hcell']
  simp [prependSpaceState, hdir, stepPos, Nat.mod_eq_of_lt hx,
    Nat.mod_eq_of_lt (Nat.succ_lt_succ hx)]

/-- A right-moving no-op step commutes with `k`-cell leading-space padding
    before the original playfield boundary. -/
theorem step_prependSpacesState_nop_right (s : State w h) (k : ℕ)
    (hdir : s.dir = .right) (hm : s.stringMode = false)
    (hcell : s.grid.get s.pc.1 s.pc.2 = ' ')
    (hx : s.pc.1 + 1 < w) :
    step (prependSpacesState s k) = some (prependSpacesState
      { s with pc := stepPos w h .right s.pc } k) := by
  have hpc : s.pc.1 < w := by omega
  have hcell' : (prependSpacesState s k).grid.get
      (prependSpacesState s k).pc.1 (prependSpacesState s k).pc.2 = ' ' := by
    rw [prependSpacesState_cell s k hpc]
    exact hcell
  rw [step_nop (prependSpacesState s k) hm hcell']
  have hold : (s.pc.1 + 1) % w = s.pc.1 + 1 :=
    Nat.mod_eq_of_lt hx
  have hnew : (s.pc.1 + k + 1) % (w + k) = s.pc.1 + k + 1 := by
    apply Nat.mod_eq_of_lt
    omega
  simp [prependSpacesState, hdir, stepPos, hold, hnew]
  omega

/-- A right-moving push step commutes with `k`-cell leading-space padding
    before the original playfield boundary. -/
theorem step_prependSpacesState_push_right (s : State w h) (k : ℕ) (n : Int)
    (hdir : s.dir = .right) (hm : s.stringMode = false)
    (hdecode : decodeChar (s.grid.get s.pc.1 s.pc.2) = .push n)
    (hx : s.pc.1 + 1 < w) :
    step (prependSpacesState s k) = some (prependSpacesState
      (stepState s (.push n)) k) := by
  have hpc : s.pc.1 < w := by omega
  have hcell : (prependSpacesState s k).grid.get
      (prependSpacesState s k).pc.1 (prependSpacesState s k).pc.2 =
      s.grid.get s.pc.1 s.pc.2 := prependSpacesState_cell s k hpc
  have hdecode' : decodeChar ((prependSpacesState s k).grid.get
      (prependSpacesState s k).pc.1 (prependSpacesState s k).pc.2) = .push n := by
    rw [hcell]
    exact hdecode
  unfold step
  dsimp only
  have hm' : (prependSpacesState s k).stringMode = false := hm
  rw [hdecode', hm']
  have hold : (s.pc.1 + 1) % w = s.pc.1 + 1 := Nat.mod_eq_of_lt hx
  have hnew : (s.pc.1 + k + 1) % (w + k) = s.pc.1 + k + 1 := by
    apply Nat.mod_eq_of_lt
    omega
  simp [prependSpacesState, stepState, hdir, stepPos, hold, hnew]
  omega

/-- A right-moving addition step commutes with `k`-cell leading-space padding
    before the original playfield boundary. -/
theorem step_prependSpacesState_add_right (s : State w h) (k : ℕ)
    (hdir : s.dir = .right) (hm : s.stringMode = false)
    (hdecode : decodeChar (s.grid.get s.pc.1 s.pc.2) = .add)
    (hx : s.pc.1 + 1 < w) :
    step (prependSpacesState s k) = some (prependSpacesState
      (stepState s .add) k) := by
  have hpc : s.pc.1 < w := by omega
  have hcell : (prependSpacesState s k).grid.get
      (prependSpacesState s k).pc.1 (prependSpacesState s k).pc.2 =
      s.grid.get s.pc.1 s.pc.2 := prependSpacesState_cell s k hpc
  have hdecode' : decodeChar ((prependSpacesState s k).grid.get
      (prependSpacesState s k).pc.1 (prependSpacesState s k).pc.2) = .add := by
    rw [hcell]
    exact hdecode
  unfold step
  dsimp only
  have hm' : (prependSpacesState s k).stringMode = false := hm
  rw [hdecode', hm']
  have hold : (s.pc.1 + 1) % w = s.pc.1 + 1 := Nat.mod_eq_of_lt hx
  have hnew : (s.pc.1 + k + 1) % (w + k) = s.pc.1 + k + 1 := by
    apply Nat.mod_eq_of_lt
    omega
  simp [prependSpacesState, stepState, hdir, stepPos, hold, hnew]
  omega

/-- A right-moving integer-output step commutes with `k`-cell leading-space
    padding before the original playfield boundary. -/
theorem step_prependSpacesState_printInt_right (s : State w h) (k : ℕ)
    (hdir : s.dir = .right) (hm : s.stringMode = false)
    (hdecode : decodeChar (s.grid.get s.pc.1 s.pc.2) = .printInt)
    (hx : s.pc.1 + 1 < w) :
    step (prependSpacesState s k) = some (prependSpacesState
      (stepState s .printInt) k) := by
  have hpc : s.pc.1 < w := by omega
  have hcell : (prependSpacesState s k).grid.get
      (prependSpacesState s k).pc.1 (prependSpacesState s k).pc.2 =
      s.grid.get s.pc.1 s.pc.2 := prependSpacesState_cell s k hpc
  have hdecode' : decodeChar ((prependSpacesState s k).grid.get
      (prependSpacesState s k).pc.1 (prependSpacesState s k).pc.2) = .printInt := by
    rw [hcell]
    exact hdecode
  unfold step
  dsimp only
  have hm' : (prependSpacesState s k).stringMode = false := hm
  rw [hdecode', hm']
  have hold : (s.pc.1 + 1) % w = s.pc.1 + 1 := Nat.mod_eq_of_lt hx
  have hnew : (s.pc.1 + k + 1) % (w + k) = s.pc.1 + k + 1 := by
    apply Nat.mod_eq_of_lt
    omega
  simp [prependSpacesState, stepState, hdir, stepPos, hold, hnew]
  omega

/-- A right-moving halt step commutes with `k`-cell leading-space padding by
    halting on both sides. -/
theorem step_prependSpacesState_halt_right (s : State w h) (k : ℕ)
    (hm : s.stringMode = false)
    (hdecode : decodeChar (s.grid.get s.pc.1 s.pc.2) = .halt)
    (hx : s.pc.1 + 1 < w) : step (prependSpacesState s k) = none := by
  have hpc : s.pc.1 < w := by omega
  have hcell : (prependSpacesState s k).grid.get
      (prependSpacesState s k).pc.1 (prependSpacesState s k).pc.2 =
      s.grid.get s.pc.1 s.pc.2 := prependSpacesState_cell s k hpc
  have hdecode' : decodeChar ((prependSpacesState s k).grid.get
      (prependSpacesState s k).pc.1 (prependSpacesState s k).pc.2) = .halt := by
    rw [hcell]
    exact hdecode
  unfold step
  dsimp only
  have hm' : (prependSpacesState s k).stringMode = false := hm
  rw [hdecode', hm']

/-- A right-moving push step commutes with leading-space state padding before
    the original playfield boundary. -/
theorem step_prependSpaceState_push_right (s : State w h) (n : Int)
    (hdir : s.dir = .right) (hm : s.stringMode = false)
    (hdecode : decodeChar (s.grid.get s.pc.1 s.pc.2) = .push n)
    (hx : s.pc.1 + 1 < w) :
    step (prependSpaceState s) = some (prependSpaceState
      { s with stack := Stack.push s.stack n, pc := stepPos w h .right s.pc }) := by
  have hpc : s.pc.1 < w := by omega
  have hcell : (prependSpaceState s).grid.get
      (prependSpaceState s).pc.1 (prependSpaceState s).pc.2 =
      s.grid.get s.pc.1 s.pc.2 := prependSpaceState_cell s hpc
  have hdecode' : decodeChar ((prependSpaceState s).grid.get
      (prependSpaceState s).pc.1 (prependSpaceState s).pc.2) = .push n := by
    rw [hcell]
    exact hdecode
  unfold step
  dsimp only
  have hm' : (prependSpaceState s).stringMode = false := hm
  rw [hdecode']
  rw [hm']
  simp [prependSpaceState, stepState, hdir, stepPos,
    Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt (Nat.succ_lt_succ hx)]

/-- A right-moving addition step commutes with leading-space state padding
    before the original playfield boundary. -/
theorem step_prependSpaceState_add_right (s : State w h)
    (hdir : s.dir = .right) (hm : s.stringMode = false)
    (hdecode : decodeChar (s.grid.get s.pc.1 s.pc.2) = .add)
    (hx : s.pc.1 + 1 < w) :
    step (prependSpaceState s) = some (prependSpaceState (stepState s .add)) := by
  have hpc : s.pc.1 < w := by omega
  have hcell : (prependSpaceState s).grid.get
      (prependSpaceState s).pc.1 (prependSpaceState s).pc.2 =
      s.grid.get s.pc.1 s.pc.2 := prependSpaceState_cell s hpc
  have hdecode' : decodeChar ((prependSpaceState s).grid.get
      (prependSpaceState s).pc.1 (prependSpaceState s).pc.2) = .add := by
    rw [hcell]
    exact hdecode
  unfold step
  dsimp only
  have hm' : (prependSpaceState s).stringMode = false := hm
  rw [hdecode', hm']
  simp [prependSpaceState, stepState, hdir, stepPos,
    Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt (Nat.succ_lt_succ hx)]

/-- A right-moving integer-output step commutes with leading-space state
    padding before the original playfield boundary. -/
theorem step_prependSpaceState_printInt_right (s : State w h)
    (hdir : s.dir = .right) (hm : s.stringMode = false)
    (hdecode : decodeChar (s.grid.get s.pc.1 s.pc.2) = .printInt)
    (hx : s.pc.1 + 1 < w) :
    step (prependSpaceState s) =
      some (prependSpaceState (stepState s .printInt)) := by
  have hpc : s.pc.1 < w := by omega
  have hcell : (prependSpaceState s).grid.get
      (prependSpaceState s).pc.1 (prependSpaceState s).pc.2 =
      s.grid.get s.pc.1 s.pc.2 := prependSpaceState_cell s hpc
  have hdecode' : decodeChar ((prependSpaceState s).grid.get
      (prependSpaceState s).pc.1 (prependSpaceState s).pc.2) = .printInt := by
    rw [hcell]
    exact hdecode
  unfold step
  dsimp only
  have hm' : (prependSpaceState s).stringMode = false := hm
  rw [hdecode', hm']
  simp [prependSpaceState, stepState, hdir, stepPos,
    Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt (Nat.succ_lt_succ hx)]

/-- A right-moving halt step commutes with leading-space state padding by
    halting on both sides. -/
theorem step_prependSpaceState_halt_right (s : State w h)
    (hm : s.stringMode = false)
    (hdecode : decodeChar (s.grid.get s.pc.1 s.pc.2) = .halt)
    (hx : s.pc.1 + 1 < w) : step (prependSpaceState s) = none := by
  have hpc : s.pc.1 < w := by omega
  have hcell : (prependSpaceState s).grid.get
      (prependSpaceState s).pc.1 (prependSpaceState s).pc.2 =
      s.grid.get s.pc.1 s.pc.2 := prependSpaceState_cell s hpc
  have hdecode' : decodeChar ((prependSpaceState s).grid.get
      (prependSpaceState s).pc.1 (prependSpaceState s).pc.2) = .halt := by
    rw [hcell]
    exact hdecode
  unfold step
  dsimp only
  have hm' : (prependSpaceState s).stringMode = false := hm
  rw [hdecode', hm']

/-- Relate optional run results under a state simulation. -/
def option_state_related (R : State w h → State w' h' → Prop) :
    Option (State w h) → Option (State w' h') → Prop
  | none, none => True
  | some s, some t => R s t
  | _, _ => False

/-- A state simulation lifts to every finite deterministic run. -/
theorem run_related_of_state_simulation
    {R : State w h → State w' h' → Prop} (hR : state_simulation R)
    {s : State w h} {t : State w' h'} (hst : R s t) (n : ℕ) :
    option_state_related R (run n s) (run n t) := by
  induction n generalizing s t with
  | zero => exact hst
  | succ n ih =>
      rcases hs : run n s with _ | sₙ
      · rcases ht : run n t with _ | tₙ
        · rw [run, hs, run, ht]
          simp [option_state_related]
        · have hrel := ih hst
          rw [hs, ht] at hrel
          cases hrel
      · rcases ht : run n t with _ | tₙ
        · have hrel := ih hst
          rw [hs, ht] at hrel
          cases hrel
        · have hstₙ : R sₙ tₙ := by
            have hrel := ih hst
            rw [hs, ht] at hrel
            exact hrel
          cases hstep : step sₙ with
          | none =>
              have hstep' : step tₙ = none := (hR sₙ tₙ hstₙ).2.1.mp hstep
              rw [run, hs, run, ht]
              simp [hstep, hstep', option_state_related]
          | some s' =>
              obtain ⟨t', hstep', hrel'⟩ :=
                (hR sₙ tₙ hstₙ).2.2.1 s' hstep
              rw [run, hs, run, ht]
              simpa [hstep, hstep', option_state_related] using hrel'

/-- A state simulation gives equal observations at every deterministic run
    bound. -/
theorem run_observations_of_state_simulation
    {R : State w h → State w' h' → Prop} (hR : state_simulation R)
    {s : State w h} {t : State w' h'} (hst : R s t) (n : ℕ) :
    observe (run n s) = observe (run n t) := by
  have hrel := run_related_of_state_simulation hR hst n
  rcases hs : run n s with _ | s'
  · rcases ht : run n t with _ | t'
    · rfl
    · rw [hs, ht] at hrel
      cases hrel
  · rcases ht : run n t with _ | t'
    · rw [hs, ht] at hrel
      cases hrel
    · rw [hs, ht] at hrel
      exact state_simulation_observe hR hrel

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

/-- Programs with identical initial observations are ordered-trace equivalent
    when `p` halts after its first step and `q` does the same after one
    leading no-op step. -/
theorem ordered_trace_equiv_halt_shift {p q : Program w h}
    (hp : ∀ n, observe (run (n + 1) (State.init p)) = none)
    (hq : ∀ n, observe (run (n + 2) (State.init q)) = none)
    (h₀ : observe (run 0 (State.init p)) = observe (run 0 (State.init q)))
    (h₁ : observe (run 0 (State.init p)) = observe (run 1 (State.init q))) :
    ordered_trace_equiv p q := by
  let f : ℕ → ℕ := fun n => if n = 0 then 0 else 2
  let g : ℕ → ℕ := fun n => if n ≤ 1 then 0 else 1
  refine ⟨f, g, ?_, ?_, ?_, ?_⟩
  · intro a b hab
    simp only [f]
    by_cases ha : a = 0 <;> by_cases hb : b = 0 <;> simp [ha, hb] at *
  · intro a b hab
    simp only [g]
    by_cases ha : a ≤ 1
    · simp [ha]
    · have hb : ¬ b ≤ 1 := by
        intro hb
        exact ha (Nat.le_trans hab hb)
      simp [ha, hb]
  · intro n
    cases n with
    | zero => exact h₀
    | succ n =>
        simp only [f]
        rw [if_neg (Nat.succ_ne_zero n), hp n, hq 0]
  · intro n
    cases n with
    | zero => exact h₀.symm
    | succ n =>
        cases n with
        | zero => exact h₁.symm
        | succ n =>
            simp only [g]
            rw [if_neg]
            · rw [hq n, hp 0]
            · omega

/-- A one-step prefix preserves ordered trace equivalence when the prefixed
    program's observations are shifted by exactly one step. -/
theorem ordered_trace_equiv_one_step_prefix {p q : Program w h}
    (h₀ : observe (run 0 (State.init p)) = observe (run 0 (State.init q)))
    (hshift : ∀ n, observe (run n (State.init p)) =
      observe (run (n + 1) (State.init q))) :
    ordered_trace_equiv p q := by
  refine ⟨Nat.succ, Nat.pred, ?_, ?_, ?_, ?_⟩
  · intro a b hab
    exact Nat.succ_le_succ hab
  · intro a b hab
    exact Nat.pred_le_pred hab
  · intro n
    exact hshift n
  · intro n
    cases n with
    | zero => exact h₀.symm
    | succ n => exact (hshift n).symm

/-- A one-step prefix theorem for programs with different playfield dimensions. -/
theorem ordered_trace_equiv_between_one_step_prefix
    {p : Program w h} {q : Program w' h'}
    (h₀ : observe (run 0 (State.init p)) = observe (run 0 (State.init q)))
    (hshift : ∀ n, observe (run n (State.init p)) =
      observe (run (n + 1) (State.init q))) :
    ordered_trace_equiv_between p q := by
  refine ⟨Nat.succ, Nat.pred, ?_, ?_, ?_, ?_⟩
  · intro a b hab
    exact Nat.succ_le_succ hab
  · intro a b hab
    exact Nat.pred_le_pred hab
  · intro n
    exact hshift n
  · intro n
    cases n with
    | zero => exact h₀.symm
    | succ n => exact (hshift n).symm

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

/-- The state reached by executing a non-string-mode space. -/
def nop_successor (s : State w h) : State w h :=
  { s with pc := stepPos w h s.dir s.pc }

/-- A non-string-mode space steps to `nop_successor`. -/
theorem step_nop_successor (s : State w h) (hm : s.stringMode = false)
    (hcell : s.grid.get s.pc.1 s.pc.2 = ' ') :
    step s = some (nop_successor s) := by
  rw [step_nop s hm hcell]
  rfl

/-- Running a state for one step and then `n` more steps is the same as
    starting from the state reached by that first step. -/
theorem run_succ_eq_run_from_step {s s' : State w h} (hstep : step s = some s')
    (n : ℕ) : run (n + 1) s = run n s' := by
  induction n with
  | zero =>
      change step s = some s'
      exact hstep
  | succ n ih =>
      change (run (n + 1) s).bind step = run (n + 1) s'
      rw [ih]
      rfl

/-- A program is equivalent to the continuation reached by one first step of
    another program, then the two programs are ordered-trace equivalent. -/
theorem ordered_trace_equiv_of_step_continuation {p q : Program w h}
    (q' : State w h) (hstep : step (State.init q) = some q')
    (h₀ : observe (run 0 (State.init p)) = observe (run 0 (State.init q)))
    (hcont : ∀ n, observe (run n (State.init p)) = observe (run n q')) :
    ordered_trace_equiv p q := by
  apply ordered_trace_equiv_one_step_prefix h₀
  intro n
  rw [run_succ_eq_run_from_step hstep n]
  exact hcont n

/-- A leading space can be handled as a one-step continuation without
    repeating its successor-state proof. -/
theorem ordered_trace_equiv_of_nop_continuation {p q : Program w h}
    (hm : (State.init q).stringMode = false)
    (hcell : (State.init q).grid.get (State.init q).pc.1 (State.init q).pc.2 = ' ')
    (h₀ : observe (run 0 (State.init p)) = observe (run 0 (State.init q)))
    (hcont : ∀ n, observe (run n (State.init p)) =
      observe (run n (nop_successor (State.init q)))) :
    ordered_trace_equiv p q := by
  apply ordered_trace_equiv_of_step_continuation (nop_successor (State.init q))
    (step_nop_successor (State.init q) hm hcell) h₀
  exact hcont

/-- Two states have equal observations at every step when their first `k`
    checkpoints agree and both runs remain halted afterward. -/
theorem run_observe_eq_of_finite_prefix (s t : State w h) (k : ℕ)
    (hs : ∀ d, run (k + d) s = none)
    (ht : ∀ d, run (k + d) t = none)
    (hobs : ∀ n, n < k → observe (run n s) = observe (run n t)) :
    ∀ n, observe (run n s) = observe (run n t) := by
  intro n
  by_cases hnk : n < k
  · exact hobs n hnk
  · have hkn : k ≤ n := Nat.le_of_not_gt hnk
    rcases Nat.le.dest hkn with ⟨d, rfl⟩
    rw [hs d, ht d]

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
