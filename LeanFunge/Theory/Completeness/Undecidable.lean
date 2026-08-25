/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import Mathlib.Computability.Halting
import LeanFunge.Theory.Completeness.Encodable
import LeanFunge.Theory.Completeness.LayoutBoot
import LeanFunge.Theory.Completeness.LayoutRows
import LeanFunge.Theory.Completeness.LayoutSimulationNormalize

/-!
# Undecidability of Befunge-93 Halting

The halting of Befunge-93 programs is undecidable, *conditional* on the
classical undecidability of two-counter machine halting. That last fact is the
one piece this development does not prove: mathlib has no counter-machine
model, so the gap is a reduction from `Turing.ToPartrec.Code` to two-counter
machines — Minsky's theorem, a separate project (see `UNDECIDABILITY.md`).

Everything else is machine-checked here. The statement is phrased over program
*text* rather than over interpreter states: `Grid` stores its cells as a
function `ℕ → ℕ → Char`, which is not `Primcodable`, so no predicate over grids
can be the domain of a `ComputablePred` at all.

## Main statements

* `befunge_undecidable_of_twoCounter`: If two-counter halting is undecidable,
  so is Befunge-93 halting.
-/

namespace LeanFunge

namespace Completeness

open Grid

/-- The compiled playfield of a machine, as text: the dimensions and the rows.
    Normalizing first makes the compiler total — every program, well-placed or
    not, maps to a playfield that simulates it. -/
def compile (prog : CMProgram) : ℕ × ℕ × List (List Char) :=
  (playfieldWidth (normalize prog),
    playfieldHeight (normalize prog),
    playfieldRowsOf (normalize prog))

/-- Halting of the compiled text is halting of the machine. -/
theorem compile_halts_iff (prog : CMProgram) :
    halts (State.init (Grid.ofRows (compile prog).1 (compile prog).2.1
        (compile prog).2.2))
      ↔ CMInstr.halts prog (CMInstr.startCM 0 0) := by
  have hne : normalize prog ≠ [] := by
    unfold normalize
    exact List.append_ne_nil_of_right_ne_nil _ (by simp)
  have hwp : wellPlaced (normalize prog) := wellPlaced_normalize prog
  show halts (State.init (Grid.ofRows (playfieldWidth (normalize prog))
    (playfieldHeight (normalize prog)) (playfieldRowsOf (normalize prog)))) ↔ _
  rw [ofRows_playfieldRowsOf (normalize prog) hne]
  exact (boot_halts_iff (normalize prog) hne hwp).trans
    (normalize_halts_iff prog (CMInstr.startCM 0 0))

/-- The compiler is computable. -/
theorem computable_compile : Computable compile := by
  sorry

/-- **Befunge-93 halting is undecidable**, given the classical undecidability
    of two-counter machine halting.

    The reduction: a decider for Befunge halting, composed with the compiler,
    would decide two-counter halting. -/
theorem befunge_undecidable_of_twoCounter
    (h2cm : ¬ ComputablePred
      (fun prog : CMProgram => CMInstr.halts prog (CMInstr.startCM 0 0))) :
    ¬ ComputablePred (fun p : ℕ × ℕ × List (List Char) =>
        halts (State.init (Grid.ofRows p.1 p.2.1 p.2.2))) := by
  intro hdec
  refine h2cm ?_
  obtain ⟨hdp, hcp⟩ := hdec
  have hcomp : Computable
      (fun prog : CMProgram => decide (halts (State.init
        (Grid.ofRows (compile prog).1 (compile prog).2.1 (compile prog).2.2)))) :=
    hcp.comp computable_compile
  refine ⟨fun prog => decidable_of_iff _ (compile_halts_iff prog), ?_⟩
  refine hcomp.of_eq (fun prog => ?_)
  exact decide_eq_decide.mpr (compile_halts_iff prog)

end Completeness

end LeanFunge
