/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanFunge.Theory.Completeness.LayoutSimulationStepRun
import LeanFunge.Theory.Run.Relational
import LeanFunge.Theory.Step
import Mathlib.Tactic

/-!
# The Machine Run Is Simulated

The machine run is simulated by the playfield run: the playfield reaches the
successor block with the successor state's encoding, or stops when the machine
stops. The universality corollaries project the simulation to the pointer
position and stack, and lift halting from the machine to the playfield.

## Theorems

* `sim_run`: The machine run is simulated by the playfield run.
* `simulation_map`: The playfield run reflects the machine run's positions and
  encodings.
* `simulation_halts`: If the machine halts, the playfield halts.
-/

namespace LeanFunge

namespace Completeness

open CMInstr

/-- The machine run is simulated by the playfield run: the playfield reaches
    the successor block with the successor state's encoding, or stops. -/
theorem sim_run (prog : CMProgram) (hwellPlaced : wellPlaced prog) (s₀ : CMState)
    (hs₀ : s₀.pc < prog.length) (n : ℕ) :
    ∃ m, run m (playfieldStart prog s₀)
        = (CMInstr.run prog n s₀).map (fun s' => afterState prog (playfieldStart prog s₀) s')
      ∧ ∀ s', CMInstr.run prog n s₀ = some s' → s'.pc < prog.length := by
  induction n with
  | zero =>
      refine ⟨0, ?_, ?_⟩
      · rw [show run 0 (playfieldStart prog s₀) = some (playfieldStart prog s₀) by rfl]
        rw [show CMInstr.run prog 0 s₀ = some s₀ by rfl]
        simp [playfieldStart, afterState, blockEntry] -- no_squeeze: simulation
      · intro s' h
        have h' : s' = s₀ := by
          simpa [CMInstr.run] using h.symm -- no_squeeze: simulation
        subst s'
        exact hs₀
  | succ n ih =>
      rcases ih with ⟨mₙ, hrunₙ, hbₙ⟩
      by_cases hnone : CMInstr.run prog n s₀ = none
      · refine ⟨mₙ, ?_, ?_⟩
        · rw [hrunₙ, CMInstr.run_succ, hnone]
          simp -- no_squeeze: simulation
        · intro s' h
          rw [CMInstr.run_succ, hnone] at h
          simp at h -- no_squeeze: simulation
      · have hsome : ∃ sₙ, CMInstr.run prog n s₀ = some sₙ := by
          by_contra h
          have hnone' : CMInstr.run prog n s₀ = none := by
            cases h2 : CMInstr.run prog n s₀ with
            | none => rfl
            | some sₙ => exact False.elim (h ⟨sₙ, h2⟩)
          exact hnone hnone'
        rcases hsome with ⟨sₙ, hrunₙ'⟩
        have hsm : (playfieldStart prog s₀).stringMode = false := rfl
        have hgrid : (playfieldStart prog s₀).grid = playfieldOf prog := rfl
        have hfall : sₙ.pc + 1 < prog.length ∨ CMInstr.instrAt prog sₙ.pc = .halt :=
          Or.symm (hwellPlaced.2 sₙ.pc (hbₙ sₙ hrunₙ'))
        have hstep := sim_step prog (hwellPlaced.1) sₙ (hbₙ sₙ hrunₙ') hfall
          (afterState prog (playfieldStart prog s₀) sₙ) hsm rfl hgrid rfl
        cases hstep2 : CMInstr.step prog sₙ with
        | none =>
            have hnone' : CMInstr.step prog sₙ = none := hstep2
            have hrun2 : run 2 (afterState prog (playfieldStart prog s₀) sₙ) = none := by
              simpa [hnone'] using hstep -- no_squeeze: simulation
            have hreach : run mₙ (playfieldStart prog s₀) = some (afterState prog (playfieldStart prog s₀) sₙ) := by
              rw [hrunₙ, hrunₙ']
              simp -- no_squeeze: simulation
            refine ⟨mₙ + 2, ?_, ?_⟩
            · have hcomp : run (mₙ + 2) (playfieldStart prog s₀) = none := by
                exact run_append (playfieldStart prog s₀) (afterState prog (playfieldStart prog s₀) sₙ) none mₙ 2 hreach hrun2
              rw [hcomp]
              rw [CMInstr.run_succ, hrunₙ']
              simp [hnone'] -- no_squeeze: simulation
            · intro s' h
              rw [CMInstr.run_succ, hrunₙ'] at h
              simp [hnone'] at h -- no_squeeze: simulation
        | some s' =>
            have hs' := hstep
            rw [hstep2] at hs'
            rcases hs' with ⟨n', hrun'⟩
            have hlt' : s'.pc < prog.length :=
              step_pc_lt prog hwellPlaced sₙ (hbₙ sₙ hrunₙ') s' hstep2
            have hreach : run mₙ (playfieldStart prog s₀) = some (afterState prog (playfieldStart prog s₀) sₙ) := by
              rw [hrunₙ, hrunₙ']
              simp -- no_squeeze: simulation
            refine ⟨mₙ + n', ?_, ?_⟩
            · have hcomp : run (mₙ + n') (playfieldStart prog s₀) = some (afterState prog (playfieldStart prog s₀) s') := by
                have hcomp' : run (mₙ + n') (playfieldStart prog s₀)
                    = some (afterState prog (afterState prog (playfieldStart prog s₀) sₙ) s') := by
                  exact run_append (playfieldStart prog s₀) (afterState prog (playfieldStart prog s₀) sₙ)
                    (some (afterState prog (afterState prog (playfieldStart prog s₀) sₙ) s')) mₙ n' hreach hrun'
                simpa [afterState] using hcomp' -- no_squeeze: simulation
              rw [hcomp]
              rw [CMInstr.run_succ, hrunₙ']
              simp [hstep2] -- no_squeeze: simulation
            · intro s'' h
              rw [CMInstr.run_succ, hrunₙ'] at h
              simp [hstep2] at h -- no_squeeze: simulation
              have hfin : s'' = s' := by
                simpa using h.symm -- no_squeeze: simulation
              rw [hfin]
              exact hlt'

/-- The playfield run reflects the machine run's positions and encodings. -/
theorem simulation_map (prog : CMProgram) (hwellPlaced : wellPlaced prog) (s₀ : CMState)
    (hs₀ : s₀.pc < prog.length) (n : ℕ) :
    ∃ m, (run m (playfieldStart prog s₀)).map (fun s => (s.pc, s.stack))
      = (CMInstr.run prog n s₀).map (fun s => (blockEntry prog s.pc, [encodeState s])) := by
  rcases (sim_run prog hwellPlaced s₀ hs₀ n) with ⟨m, hrun, hb⟩
  refine ⟨m, ?_⟩
  rw [hrun]
  rw [Option.map_map]
  congr 1

/-- If the machine halts, the playfield halts. -/
theorem simulation_halts (prog : CMProgram) (hwellPlaced : wellPlaced prog) (s₀ : CMState)
    (hs₀ : s₀.pc < prog.length) :
    CMInstr.halts prog s₀ → halts (playfieldStart prog s₀) := by
  intro h
  rcases h with ⟨n, hn⟩
  rcases (sim_run prog hwellPlaced s₀ hs₀ n) with ⟨m, hrun, hb⟩
  rw [hn] at hrun
  refine ⟨m, ?_⟩
  simpa using hrun -- no_squeeze: simulation

end Completeness

end LeanFunge
