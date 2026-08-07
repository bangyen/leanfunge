/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanFunge.Theory.Completeness.LayoutSimulation
import LeanFunge.Theory.Completeness.LayoutSimulationDecz
import LeanFunge.Theory.Completeness.LayoutSimulationStep
import LeanFunge.Theory.Run.Relational
import LeanFunge.Theory.Step
import Mathlib.Tactic

/-!
# The Step Simulation

One two-counter machine step corresponds to a playfield run from a block's
entry to the successor block with the successor state's encoding, or stops for
a `halt`. The successor's program counter is shown to stay in bounds.

## Main definitions

* `afterState`: The playfield state after executing a block, at the successor
  entry with the successor's encoding.
* `playfieldStart`: The playfield start state for a two-counter machine state.

## Theorems

* `step_pc_lt`: A machine step stays within the program.
* `sim_step`: One machine step is a playfield run to the successor entry.
-/

namespace LeanFunge

namespace Completeness

open CMInstr

/-- The playfield state after executing a block: the successor entry with the
    successor state's encoding. -/
def afterState (prog : CMProgram)
    (s₀ : State (playfieldWidth prog) (playfieldHeight prog)) (s' : CMState) :
    State (playfieldWidth prog) (playfieldHeight prog) :=
  { s₀ with stack := [encodeState s'], pc := blockEntry prog s'.pc, dir := .down }

/-- The playfield start state for a two-counter machine state. -/
def playfieldStart (prog : CMProgram) (s₀ : CMState) : State (playfieldWidth prog) (playfieldHeight prog) :=
  { State.init (playfieldOf prog) with
    stack := [encodeState s₀],
    pc := blockEntry prog s₀.pc,
    dir := .down }

/-- A machine step stays within the program. -/
theorem step_pc_lt (prog : CMProgram) (hwellPlaced : wellPlaced prog) (s₀ : CMState)
    (hs₀ : s₀.pc < prog.length) :
    ∀ s', CMInstr.step prog s₀ = some s' → s'.pc < prog.length := by
  cases hget : CMInstr.instrAt prog s₀.pc with
  | inc c =>
      intro s' hstep
      have hs := CMInstr.step_inc prog s₀ c hget
      rw [hstep] at hs
      injection hs with hs'
      rw [hs']
      have hfall := (hwellPlaced.2 s₀.pc hs₀)
      rcases hfall with hh | hf
      · exfalso
        have : CMInstr.instrAt prog s₀.pc ≠ .halt := by
          rw [hget]
          intro h
          cases h
        exact this hh
      · simpa [CMInstr.incCounter, CMInstr.write, CMInstr.read] -- no_squeeze: simulation
  | decz c k =>
      intro s' hstep
      by_cases hz : CMInstr.read c s₀ = 0
      · have hs := CMInstr.step_decz_zero prog s₀ c k hget hz
        rw [hstep] at hs
        injection hs with hs'
        rw [hs']
        have hk : k < prog.length := (hwellPlaced.1) s₀.pc hs₀ c k (Or.inl (by simpa [CMInstr.instrAt] using hget)) -- no_squeeze: simulation
        simpa -- no_squeeze: simulation
      · have hs := CMInstr.step_decz_nonzero prog s₀ c k hget hz
        rw [hstep] at hs
        injection hs with hs'
        rw [hs']
        have hfall := (hwellPlaced.2 s₀.pc hs₀)
        rcases hfall with hh | hf
        · exfalso
          have : CMInstr.instrAt prog s₀.pc ≠ .halt := by
            rw [hget]
            intro h
            cases h
          exact this hh
        · simpa [CMInstr.decCounter, CMInstr.write, CMInstr.read] -- no_squeeze: simulation
  | jump k =>
      intro s' hstep
      have hs := CMInstr.step_jump prog s₀ k hget
      rw [hstep] at hs
      injection hs with hs'
      rw [hs']
      have hk : k < prog.length := (hwellPlaced.1) s₀.pc hs₀ 0 k (Or.inr (by simpa [CMInstr.instrAt] using hget)) -- no_squeeze: simulation
      simpa -- no_squeeze: simulation
  | halt =>
      intro s' hstep
      rw [CMInstr.step_halt prog s₀ hget] at hstep
      cases hstep

/-- One machine step is a playfield run to the successor entry. -/
theorem sim_step (prog : CMProgram) (hwell : wellFormed prog) (s₀ : CMState)
    (hs₀ : s₀.pc < prog.length) (hfall : s₀.pc + 1 < prog.length ∨ CMInstr.instrAt prog s₀.pc = .halt)
    (s : State (playfieldWidth prog) (playfieldHeight prog))
    (hsm : s.stringMode = false) (hpc : s.pc = blockEntry prog s₀.pc)
    (hgrid : s.grid = playfieldOf prog) (hstack : s.stack = [encodeState s₀]) :
    match CMInstr.step prog s₀ with
    | some s' => ∃ n, run n s = some (afterState prog s s')
    | none => run 2 s = none := by
  cases hget : CMInstr.instrAt prog s₀.pc with
  | inc c =>
      have hinc : prog.getD s₀.pc .halt = .inc c := by simpa [CMInstr.instrAt] using hget -- no_squeeze: simulation
      have hs := CMInstr.step_inc prog s₀ c hget
      rw [hs]
      have hi1 : s₀.pc + 1 < prog.length := by
        rcases hfall with hf | hh
        · exact hf
        · exfalso
          have : CMInstr.instrAt prog s₀.pc ≠ .halt := by
            rw [hget]
            intro h
            cases h
          exact this hh
      have hrun := sim_inc prog s₀.pc c hi1 hinc s hsm hpc hgrid hstack
      refine ⟨5, ?_⟩
      simpa [afterState, blockEntry] using hrun -- no_squeeze: simulation
  | decz c k =>
      have hdecz : prog.getD s₀.pc .halt = .decz c k := by simpa [CMInstr.instrAt] using hget -- no_squeeze: simulation
      by_cases hz : CMInstr.read c s₀ = 0
      · have hs := CMInstr.step_decz_zero prog s₀ c k hget hz
        rw [hs]
        have hi1 : s₀.pc + 1 < prog.length := by
          rcases hfall with hf | hh
          · exact hf
          · exfalso
            have : CMInstr.instrAt prog s₀.pc ≠ .halt := by
              rw [hget]
              intro h
              cases h
            exact this hh
        have hrun := sim_decz_zero prog s₀.pc k c hi1 hwell hdecz s hsm hpc hgrid hstack hz
        refine ⟨5 + corridorSteps prog s₀.pc k, ?_⟩
        simpa [afterState, blockEntry] using hrun -- no_squeeze: simulation
      · have hs := CMInstr.step_decz_nonzero prog s₀ c k hget hz
        rw [hs]
        have hi1 : s₀.pc + 1 < prog.length := by
          rcases hfall with hf | hh
          · exact hf
          · exfalso
            have : CMInstr.instrAt prog s₀.pc ≠ .halt := by
              rw [hget]
              intro h
              cases h
            exact this hh
        have hrun := sim_decz_nonzero prog s₀.pc c hi1 hdecz s hsm hpc hgrid hstack hz
        refine ⟨10, ?_⟩
        simpa [afterState, blockEntry] using hrun -- no_squeeze: simulation
  | jump k =>
      have hjump : prog.getD s₀.pc .halt = .jump k := by simpa [CMInstr.instrAt] using hget -- no_squeeze: simulation
      have hs := CMInstr.step_jump prog s₀ k hget
      rw [hs]
      have hi1 : s₀.pc + 1 < prog.length := by
        rcases hfall with hf | hh
        · exact hf
        · exfalso
          have : CMInstr.instrAt prog s₀.pc ≠ .halt := by
            rw [hget]
            intro h
            cases h
          exact this hh
      have hrun := sim_jump prog s₀.pc k hi1 hwell hjump s hsm hpc hgrid hstack
      refine ⟨2 + corridorSteps prog s₀.pc k, ?_⟩
      simpa [afterState, blockEntry] using hrun -- no_squeeze: simulation
  | halt =>
      have hhalt : prog.getD s₀.pc .halt = .halt := by simpa [CMInstr.instrAt] using hget -- no_squeeze: simulation
      have hs := CMInstr.step_halt prog s₀ hget
      rw [hs]
      have hrun := sim_halt prog s₀.pc hs₀ hhalt s hsm hpc hgrid
      exact hrun

end Completeness

end LeanFunge
