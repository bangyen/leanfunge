/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanFunge.Theory.Completeness.Layout
import LeanFunge.Theory.Completeness.LayoutBlock
import LeanFunge.Theory.Completeness.LayoutCorridorRow
import LeanFunge.Theory.Completeness.PairEncoding
import LeanFunge.Theory.Completeness.TwoCounter
import Mathlib.Tactic

/-!
# The Simulation Foundations

The two-counter machine state is encoded as the single stack value
`2^c1 * 3^c2`, and the counter updates translate into stack arithmetic. This
module proves the encoding-level lemmas the simulation needs, and the step
count of a corridor jump.

## Main definitions

* `encodeState`: The stack value encoding a two-counter machine state.
* `corridorSteps`: The number of playfield steps a corridor jump takes.
* `wellPlaced`: A well-formed program whose last instruction is `halt`, so no
  fall-through runs off the end of the playfield.

## Theorems

* `encode_incCounter`: Incrementing a counter multiplies the encoding by its digit.
* `encode_deczCounter`: Decrementing a positive counter divides the encoding by its digit.
* `encode_mod_zero`: The encoding's remainder tests whether the counter is positive.
* `corridorSteps_pos`: A corridor jump takes at least one step.
-/

namespace LeanFunge

namespace Completeness

open CMInstr

/-- The stack value encoding a two-counter machine state. -/
def encodeState (s : CMState) : Int :=
  Int.ofNat (encode s.c1 s.c2)

/-- The number of playfield steps a corridor jump edge takes. -/
def corridorSteps (prog : CMProgram) (i k : ℕ) : ℕ :=
  (blockRow prog i - i)
    + (if entryColumn prog k ≥ branchColumn prog i then
         entryColumn prog k - branchColumn prog i
       else branchColumn prog i - entryColumn prog k)
    + (blockRow prog k - i - 1)

/-- A well-formed program whose last instruction is `halt`, so no fall-through
    runs off the end of the playfield. -/
def wellPlaced (prog : CMProgram) : Prop :=
  wellFormed prog ∧ ∀ i : ℕ, i < prog.length → instrAt prog i = .halt ∨ i + 1 < prog.length

/-- Incrementing a counter multiplies the encoding by its digit. -/
theorem encode_incCounter (c : Fin 2) (s : CMState) :
    encodeState (incCounter c s) = encodeState s * counterVal c := by
  fin_cases c
  · simpa [encodeState, incCounter, write, CMInstr.read, counterVal] using (encode_inc_c1_int s.c1 s.c2).symm -- no_squeeze: simulation
  · simpa [encodeState, incCounter, write, CMInstr.read, counterVal] using (encode_inc_c2_int s.c1 s.c2).symm -- no_squeeze: simulation

/-- Decrementing a positive counter divides the encoding by its digit. -/
theorem encode_deczCounter (c : Fin 2) (s : CMState) (h : CMInstr.read c s ≠ 0) :
    encodeState (decCounter c s) = encodeState s / counterVal c := by
  fin_cases c
  · have h1 : 0 < s.c1 := by
      have : s.c1 ≠ 0 := by simpa [CMInstr.read] using h -- no_squeeze: simulation
      omega
    simpa [encodeState, decCounter, write, CMInstr.read, counterVal, h1] using (encode_decz_c1_int s.c1 s.c2 h1).symm -- no_squeeze: simulation
  · have h2 : 0 < s.c2 := by
      have : s.c2 ≠ 0 := by simpa [CMInstr.read] using h -- no_squeeze: simulation
      omega
    simpa [encodeState, decCounter, write, CMInstr.read, counterVal, h2] using (encode_decz_c2_int s.c1 s.c2 h2).symm -- no_squeeze: simulation

/-- The encoding's remainder tests whether the counter is positive. -/
theorem encode_mod_zero (c : Fin 2) (s : CMState) :
    encodeState s % counterVal c = 0 ↔ CMInstr.read c s ≠ 0 := by
  fin_cases c
  · simp [encodeState, counterVal, CMInstr.read] -- no_squeeze: simulation
    have hdvd : (2 : Int) ∣ (encode s.c1 s.c2 : Int) ↔ (2 : ℕ) ∣ encode s.c1 s.c2 := by
      simpa using (Int.natCast_dvd_natCast (m := 2) (n := encode s.c1 s.c2)) -- no_squeeze: simulation
    rw [hdvd]
    have h := encode_c1_pos s.c1 s.c2
    rw [Nat.dvd_iff_mod_eq_zero, h.symm]
    omega
  · simp [encodeState, counterVal, CMInstr.read] -- no_squeeze: simulation
    have hdvd : (3 : Int) ∣ (encode s.c1 s.c2 : Int) ↔ (3 : ℕ) ∣ encode s.c1 s.c2 := by
      simpa using (Int.natCast_dvd_natCast (m := 3) (n := encode s.c1 s.c2)) -- no_squeeze: simulation
    rw [hdvd]
    have h := encode_c2_pos s.c1 s.c2
    rw [Nat.dvd_iff_mod_eq_zero, h.symm]
    omega

/-- A corridor jump takes at least one step. -/
theorem corridorSteps_pos (prog : CMProgram) (i : ℕ) (hi : i < prog.length) (k : ℕ) :
    1 ≤ corridorSteps prog i k := by
  dsimp [corridorSteps] -- no_squeeze: simulation
  have hge : prog.length ≤ blockRow prog i := blockRow_ge_length prog i
  omega

end Completeness

end LeanFunge
