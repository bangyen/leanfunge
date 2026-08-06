/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanFunge.Theory.Completeness.Linear
import LeanFunge.Theory.Completeness.LinearRow
import LeanFunge.Theory.Completeness.TwoCounter
import LeanFunge.Theory.Step
import Mathlib.Data.Nat.Notation

/-!
# The Branch-Free Simulation Core

The two-counter machine side of the branch-free simulation: the prefix run of
`foldIncs`, the encoding updates, the two-cell increment runs, and the central
`linear_prefix` correspondence linking the interpreter run to the encoded prefix.

## Theorems

* `foldIncs_zero`: Applying no instructions is the identity.
* `foldIncs_succ_inc`: Applying one more `inc` increments the counter.
* `enc_update_inc_zero`: The encoding after incrementing counter 1.
* `enc_update_inc_one`: The encoding after incrementing counter 2.
* `linear_step_mul_two`: Running a `2*` pair on a one-element stack.
* `linear_step_mul_three`: Running a `3*` pair on a one-element stack.
* `linear_prefix`: The interpreter reaches instruction `j` with the encoded prefix.
* `linear_prefix_2cm`: The two-counter machine reaches the same prefix.
-/

namespace LeanFunge
namespace Completeness

theorem foldIncs_zero (prog : CMProgram) (s : CMState) : foldIncs prog 0 s = s := by
  rfl

/-- Applying one more `inc` increments the named counter. -/
theorem foldIncs_succ_inc (prog : CMProgram) (j : ℕ) (c : Fin 2) (s : CMState)
    (h : prog.getD j .halt = .inc c) :
    foldIncs prog (j + 1) s = CMInstr.incCounter c (foldIncs prog j s) := by
  rw [show j + 1 = Nat.succ j by omega]
  change (match prog.getD j .halt with
          | .inc c => CMInstr.incCounter c (foldIncs prog j s)
          | x => foldIncs prog j s) = CMInstr.incCounter c (foldIncs prog j s)
  rw [h]

/-- The encoding after incrementing counter 1. -/
theorem enc_update_inc_zero (prog : CMProgram) (c1 c2 : ℕ) {j : ℕ}
    (h : prog.getD j .halt = .inc 0) :
    (Int.ofNat (encode (foldIncs prog j (CMInstr.startCM c1 c2)).c1
                       (foldIncs prog j (CMInstr.startCM c1 c2)).c2)) * 2
      = Int.ofNat (encode (foldIncs prog (j + 1) (CMInstr.startCM c1 c2)).c1
                          (foldIncs prog (j + 1) (CMInstr.startCM c1 c2)).c2) := by
  rw [foldIncs_succ_inc prog j 0 (CMInstr.startCM c1 c2) h]
  have hc1 : (CMInstr.incCounter 0 (foldIncs prog j (CMInstr.startCM c1 c2))).c1
      = (foldIncs prog j (CMInstr.startCM c1 c2)).c1 + 1 := by
    simp only [CMInstr.incCounter, CMInstr.read, CMInstr.write]
    rfl
  have hc2 : (CMInstr.incCounter 0 (foldIncs prog j (CMInstr.startCM c1 c2))).c2
      = (foldIncs prog j (CMInstr.startCM c1 c2)).c2 := by
    simp only [CMInstr.incCounter, CMInstr.read, CMInstr.write]
    rfl
  rw [hc1, hc2]
  rw (config := { transparency := .default }) [encode_inc_c1_int
      (foldIncs prog j (CMInstr.startCM c1 c2)).c1
      (foldIncs prog j (CMInstr.startCM c1 c2)).c2]
  rfl

/-- The encoding after incrementing counter 2. -/
theorem enc_update_inc_one (prog : CMProgram) (c1 c2 : ℕ) {j : ℕ}
    (h : prog.getD j .halt = .inc 1) :
    (Int.ofNat (encode (foldIncs prog j (CMInstr.startCM c1 c2)).c1
                       (foldIncs prog j (CMInstr.startCM c1 c2)).c2)) * 3
      = Int.ofNat (encode (foldIncs prog (j + 1) (CMInstr.startCM c1 c2)).c1
                          (foldIncs prog (j + 1) (CMInstr.startCM c1 c2)).c2) := by
  rw [foldIncs_succ_inc prog j 1 (CMInstr.startCM c1 c2) h]
  have hc1 : (CMInstr.incCounter 1 (foldIncs prog j (CMInstr.startCM c1 c2))).c1
      = (foldIncs prog j (CMInstr.startCM c1 c2)).c1 := by
    simp only [CMInstr.incCounter, CMInstr.read, CMInstr.write]
    rfl
  have hc2 : (CMInstr.incCounter 1 (foldIncs prog j (CMInstr.startCM c1 c2))).c2
      = (foldIncs prog j (CMInstr.startCM c1 c2)).c2 + 1 := by
    simp only [CMInstr.incCounter, CMInstr.read, CMInstr.write]
    rfl
  rw [hc1, hc2]
  rw (config := { transparency := .default }) [encode_inc_c2_int
      (foldIncs prog j (CMInstr.startCM c1 c2)).c1
      (foldIncs prog j (CMInstr.startCM c1 c2)).c2]
  rfl

/-- Running a `2*` pair on a one-element stack multiplies the value by two. -/
theorem linear_step_mul_two (s : State w h) (p : ℕ) (n : Int)
    (hsm : s.stringMode = false) (hdir : s.dir = Direction.right)
    (hpc : s.pc = (p, 0)) (hno : p + 2 < w) (hstack : s.stack = [n])
    (hc1 : s.grid.get p 0 = '2') (hc2 : s.grid.get (p + 1) 0 = '*') :
    run 2 s = some { s with stack := [n * 2], pc := (p + 2, 0) } := by
  rw [run_mul_two s p hsm hdir hpc hno hc1 hc2]
  congr 1
  rw [hstack]
  rfl

/-- Running a `3*` pair on a one-element stack multiplies the value by three. -/
theorem linear_step_mul_three (s : State w h) (p : ℕ) (n : Int)
    (hsm : s.stringMode = false) (hdir : s.dir = Direction.right)
    (hpc : s.pc = (p, 0)) (hno : p + 2 < w) (hstack : s.stack = [n])
    (hc1 : s.grid.get p 0 = '3') (hc2 : s.grid.get (p + 1) 0 = '*') :
    run 2 s = some { s with stack := [n * 3], pc := (p + 2, 0) } := by
  rw [run_mul_three s p hsm hdir hpc hno hc1 hc2]
  congr 1
  rw [hstack]
  rfl

/-- The interpreter reaches the entry of instruction `j` with the encoded
    prefix on the stack. -/
theorem linear_prefix (prog : CMProgram) (c1 c2 : ℕ) (j : ℕ)
    (hinc : ∀ i, i < j → prog.getD i .halt = .inc 0 ∨ prog.getD i .halt = .inc 1)
    (hw : 1 + 2 * j < (linearRow prog).length) :
    run (1 + 2 * j) (linearStart prog c1 c2) =
      some { linearStart prog c1 c2 with
        stack := [Int.ofNat (encode (foldIncs prog j (CMInstr.startCM c1 c2)).c1
                                     (foldIncs prog j (CMInstr.startCM c1 c2)).c2)],
        pc := (1 + 2 * j, 0) } := by
  induction j with
  | zero =>
      have hcell : (linearStart prog c1 c2).grid.get 0 0 = '>' := by
        rw [show (linearStart prog c1 c2).grid.get 0 0 = (linearGrid prog).get 0 0 by rfl]
        rw [linearGrid_get prog 0 (by have hl := linearRow_length prog 0 hinc; omega)]
        rfl
      have hstep : step (linearStart prog c1 c2) =
          some { linearStart prog c1 c2 with pc := (1, 0) } := by
        unfold step
        have hdec : decodeChar '>' = .right := by
          unfold decodeChar
          rfl
        simp only [linearStart, State.init, hdec, hcell, stepState]
        rw [stepPos_right_no_wrap 0 (linearRow prog).length 1 (by
            have hl := linearRow_length prog 0 hinc
            omega)]
        rfl
      rw [show run 1 (linearStart prog c1 c2) = step (linearStart prog c1 c2) by rfl]
      rw [hstep]
      rfl
  | succ j ih =>
      have hinc_j : ∀ i, i < j → prog.getD i .halt = .inc 0 ∨ prog.getD i .halt = .inc 1 :=
        fun i hi => hinc i (Nat.lt_trans hi (Nat.lt_succ_self j))
      have hw_j : 1 + 2 * j < (linearRow prog).length := by omega
      have hrun_j : run (1 + 2 * j) (linearStart prog c1 c2) =
          some { linearStart prog c1 c2 with
            stack := [Int.ofNat (encode (foldIncs prog j (CMInstr.startCM c1 c2)).c1
                                         (foldIncs prog j (CMInstr.startCM c1 c2)).c2)],
            pc := (1 + 2 * j, 0) } := ih hinc_j hw_j
      let S : State (linearRow prog).length 1 :=
        { linearStart prog c1 c2 with
          stack := [Int.ofNat (encode (foldIncs prog j (CMInstr.startCM c1 c2)).c1
                                       (foldIncs prog j (CMInstr.startCM c1 c2)).c2)],
          pc := (1 + 2 * j, 0) }
      have hstep2 : run 2 S =
          some { linearStart prog c1 c2 with
            stack := [Int.ofNat (encode (foldIncs prog (j + 1) (CMInstr.startCM c1 c2)).c1
                                         (foldIncs prog (j + 1) (CMInstr.startCM c1 c2)).c2)],
            pc := (1 + 2 * (j + 1), 0) } := by
        rcases hinc j (Nat.lt_succ_self j) with h0 | h1
        · rw [linear_step_mul_two S (1 + 2 * j)
              (Int.ofNat (encode (foldIncs prog j (CMInstr.startCM c1 c2)).c1
                                 (foldIncs prog j (CMInstr.startCM c1 c2)).c2))
              (by rfl) (by rfl) (by rfl) (by omega)
              (by rfl)
              (by
                rw [show S.grid.get (1 + 2 * j) 0 = (linearGrid prog).get (1 + 2 * j) 0 by rfl]
                rw [linearGrid_get prog (1 + 2 * j) (by omega)]
                rw [linearRow_get_first prog j hinc_j (Or.inl h0)]
                rw [h0]
                decide)
              (by
                rw [show S.grid.get ((1 + 2 * j) + 1) 0 = (linearGrid prog).get ((1 + 2 * j) + 1) 0 by rfl]
                rw [linearGrid_get prog ((1 + 2 * j) + 1) (by omega)]
                rw [show (1 + 2 * j) + 1 = 2 + 2 * j by omega]
                rw [linearRow_get_second prog j hinc_j (Or.inl h0)]
                rw [h0]
                decide)]
          congr 1
          rw [enc_update_inc_zero prog c1 c2 h0]
          rw [show (1 + 2 * j + 2, 0) = (1 + 2 * (j + 1), 0) by ext <;> omega]
        · rw [linear_step_mul_three S (1 + 2 * j)
              (Int.ofNat (encode (foldIncs prog j (CMInstr.startCM c1 c2)).c1
                                 (foldIncs prog j (CMInstr.startCM c1 c2)).c2))
              (by rfl) (by rfl) (by rfl) (by omega)
              (by rfl)
              (by
                rw [show S.grid.get (1 + 2 * j) 0 = (linearGrid prog).get (1 + 2 * j) 0 by rfl]
                rw [linearGrid_get prog (1 + 2 * j) (by omega)]
                rw [linearRow_get_first prog j hinc_j (Or.inr h1)]
                rw [h1]
                decide)
              (by
                rw [show S.grid.get ((1 + 2 * j) + 1) 0 = (linearGrid prog).get ((1 + 2 * j) + 1) 0 by rfl]
                rw [linearGrid_get prog ((1 + 2 * j) + 1) (by omega)]
                rw [show (1 + 2 * j) + 1 = 2 + 2 * j by omega]
                rw [linearRow_get_second prog j hinc_j (Or.inr h1)]
                rw [h1]
                decide)]
          congr 1
          rw [enc_update_inc_one prog c1 c2 h1]
          rw [show (1 + 2 * j + 2, 0) = (1 + 2 * (j + 1), 0) by ext <;> omega]
      have hrun : run (1 + 2 * (j + 1)) (linearStart prog c1 c2) =
          some { linearStart prog c1 c2 with
            stack := [Int.ofNat (encode (foldIncs prog (j + 1) (CMInstr.startCM c1 c2)).c1
                                         (foldIncs prog (j + 1) (CMInstr.startCM c1 c2)).c2)],
            pc := (1 + 2 * (j + 1), 0) } := by
        rw [show 1 + 2 * (j + 1) = (1 + 2 * j) + 2 by omega]
        exact run_append (linearStart prog c1 c2) S
          (some { linearStart prog c1 c2 with
            stack := [Int.ofNat (encode (foldIncs prog (j + 1) (CMInstr.startCM c1 c2)).c1
                                         (foldIncs prog (j + 1) (CMInstr.startCM c1 c2)).c2)],
            pc := (1 + 2 * (j + 1), 0) }) (1 + 2 * j) 2 hrun_j hstep2
      exact hrun

/-- The two-counter machine reaches the same prefix. -/
theorem linear_prefix_2cm (prog : CMProgram) (c1 c2 : ℕ) (j : ℕ)
    (hinc : ∀ i, i < j → prog.getD i .halt = .inc 0 ∨ prog.getD i .halt = .inc 1) :
    CMInstr.run prog j (CMInstr.startCM c1 c2) =
      some { foldIncs prog j (CMInstr.startCM c1 c2) with pc := j } := by
  induction j with
  | zero => rfl
  | succ j ih =>
      have hrun : CMInstr.run prog j (CMInstr.startCM c1 c2) =
          some { foldIncs prog j (CMInstr.startCM c1 c2) with pc := j } := by
        apply ih
        intro i hi
        exact hinc i (Nat.lt_trans hi (Nat.lt_succ_self j))
      rw [CMInstr.run_succ]
      rw [hrun]
      change CMInstr.step prog { foldIncs prog j (CMInstr.startCM c1 c2) with pc := j }
        = some { foldIncs prog (j + 1) (CMInstr.startCM c1 c2) with pc := j + 1 }
      rcases hinc j (Nat.lt_succ_self j) with h0 | h1
      · rw [CMInstr.step_inc prog { foldIncs prog j (CMInstr.startCM c1 c2) with pc := j } 0]
        · congr 1
          rw [foldIncs_succ_inc prog j 0 (CMInstr.startCM c1 c2) h0]
          rfl
        · simpa only [CMInstr.instrAt] using h0
      · rw [CMInstr.step_inc prog { foldIncs prog j (CMInstr.startCM c1 c2) with pc := j } 1]
        · congr 1
          rw [foldIncs_succ_inc prog j 1 (CMInstr.startCM c1 c2) h1]
          rfl
        · simpa only [CMInstr.instrAt] using h1

end Completeness

end LeanFunge
