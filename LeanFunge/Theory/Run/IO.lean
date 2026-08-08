/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanFunge.Core.Semantics
import LeanFunge.Theory.Parser
import Mathlib.Data.Nat.Notation

/-!
# Run-Level I/O Separation

Input and output are independent, prefix-based effects. Reading consumes a
prefix of the input stream (never grows it), and printing appends to the
output (never shrinks it). This module proves the step-level and run-level
lemmas: the single-step case analysis over the instruction set, and the
induction showing a whole run consumes a prefix of the input and produces a
suffix extension of the output.

## Theorems

* `stepString_input`: A string-mode step leaves the input unchanged.
* `stepString_output`: A string-mode step leaves the output unchanged.
* `stepState_input_prefix`: A step-state transition consumes a prefix of the
  input.
* `stepState_output_prefix`: A step-state transition appends to the output.
* `step_input_prefix`: A step consumes a prefix of the input.
* `step_output_prefix`: A step appends to the output.
* `run_input_prefix`: A run consumes a prefix of the input.
* `run_output_prefix`: A run appends to the output.
-/

namespace LeanFunge

/-- A string-mode step leaves the input unchanged. -/
theorem stepString_input (s : State w h) (ch : Char) :
    (stepString s ch).input = s.input := by
  unfold stepString
  cases (ch.toNat == '"'.toNat) <;> rfl

/-- A string-mode step leaves the output unchanged. -/
theorem stepString_output (s : State w h) (ch : Char) :
    (stepString s ch).output = s.output := by
  unfold stepString
  cases (ch.toNat == '"'.toNat) <;> rfl

/-- A step-state transition consumes a prefix of the input: the new input is a
    suffix of the old, taken from the front. -/
theorem stepState_input_prefix (s : State w h) (instr : Instruction) :
    ∃ pre : List Char, s.input = pre ++ (stepState s instr).input := by
  by_cases hic : instr = .inputChar
  · subst instr
    cases h : s.input with
    | nil => exact ⟨[], by simp only [stepState, h, List.append_nil]
        ⟩
    | cons c rest => exact ⟨[c], by simp only [
      stepState, h, Int.ofNat_eq_natCast, List.cons_append, List.nil_append]
        ⟩
  · by_cases hii : instr = .inputInt
    · subst instr
      rcases parseInt_suffix s.input with ⟨pre, hpre⟩
      exact ⟨pre, hpre⟩
    · exact ⟨[], by
        cases instr <;> first
          | contradiction
          | simp only [stepState, List.nil_append, gt_iff_lt, Int.ofNat_eq_natCast]
        ⟩

/-- A step-state transition appends to the output: the new output extends the
    old. -/
theorem stepState_output_prefix (s : State w h) (instr : Instruction) :
    ∃ suf : String, (stepState s instr).output = s.output ++ suf := by
  by_cases hpi : instr = .printInt
  · subst instr
    exact ⟨String.ofList (formatInt (Stack.top s.stack)), rfl⟩
  · by_cases hpc : instr = .printChar
    · subst instr
      exact ⟨String.singleton (Char.ofNat (Int.toNat (Stack.top s.stack))), rfl⟩
    · exact ⟨"", by
        cases instr <;> first
          | contradiction
          | cases h : s.input <;> simp only [
            stepState, h, String.append_empty, gt_iff_lt, Int.ofNat_eq_natCast]
        ⟩

/-- A step consumes a prefix of the input: the remaining input is a suffix of
    the original. -/
theorem step_input_prefix (s s' : State w h) (hstep : step s = some s') :
    ∃ pre : List Char, s.input = pre ++ s'.input := by
  unfold step at hstep
  cases hsm : s.stringMode with
  | true =>
      rw [hsm] at hstep
      have hs' : stepString s (s.grid.get s.pc.1 s.pc.2) = s' := by
        simpa only [Option.some.injEq] using hstep
      subst s'
      exact ⟨[], by simp only [stepString_input, List.nil_append]
        ⟩
  | false =>
      rw [hsm] at hstep
      by_cases hdec : decodeChar (s.grid.get s.pc.1 s.pc.2) = .halt
      · simp only [hdec, reduceCtorEq] at hstep
      · simp only [Option.some.injEq] at hstep
        subst s'
        rcases stepState_input_prefix s (decodeChar (s.grid.get s.pc.1 s.pc.2)) with ⟨pre, hpre⟩
        exact ⟨pre, hpre⟩

/-- A step appends to the output: the new output extends the old. -/
theorem step_output_prefix (s s' : State w h) (hstep : step s = some s') :
    ∃ suf : String, s'.output = s.output ++ suf := by
  unfold step at hstep
  cases hsm : s.stringMode with
  | true =>
      rw [hsm] at hstep
      have hs' : stepString s (s.grid.get s.pc.1 s.pc.2) = s' := by
        simpa only [Option.some.injEq] using hstep
      subst s'
      exact ⟨"", by simp only [stepString_output, String.append_empty]
        ⟩
  | false =>
      rw [hsm] at hstep
      by_cases hdec : decodeChar (s.grid.get s.pc.1 s.pc.2) = .halt
      · simp only [hdec, reduceCtorEq] at hstep
      · simp only [Option.some.injEq] at hstep
        subst s'
        rcases stepState_output_prefix s (decodeChar (s.grid.get s.pc.1 s.pc.2)) with ⟨suf, hsuf⟩
        exact ⟨suf, hsuf⟩

/-- A run consumes a prefix of the input: the input at any point is a suffix
    of the original stream. -/
theorem run_input_prefix (s : State w h) (n : ℕ) (s' : State w h) (h : run n s = some s') :
    ∃ pre : List Char, s.input = pre ++ s'.input := by
  induction n generalizing s' with
  | zero =>
      rw [run] at h
      injection h with hs'
      rw [hs']
      exact ⟨[], by simp only [List.nil_append]
        ⟩
  | succ n ih =>
      rcases hrun : run n s with _ | sₙ
      · rw [run, hrun] at h
        cases h
      · rw [run, hrun] at h
        have hstep : step sₙ = some s' := by simpa only using h
        rcases ih sₙ hrun with ⟨pre₁, hpre₁⟩
        rcases step_input_prefix sₙ s' hstep with ⟨pre₂, hpre₂⟩
        exact ⟨pre₁ ++ pre₂, by
          rw [hpre₁, hpre₂]
          simp only [List.append_assoc]
          ⟩

/-- A run appends to the output: the output at any point extends the initial
    output. -/
theorem run_output_prefix (s : State w h) (n : ℕ) (s' : State w h) (h : run n s = some s') :
    ∃ suf : String, s'.output = s.output ++ suf := by
  induction n generalizing s' with
  | zero =>
      rw [run] at h
      injection h with hs'
      rw [hs']
      exact ⟨"", by simp only [String.append_empty]
        ⟩
  | succ n ih =>
      rcases hrun : run n s with _ | sₙ
      · rw [run, hrun] at h
        cases h
      · rw [run, hrun] at h
        have hstep : step sₙ = some s' := by simpa only using h
        rcases ih sₙ hrun with ⟨suf₁, hsuf₁⟩
        rcases step_output_prefix sₙ s' hstep with ⟨suf₂, hsuf₂⟩
        exact ⟨suf₁ ++ suf₂, by
          rw [hsuf₂, hsuf₁]
          simp only [String.append_assoc]
          ⟩

end LeanFunge
