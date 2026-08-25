/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanFunge.Theory.Run.IO
import LeanFunge.Theory.Run.Relational
import LeanFunge.Theory.Run.String

/-!
# Run-Level Laws for the Nondeterministic Semantics

The run-level laws are proven for the deterministic interpreter, which fixes
`?` to keep the current direction. This module lifts the direction-independent
ones to the transition relation, so they hold along every nondeterministic
trace.

The lift rests on `stepRel_fields`: a relational step is either the
deterministic step, or a `?` redirect that changes only the direction and the
pointer. Every field a direction-independent law speaks about — the playfield,
the stack, string mode, the input, and the output — is therefore untouched by
the nondeterminism.

Two run-level laws do *not* lift, and deliberately so. The write trace of
`run_grid_writes` is path-dependent: which cells a run executes depends on the
directions taken, so the accumulated writes are not determined by the step
count alone. And `not_halts_safe_line` is a statement about travel in a fixed
direction — a `?` on the line redirects the pointer off its row or column, so
the safe-line hypothesis no longer describes where the pointer goes.

## Theorems

* `stepRel_fields`: A relational step is the deterministic step, or a `?`
  redirect that changes only the direction and the pointer.
* `stepRel_string_mode`: A relational step in string mode leaves the
  playfield, input, and output untouched.
* `stepRel_stringMode_xor`: Every relational step toggles string mode exactly
  when the executed cell is a double quote.
* `stepRel_input_prefix`: A relational step consumes a prefix of the input.
* `stepRel_output_prefix`: A relational step appends to the output.
* `runRel_input_prefix`: A relational run consumes a prefix of the input.
* `runRel_output_prefix`: A relational run appends to the output.
* `runRel_string_mode`: A relational run that stays in string mode throughout
  leaves the playfield, input, and output untouched.
-/

namespace LeanFunge

/-- A relational step is either the deterministic step, or a `?` redirect that
    changes only the direction and the pointer. -/
theorem stepRel_fields {s s' : State w h} (hrel : stepRel s (some s')) :
    (step s = some s' ∨
      (s'.grid = s.grid ∧ s'.stack = s.stack ∧ s'.stringMode = s.stringMode ∧
        s'.input = s.input ∧ s'.output = s.output ∧
        decodeChar (s.grid.get s.pc.1 s.pc.2) = .random)) := by
  rcases hrel with hd | ⟨d, hsm, hrand, heq⟩
  · exact Or.inl hd.symm
  · right
    injection heq with heq
    subst heq
    exact ⟨rfl, rfl, rfl, rfl, rfl, hrand⟩


/-- A relational step in string mode leaves the playfield, input, and output
    untouched: string mode is data, not code, for the nondeterministic
    semantics too. Note `?` decodes to `.random` only outside string mode, so
    in string mode the relation coincides with the deterministic step. -/
theorem stepRel_string_mode {s s' : State w h} (hsm : s.stringMode = true)
    (hrel : stepRel s (some s')) :
    s'.grid = s.grid ∧ s'.input = s.input ∧ s'.output = s.output := by
  rcases stepRel_fields hrel with hd | ⟨hg, _, _, hi, ho, _⟩
  · obtain ⟨s'', hstep, hg, hi, ho, _⟩ := step_string_mode s hsm
    rw [hd] at hstep
    injection hstep with he
    subst he
    exact ⟨hg, hi, ho⟩
  · exact ⟨hg, hi, ho⟩

/-- Every relational step toggles string mode exactly when the executed cell
    is `"`, since a `?` redirect leaves string mode alone. -/
theorem stepRel_stringMode_xor {s s' : State w h} (hrel : stepRel s (some s')) :
    s'.stringMode = xor s.stringMode (s.grid.get s.pc.1 s.pc.2 == '"') := by
  rcases stepRel_fields hrel with hd | ⟨_, _, hsm, _, _, hrand⟩
  · exact step_stringMode_xor hd
  · rw [hsm]
    have hq : (s.grid.get s.pc.1 s.pc.2 == '"') = false := by
      have hne : s.grid.get s.pc.1 s.pc.2 ≠ '"' := by
        intro hc
        rw [(decodeChar_stringMode_iff _).mpr hc] at hrand
        cases hrand
      simpa only [beq_eq_false_iff_ne, ne_eq]
    rw [hq]
    simp only [Bool.xor_false]


/-- A relational step consumes a prefix of the input. -/
theorem stepRel_input_prefix {s s' : State w h} (hrel : stepRel s (some s')) :
    ∃ pre : List Char, s.input = pre ++ s'.input := by
  rcases stepRel_fields hrel with hd | ⟨_, _, _, hi, _, _⟩
  · exact step_input_prefix s s' hd
  · exact ⟨[], by rw [hi, List.nil_append]⟩

/-- A relational step appends to the output. -/
theorem stepRel_output_prefix {s s' : State w h} (hrel : stepRel s (some s')) :
    ∃ suf : String, s'.output = s.output ++ suf := by
  rcases stepRel_fields hrel with hd | ⟨_, _, _, _, ho, _⟩
  · exact step_output_prefix s s' hd
  · exact ⟨"", by rw [ho, String.append_empty]⟩


/-- A relational run consumes a prefix of the input. -/
theorem runRel_input_prefix (n : ℕ) (s s' : State w h)
    (hrel : runRel n s (some s')) :
    ∃ pre : List Char, s.input = pre ++ s'.input := by
  induction n generalizing s' with
  | zero =>
      rw [runRel] at hrel
      injection hrel with he
      subst he
      exact ⟨[], rfl⟩
  | succ n ih =>
      rcases hrel with ⟨sn, hn, hstep⟩ | ⟨_, hc⟩
      · obtain ⟨pre₁, hpre₁⟩ := ih sn hn
        obtain ⟨pre₂, hpre₂⟩ := stepRel_input_prefix hstep
        exact ⟨pre₁ ++ pre₂, by rw [hpre₁, hpre₂, List.append_assoc]⟩
      · cases hc

/-- A relational run appends to the output. -/
theorem runRel_output_prefix (n : ℕ) (s s' : State w h)
    (hrel : runRel n s (some s')) :
    ∃ suf : String, s'.output = s.output ++ suf := by
  induction n generalizing s' with
  | zero =>
      rw [runRel] at hrel
      injection hrel with he
      subst he
      exact ⟨"", by rw [String.append_empty]⟩
  | succ n ih =>
      rcases hrel with ⟨sn, hn, hstep⟩ | ⟨_, hc⟩
      · obtain ⟨suf₁, hsuf₁⟩ := ih sn hn
        obtain ⟨suf₂, hsuf₂⟩ := stepRel_output_prefix hstep
        exact ⟨suf₁ ++ suf₂, by rw [hsuf₂, hsuf₁, String.append_assoc]⟩
      · cases hc


/-- A relational run that stays in string mode throughout leaves the
    playfield, input, and output untouched. -/
theorem runRel_string_mode (n : ℕ) (s s' : State w h)
    (hrel : runRel n s (some s'))
    (hin : ∀ k < n, ∀ sk, runRel k s (some sk) → sk.stringMode = true) :
    s'.grid = s.grid ∧ s'.input = s.input ∧ s'.output = s.output := by
  induction n generalizing s' with
  | zero =>
      rw [runRel] at hrel
      injection hrel with he
      subst he
      exact ⟨rfl, rfl, rfl⟩
  | succ n ih =>
      rcases hrel with ⟨sn, hn, hstep⟩ | ⟨_, hc⟩
      · obtain ⟨hg, hi, ho⟩ := ih sn hn (fun k hk sk hsk =>
          hin k (Nat.lt_succ_of_lt hk) sk hsk)
        have hsm : sn.stringMode = true := hin n (Nat.lt_succ_self n) sn hn
        obtain ⟨hg', hi', ho'⟩ := stepRel_string_mode hsm hstep
        exact ⟨by rw [hg', hg], by rw [hi', hi], by rw [ho', ho]⟩
      · cases hc

end LeanFunge
