import LeanFunge.Theory.Completeness.LayoutSimulation
import LeanFunge.Theory.Completeness.LayoutSimulationRun
import LeanFunge.Theory.Step
import Mathlib.Tactic

/-!
# The Program Normalization

Every two-counter machine is equivalent, on the encoded counters and on
halting, to a well-placed program: clamp every jump target into the program
and append a `halt`.

## Main definitions

* `clampInstr`: Clamp a jump target into a program's instruction range.
* `normalize`: Clamp every target into the program and append a `halt`.

## Theorems

* `wellPlaced_normalize`: Every program normalizes to a well-placed one.
-/

namespace LeanFunge

namespace Completeness

open CMInstr

def clampInstr (n : ℕ) : CMInstr → CMInstr
  | .jump k => .jump (min k n)
  | .decz c k => .decz c (min k n)
  | instr => instr

/-- The normalization of a program: clamp every target into the program and
    append a `halt`, so the last instruction is a `halt` and no target runs off
    the end. -/
def normalize (prog : CMProgram) : CMProgram :=
  (prog.map (clampInstr prog.length)) ++ [.halt]

lemma getD_append_lt {α : Type} (l₁ l₂ : List α) (n : ℕ) (hn : n < l₁.length) (d : α) :
    (l₁ ++ l₂).getD n d = l₁.getD n d := by
  induction l₁ generalizing n with
  | nil =>
      simp [List.length] at hn
  | cons x xs ih =>
      cases n with
      | zero => rfl
      | succ n =>
          simp [List.length] at hn
          have hn' : n < xs.length := by omega
          simpa using ih n hn'

lemma getD_map {α β : Type} (f : α → β) (l : List α) (n : ℕ) (d : α) :
    (l.map f).getD n (f d) = f (l.getD n d) := by
  induction l generalizing n with
  | nil => simp
  | cons x xs ih =>
      cases n with
      | zero => rfl
      | succ n => exact ih n

lemma getD_append_right {α : Type} (l₁ l₂ : List α) (n : ℕ) (hn : l₁.length ≤ n) (d : α) :
    (l₁ ++ l₂).getD n d = l₂.getD (n - l₁.length) d := by
  induction l₁ generalizing n with
  | nil => simp
  | cons x xs ih =>
      cases n with
      | zero => simp at hn
      | succ n =>
          simp [List.length] at hn
          have hn' : xs.length ≤ n := by omega
          simpa using ih n hn'

/-- The normalized program's instruction at an in-range index is the clamped
    original instruction. -/
lemma instrAt_normalize_lt (prog : CMProgram) (i : ℕ) (hi : i < prog.length) :
    instrAt (normalize prog) i = clampInstr prog.length (instrAt prog i) := by
  unfold instrAt normalize
  have hlen : i < (prog.map (clampInstr prog.length)).length := by
    simpa using hi
  rw [getD_append_lt (prog.map (clampInstr prog.length)) [.halt] i hlen .halt]
  change (prog.map (clampInstr prog.length)).getD i (clampInstr prog.length .halt)
      = clampInstr prog.length (prog.getD i .halt)
  rw [getD_map (clampInstr prog.length) prog i .halt]

/-- Past the appended `halt`, the normalized program is a `halt`. -/
lemma instrAt_normalize_ge (prog : CMProgram) (i : ℕ) (hi : prog.length ≤ i) :
    instrAt (normalize prog) i = .halt := by
  unfold instrAt normalize
  have hlen : (prog.map (clampInstr prog.length)).length ≤ i := by
    simpa using hi
  rw [getD_append_right (prog.map (clampInstr prog.length)) [.halt] i hlen .halt]
  have hsub : i - (prog.map (clampInstr prog.length)).length = i - prog.length := by
    simp
  rw [hsub]
  by_cases h0 : i - prog.length = 0
  · simp [h0]
  · have hpos : 0 < i - prog.length := by omega
    simp [h0]

/-- The normalized program is well placed. -/
theorem wellPlaced_normalize (prog : CMProgram) : wellPlaced (normalize prog) := by
  constructor
  · unfold wellFormed
    intro i hi c k hk
    change instrAt (normalize prog) i = .decz c k ∨ instrAt (normalize prog) i = .jump k at hk
    have hlen : i < prog.length := by
      by_contra h
      have hge : prog.length ≤ i := by omega
      have hh : instrAt (normalize prog) i = .halt := instrAt_normalize_ge prog i hge
      rw [hh] at hk
      rcases hk with hk | hk <;> cases hk
    have hget' : instrAt (normalize prog) i = clampInstr prog.length (instrAt prog i) :=
      instrAt_normalize_lt prog i hlen
    rw [hget'] at hk
    rcases hk with hk | hk
    · cases hget : instrAt prog i with
      | decz c0 k₀ =>
          have hk' : c0 = c ∧ min k₀ prog.length = k := by
            simpa [clampInstr, hget] using hk
          rw [← hk'.2]
          have hm : min k₀ prog.length ≤ prog.length := Nat.min_le_right k₀ prog.length
          have hlen' : (normalize prog).length = prog.length + 1 := by
            dsimp [normalize]
            simp
          omega
      | jump k₀ =>
          simp [clampInstr, hget] at hk ⊢
      | _ => simp [clampInstr, hget] at hk ⊢
    · cases hget : instrAt prog i with
      | decz c0 k₀ =>
          simp [clampInstr, hget] at hk ⊢
      | jump k₀ =>
          have hk' : min k₀ prog.length = k := by
            simpa [clampInstr, hget] using hk
          rw [← hk']
          have hm : min k₀ prog.length ≤ prog.length := Nat.min_le_right k₀ prog.length
          have hlen' : (normalize prog).length = prog.length + 1 := by
            dsimp [normalize]
            simp
          omega
      | _ => simp [clampInstr, hget] at hk ⊢
  · intro i hi
    have hlen : (normalize prog).length = prog.length + 1 := by
      dsimp [normalize]
      simp
    rw [hlen] at hi
    by_cases hlt : i < prog.length
    · right
      omega
    · have hge : prog.length ≤ i := by omega
      left
      exact instrAt_normalize_ge prog i hge

end Completeness

end LeanFunge
