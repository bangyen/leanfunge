/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanFunge.Theory.Completeness.LayoutHeader

/-!
# Header-Row Lookup Tests
-/

namespace LeanFunge.Tests

open LeanFunge
open LeanFunge.Completeness

/-- The transfer program's decz block places a `>` turn on its header row. -/
example : (playfieldOf layoutProgram).get 7 1 = '>' := by
  have ht : ∀ c : Fin 2, ∀ k : ℕ,
      (layoutProgram.getD 1 .halt = .decz c k ∨ layoutProgram.getD 1 .halt = .jump k) →
        k < layoutProgram.length := by
    intro c k hk
    fin_cases c
    · rcases hk with hk | hk
      · have hk3 : k = 3 := by
          change layoutProgram.getD 1 .halt = .decz 0 k at hk
          simp at hk
          injection hk with h0 hk3
          omega
        rw [hk3]
        decide
      · change layoutProgram.getD 1 .halt = .jump k at hk
        simp at hk
        cases hk
    · rcases hk with hk | hk
      · change layoutProgram.getD 1 .halt = .decz 1 k at hk
        simp at hk
        injection hk with h0 hk3
        have h01 : (0 : Fin 2) ≠ 1 := by decide
        exfalso
        exact h01 h0
      · change layoutProgram.getD 1 .halt = .jump k at hk
        simp at hk
        cases hk
  have h := playfield_header_get layoutProgram 7 1 (by decide) ht (by decide)
  simpa only [h, corridorRowAt] using (by decide : corridorRowAt layoutProgram 7 1 = '>')

end LeanFunge.Tests
