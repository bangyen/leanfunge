/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanFunge.Theory.Completeness.LayoutRouting

/-!
# Header Lookups at the Boot Prelude

`playfield_header_get` characterises every column of every header row, but the
boot prelude (see `LayoutBoot`) occupies columns zero and one of row zero, so
that lemma carries a `y = 0 → 2 ≤ x` guard. This module supplies the readings
at the two excluded positions.

The contested position is block zero's entry column on row zero: the prelude
writes a `v` there to turn the pointer down, and a corridor drop into block
zero would write a `v` there too. Both writes agree, so the reading holds
whichever one wins the fold — which is what `playfield_boot_turn` says, without
needing any well-formedness hypothesis.

## Theorems

* `blockCells_v_at_boot`: Any block cell that lands on the boot turn's
  position is itself a downward turn.
* `playfield_boot_turn`: The boot turn reads `v` at block zero's entry column
  on row zero.
* `playfield_drop_get`: A corridor drop cell reads `v`, including on row zero.
-/

namespace LeanFunge

namespace Completeness

/-- Any block cell that lands on the boot turn's position is itself a `v`. The
    only cell a block places in block zero's entry column on row zero is a
    corridor drop, whose character is `v`. -/
theorem blockCells_v_at_boot (prog : CMProgram) (c : (ℕ × ℕ) × Char)
    (hc : c ∈ List.flatMap (fun j => blockCellList prog j) (List.range prog.length))
    (hm : c.1.1 % playfieldWidth prog = 1 % playfieldWidth prog ∧
          c.1.2 % playfieldHeight prog = 0 % playfieldHeight prog) :
    c.2 = 'v' := by
  rcases List.mem_flatMap.1 hc with ⟨j, hj, hcj⟩
  have hjl : j < prog.length := List.mem_range.1 hj
  have hep : ∀ t, 1 ≤ entryColumn prog t := entryColumn_pos prog
  have hbr : prog.length ≤ blockRow prog j := blockRow_ge_length prog j
  have hjpos : 0 < prog.length := by omega
  have hrowlt : blockRow prog j < playfieldHeight prog := by
    unfold playfieldHeight
    exact blockRow_strict_mono prog hjl
  have h1w : 1 < playfieldWidth prog := by
    have := entryColumn_strict_mono prog hjpos
    have he0 : entryColumn prog 0 = 1 := rfl
    unfold playfieldWidth
    omega
  have hnext : entryColumn prog (j + 1) ≤ playfieldWidth prog := by
    unfold playfieldWidth
    rcases Nat.lt_or_ge (j + 1) prog.length with hlt | hge
    · exact le_of_lt (entryColumn_strict_mono prog hlt)
    · have heq : j + 1 = prog.length := by omega
      rw [heq]
  rw [entryColumn_succ] at hnext
  have hbw := blockWidth_two (prog.getD j .halt)
  have hCw : entryColumn prog j + blockWidth (prog.getD j .halt) - 1
      < playfieldWidth prog := by have := hep j; omega
  have hC2 : 2 ≤ entryColumn prog j + blockWidth (prog.getD j .halt) - 1 := by
    have := hep j; omega
  obtain ⟨hmx, hmy⟩ := hm
  rw [Nat.mod_eq_of_lt h1w] at hmx
  cases hget : prog.getD j .halt with
  | inc cc =>
      simp only [blockCellList, hget, blockWidth, List.mem_cons, List.not_mem_nil,
        or_false] at hcj
      exfalso
      rcases hcj with h|h|h|h <;> subst h <;> simp only [] at hmy <;>
        rw [Nat.mod_eq_of_lt hrowlt, Nat.zero_mod] at hmy <;> omega
  | halt =>
      simp only [blockCellList, hget, blockWidth, List.mem_cons, List.not_mem_nil,
        or_false] at hcj
      exfalso
      rcases hcj with h|h <;> subst h <;> simp only [] at hmy <;>
        rw [Nat.mod_eq_of_lt hrowlt, Nat.zero_mod] at hmy <;> omega
  | jump k =>
      rw [hget] at hCw hC2
      simp only [blockWidth] at hCw hC2
      simp only [blockCellList, hget, corridorCells, blockWidth, List.cons_append,
        List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hcj
      rcases hcj with h|h|h|h <;> subst h <;>
        first
          | rfl
          | (exfalso; simp only [] at hmx hmy
             rw [Nat.mod_eq_of_lt hrowlt, Nat.zero_mod] at hmy; omega)
          | (exfalso
             simp only [] at hmx
             rw [Nat.mod_eq_of_lt (by omega)] at hmx
             omega)
  | decz cc k =>
      rw [hget] at hCw hC2
      simp only [blockWidth] at hCw hC2
      simp only [blockCellList, hget, corridorCells, blockWidth, List.cons_append,
        List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hcj
      rcases hcj with h|h|h|h|h|h|h|h|h|h|h <;> subst h <;>
        first
          | rfl
          | (exfalso; simp only [] at hmx hmy
             rw [Nat.mod_eq_of_lt hrowlt, Nat.zero_mod] at hmy; omega)
          | (exfalso
             simp only [] at hmx
             rw [Nat.mod_eq_of_lt (by omega)] at hmx
             omega)

/-- The boot turn reads `v` at block zero's entry column on row zero. Any
    corridor drop that lands there is also a `v`, so the reading holds whichever
    write wins. -/
theorem playfield_boot_turn (prog : CMProgram) (hne : prog ≠ []) :
    (playfieldOf prog).get (entryColumn prog 0) 0 = 'v' := by
  have hjpos : 0 < prog.length := List.length_pos_of_ne_nil hne
  have he0 : entryColumn prog 0 = 1 := rfl
  have h1w : 1 < playfieldWidth prog := by
    have := entryColumn_strict_mono prog hjpos
    unfold playfieldWidth
    omega
  have hhpos : 0 < playfieldHeight prog := by
    have := blockRow_ge_length prog prog.length
    unfold playfieldHeight
    omega
  rw [he0, playfieldOf_get_eq_lastCellAt]
  unfold playfieldCells
  rw [lastCellAt_append]
  have hboot : lastCellAt (playfieldWidth prog) (playfieldHeight prog) ' '
      (bootCells prog) 1 0 = 'v' := by
    unfold bootCells lastCellAt
    simp only [Nat.zero_mod, ↓Char.isValue, he0, List.foldl_cons,
      Nat.zero_eq_one_mod_iff, and_true, and_self, ↓reduceIte, List.foldl_nil]
  rw [hboot]
  exact lastCellAt_const _ _ 'v' _ 1 0 (fun c hc hm =>
    blockCells_v_at_boot prog c hc hm)

/-- A corridor drop cell reads `v`, including on row zero where the boot
    prelude's turn sits at block zero's entry column. Both writes are `v`, so
    the reading is the same whichever wins. -/
theorem playfield_drop_get (prog : CMProgram) (x y : ℕ) (hy : y < prog.length)
    (ht : ∀ c : Fin 2, ∀ k : ℕ,
      (prog.getD y .halt = .decz c k ∨ prog.getD y .halt = .jump k) → k < prog.length)
    (hx : x < playfieldWidth prog) (hdrop : corridorRowAt prog x y = 'v')
    (hne : prog ≠ []) :
    (playfieldOf prog).get x y = 'v' := by
  by_cases hrow : y = 0 ∧ x < 2
  · obtain ⟨hy0, hx2⟩ := hrow
    subst hy0
    have he0 : entryColumn prog 0 = 1 := rfl
    have hep : ∀ j, 1 ≤ entryColumn prog j := entryColumn_pos prog
    -- column zero holds the push, so a drop there is impossible
    have hx1 : x = 1 := by
      rcases Nat.lt_or_ge x 1 with h0 | h1
      · exfalso
        have hx0 : x = 0 := by omega
        subst hx0
        -- column zero is never a corridor column: both candidates are ≥ 1
        unfold corridorRowAt at hdrop
        have hz : (0 : ℕ) ≠ entryColumn prog 0 := by have := hep 0; omega
        cases hget : prog.getD 0 .halt with
        | inc _ => rw [hget] at hdrop; exact absurd hdrop (by simp only [↓Char.isValue, Char.reduceEq, not_false_eq_true])
        | halt => rw [hget] at hdrop; exact absurd hdrop (by simp only [↓Char.isValue, Char.reduceEq, not_false_eq_true])
        | jump k =>
            rw [hget] at hdrop
            have h1 := hep k
            have h2 := hep 0
            simp only [] at hdrop
            rw [if_neg (by omega), if_neg (by omega)] at hdrop
            exact absurd hdrop (by simp only [↓Char.isValue, Char.reduceEq, not_false_eq_true])
        | decz _ k =>
            rw [hget] at hdrop
            have h1 := hep k
            have h2 := hep 0
            simp only [] at hdrop
            rw [if_neg (by omega), if_neg (by omega)] at hdrop
            exact absurd hdrop (by simp only [↓Char.isValue, Char.reduceEq, not_false_eq_true])
      · omega
    subst hx1
    have he0' : entryColumn prog 0 = 1 := rfl
    rw [← he0']
    exact playfield_boot_turn prog hne
  · rw [playfield_header_get prog x y hy ht hx (by
      intro hy0
      by_contra hlt
      exact hrow ⟨hy0, by omega⟩)]
    exact hdrop

end Completeness

end LeanFunge
