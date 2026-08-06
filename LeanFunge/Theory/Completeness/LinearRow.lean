/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanFunge.Theory.Completeness.Linear
import Mathlib.Data.Nat.Notation

/-!
# The Branch-Free Playfield Row

The cells of a branch-free program form a single row; this module proves the
cell facts needed to read instruction `j`'s cells out of the row.

## Theorems

* `linearCells_length_inc`: An `inc` contributes two cells.
* `getD_eq_drop_getD`: Reading at `n` equals reading the `n`-drop at zero.
* `getD_add_getD_drop`: Reading at `n + m` equals reading the `n`-drop at `m`.
* `getD_append_getD`: Reading an append at `n` inside the prefix.
* `linearRowAux_drop`: Dropping the cells of the first `j` increments.
* `linearRowAux_cons`: The cells of a program are the first instruction's cells
  followed by the rest.
* `linearRow_get_first`: The cell at the start of instruction `j`.
* `linearRow_get_second`: The cell after the start of instruction `j`.
* `linearGrid_get`: A grid cell is the corresponding row cell.
* `linearRowAux_nonempty`: The cell list is never empty.
* `linearRow_length`: The row is long enough to reach instruction `j`.
-/

namespace LeanFunge

namespace Completeness

/-- An `inc` contributes two cells. -/
theorem linearCells_length_inc (c : Fin 2) : (linearCells (.inc c)).length = 2 := by
  have hc : c.val = 0 ∨ c.val = 1 := by omega
  rcases hc with h | h
  · have hc0 : c = 0 := Fin.ext h
    rw [hc0]
    rfl
  · have hc1 : c = 1 := Fin.ext h
    rw [hc1]
    rfl

/-- Reading a list at `n` equals reading its `n`-drop at zero. -/
theorem getD_eq_drop_getD {α : Type} (l : List α) (n : ℕ) (a : α) :
    l.getD n a = (l.drop n).getD 0 a := by
  induction l generalizing n with
  | nil => cases n <;> rfl
  | cons x xs ih =>
      cases n with
      | zero => rfl
      | succ n => exact ih n

/-- Reading a list at `n + m` equals reading its `n`-drop at `m`. -/
theorem getD_add_getD_drop {α : Type} (l : List α) (n m : ℕ) (a : α) :
    l.getD (n + m) a = (l.drop n).getD m a := by
  conv =>
    lhs
    rw [getD_eq_drop_getD]
  rw [← List.drop_drop]
  conv =>
    rhs
    rw [getD_eq_drop_getD]

/-- Dropping the cells of the first `j` instructions (all increments) leaves
    the cells of the remaining program. -/
theorem linearRowAux_drop (prog : CMProgram) (j : ℕ)
    (hinc : ∀ i, i < j → prog.getD i .halt = .inc 0 ∨ prog.getD i .halt = .inc 1) :
    (linearRowAux prog).drop (2 * j) = linearRowAux (prog.drop j) := by
  induction j generalizing prog with
  | zero =>
      rw [mul_zero]
      rfl
  | succ j ih =>
      cases prog with
      | nil =>
          exfalso
          rcases hinc 0 (Nat.succ_pos j) with h | h
          · change CMInstr.halt = CMInstr.inc 0 at h
            cases h
          · change CMInstr.halt = CMInstr.inc 1 at h
            cases h
      | cons head rest =>
          cases head with
          | inc c =>
              have hih : (linearRowAux rest).drop (2 * j) = linearRowAux (rest.drop j) := by
                apply ih
                intro i hi
                simpa only [show (.inc c :: rest).getD (i + 1) .halt = rest.getD i .halt by rfl]
                  using hinc (i + 1) (Nat.succ_lt_succ hi)
              rw [show linearRowAux (.inc c :: rest) = linearCells (.inc c) ++ linearRowAux rest by rfl]
              rw [show (.inc c :: rest).drop (j + 1) = rest.drop j by rfl]
              rw [show 2 * (j + 1) = 2 * j + 2 by omega]
              rw [List.drop_append]
              rw [linearCells_length_inc c]
              rw [show 2 * j + 2 - 2 = 2 * j by omega]
              have hnonempty : (linearCells (.inc c)).length ≤ 2 * j + 2 := by
                rw [linearCells_length_inc c]
                omega
              rw [List.drop_eq_nil_of_le hnonempty]
              rw [List.nil_append]
              exact hih
          | decz c k =>
              exfalso
              rcases hinc 0 (Nat.succ_pos j) with h | h <;> cases h
          | jump k =>
              exfalso
              rcases hinc 0 (Nat.succ_pos j) with h | h <;> cases h
          | halt =>
              exfalso
              rcases hinc 0 (Nat.succ_pos j) with h | h <;> cases h

/-- The cells of a program are the first instruction's cells followed by the
    rest. -/
theorem linearRowAux_cons (l : CMProgram) :
    linearRowAux l = linearCells (l.getD 0 .halt) ++ linearRowAux (l.drop 1) := by
  cases l with
  | nil => rfl
  | cons x xs => rfl

/-- Reading `A ++ B` at `n` inside `A` agrees with reading `A`. -/
theorem getD_append_getD {α : Type} (A B : List α) (n : ℕ) (a : α)
    (h : n < A.length) : (A ++ B).getD n a = A.getD n a := by
  induction n generalizing A with
  | zero =>
      cases A with
      | nil =>
          have hlen : ([] : List α).length = 0 := rfl
          omega
      | cons x xs => rfl
  | succ n ih =>
      cases A with
      | nil =>
          have hlen : ([] : List α).length = 0 := rfl
          omega
      | cons x xs =>
          rw [show (x :: xs).getD (n + 1) a = xs.getD n a by rfl]
          rw [show ((x :: xs) ++ B).getD (n + 1) a = (xs ++ B).getD n a by rfl]
          have hlt : n < xs.length := by
            rw [List.length_cons] at h
            omega
          exact ih xs hlt

/-- The cell at the start of instruction `j` is the first cell of its own
    cells. -/
theorem linearRow_get_first (prog : CMProgram) (j : ℕ)
    (hinc : ∀ i, i < j → prog.getD i .halt = .inc 0 ∨ prog.getD i .halt = .inc 1)
    (hjinc : prog.getD j .halt = .inc 0 ∨ prog.getD j .halt = .inc 1) :
    (linearRow prog).getD (1 + 2 * j) ' ' = (linearCells (prog.getD j .halt)).getD 0 ' ' := by
  rcases hjinc with h0 | h1
  · rw [h0]
    unfold linearRow
    rw [show ('>' :: linearRowAux prog).getD (1 + 2 * j) ' ' = (linearRowAux prog).getD (2 * j) ' ' by
        rw [show 1 + 2 * j = Nat.succ (2 * j) by omega]
        rfl]
    rw [show 2 * j = 2 * j + 0 by omega]
    rw [getD_add_getD_drop]
    rw [linearRowAux_drop prog j hinc]
    rw [linearRowAux_cons]
    rw [show (prog.drop j).getD 0 .halt = prog.getD j .halt by rw [← getD_eq_drop_getD prog j .halt]]
    rw [h0]
    exact getD_append_getD (linearCells (.inc 0)) (linearRowAux ((prog.drop j).drop 1)) 0 ' ' (by decide)
  · rw [h1]
    unfold linearRow
    rw [show ('>' :: linearRowAux prog).getD (1 + 2 * j) ' ' = (linearRowAux prog).getD (2 * j) ' ' by
        rw [show 1 + 2 * j = Nat.succ (2 * j) by omega]
        rfl]
    rw [show 2 * j = 2 * j + 0 by omega]
    rw [getD_add_getD_drop]
    rw [linearRowAux_drop prog j hinc]
    rw [linearRowAux_cons]
    rw [show (prog.drop j).getD 0 .halt = prog.getD j .halt by rw [← getD_eq_drop_getD prog j .halt]]
    rw [h1]
    exact getD_append_getD (linearCells (.inc 1)) (linearRowAux ((prog.drop j).drop 1)) 0 ' ' (by decide)

/-- The cell after the start of instruction `j` is the second cell of its own
    cells. -/
theorem linearRow_get_second (prog : CMProgram) (j : ℕ)
    (hinc : ∀ i, i < j → prog.getD i .halt = .inc 0 ∨ prog.getD i .halt = .inc 1)
    (hjinc : prog.getD j .halt = .inc 0 ∨ prog.getD j .halt = .inc 1) :
    (linearRow prog).getD (2 + 2 * j) ' ' = (linearCells (prog.getD j .halt)).getD 1 ' ' := by
  rcases hjinc with h0 | h1
  · rw [h0]
    unfold linearRow
    rw [show ('>' :: linearRowAux prog).getD (2 + 2 * j) ' ' = (linearRowAux prog).getD (2 * j + 1) ' ' by
        rw [show 2 + 2 * j = Nat.succ (2 * j + 1) by omega]
        rfl]
    rw [getD_add_getD_drop]
    rw [linearRowAux_drop prog j hinc]
    rw [linearRowAux_cons]
    rw [show (prog.drop j).getD 0 .halt = prog.getD j .halt by rw [← getD_eq_drop_getD prog j .halt]]
    rw [h0]
    exact getD_append_getD (linearCells (.inc 0)) (linearRowAux ((prog.drop j).drop 1)) 1 ' ' (by decide)
  · rw [h1]
    unfold linearRow
    rw [show ('>' :: linearRowAux prog).getD (2 + 2 * j) ' ' = (linearRowAux prog).getD (2 * j + 1) ' ' by
        rw [show 2 + 2 * j = Nat.succ (2 * j + 1) by omega]
        rfl]
    rw [getD_add_getD_drop]
    rw [linearRowAux_drop prog j hinc]
    rw [linearRowAux_cons]
    rw [show (prog.drop j).getD 0 .halt = prog.getD j .halt by rw [← getD_eq_drop_getD prog j .halt]]
    rw [h1]
    exact getD_append_getD (linearCells (.inc 1)) (linearRowAux ((prog.drop j).drop 1)) 1 ' ' (by decide)

/-- A grid cell is the corresponding row cell. -/
theorem linearGrid_get (prog : CMProgram) (k : ℕ)
    (hk : k < (linearRow prog).length) :
    (linearGrid prog).get k 0 = (linearRow prog).getD k ' ' := by
  unfold linearGrid linearRow Grid.get Grid.ofRows
  simp only [Nat.zero_mod, List.getD_cons_zero]
  change (linearRow prog).getD (k % (linearRow prog).length) ' ' = (linearRow prog).getD k ' '
  rw [Nat.mod_eq_of_lt hk]

/-- The cell list is never empty. -/
theorem linearRowAux_nonempty (prog : CMProgram) : (linearRowAux prog).length ≠ 0 := by
  induction prog with
  | nil => norm_num [linearRowAux]
  | cons i rest ih =>
      rw [linearRowAux]
      rw [List.length_append]
      omega

/-- The row is long enough to reach instruction `j`. -/
theorem linearRow_length (prog : CMProgram) (j : ℕ)
    (hinc : ∀ i, i < j → prog.getD i .halt = .inc 0 ∨ prog.getD i .halt = .inc 1) :
    1 + 2 * j < (linearRow prog).length := by
  unfold linearRow
  rw [List.length_cons]
  have hdrop : (linearRowAux prog).length = 2 * j + ((linearRowAux prog).drop (2 * j)).length := by
    have hd : (linearRowAux prog).drop (2 * j) = linearRowAux (prog.drop j) :=
      linearRowAux_drop prog j hinc
    have hnon : ((linearRowAux prog).drop (2 * j)).length ≠ 0 := by
      rw [hd]
      exact linearRowAux_nonempty (prog.drop j)
    have hld : ((linearRowAux prog).drop (2 * j)).length = (linearRowAux prog).length - 2 * j :=
      List.length_drop
    omega
  rw [hdrop]
  have hnon2 : ((linearRowAux prog).drop (2 * j)).length ≠ 0 := by
    rw [linearRowAux_drop prog j hinc]
    exact linearRowAux_nonempty (prog.drop j)
  omega

end Completeness

end LeanFunge
