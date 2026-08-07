/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanFunge.Theory.Completeness.LayoutCells
import LeanFunge.Theory.Completeness.LayoutCorridor
import LeanFunge.Theory.Completeness.LayoutCorridorRow
import LeanFunge.Theory.Completeness.LayoutHeader
import LeanFunge.Theory.Completeness.LayoutRowAt
import Mathlib.Tactic

/-!
# The Corridor Along and Drop Cell Cleanliness

The header-row cells of a jump edge are its turn and its drop; every other cell
of the corridor row is a space. The drop column down to the target holds only
spaces and the `v`s of the corridor drops and the preceding block's exit, so a
down run passes through it.

## Theorems

* `corridorAlong_cell`: The header-row cells other than the turn and the drop are spaces.
* `corridorDown_cell`: The cells on the drop column down to the target are spaces or `v`s.
-/

namespace LeanFunge

namespace Completeness

/-- The header-row cells of block `i`, other than its corridor turn and drop,
    are spaces. -/
theorem corridorAlong_cell (prog : CMProgram) (i k : ℕ) (c : Fin 2) (x : ℕ)
    (hi : i < prog.length) (hwell : wellFormed prog)
    (hget : prog.getD i .halt = .decz c k ∨ prog.getD i .halt = .jump k)
    (hxC : x ≠ branchColumn prog i) (hxK : x ≠ entryColumn prog k)
    (hx : x < playfieldWidth prog) :
    (playfieldOf prog).get x i = ' ' := by
  have hcell := playfield_header_get prog x i hi (fun c' k' hk => hwell i hi c' k' hk) hx
  rw [hcell]
  rcases hget with hget | hget
  · have hC' : branchColumn prog i = entryColumn prog i + 4 := by
      rw [branchColumn, hget]
      norm_num [blockWidth]
    have hxC' : x ≠ entryColumn prog i + 4 := by
      intro h
      exact hxC (by rw [hC']; exact h)
    unfold corridorRowAt
    rw [hget]
    simp [hxC', hxK]
  · have hC' : branchColumn prog i = entryColumn prog i + 1 := by
      rw [branchColumn, hget]
      norm_num [blockWidth]
    have hxC' : x ≠ entryColumn prog i + 1 := by
      intro h
      exact hxC (by rw [hC']; exact h)
    unfold corridorRowAt
    rw [hget]
    simp [hxC', hxK]

/-- The cells on the drop column of a jump edge, down to the target, are a `v`
    or a space. -/
theorem corridorDown_cell (prog : CMProgram) (k : ℕ)
    (hk : k < prog.length) (hwell : wellFormed prog) (r : ℕ)
    (hr : r < blockRow prog k) :
    (playfieldOf prog).get (entryColumn prog k) r = ' '
      ∨ (playfieldOf prog).get (entryColumn prog k) r = 'v' := by
  have hDK : entryColumn prog k < playfieldWidth prog := by
    rw [playfieldWidth]
    exact entryColumn_strict_mono prog hk
  by_cases hhead : r < prog.length
  · have hcell := playfield_header_get prog (entryColumn prog k) r (by omega)
      (fun c k' hk' => hwell r (by omega) c k' hk') hDK
    rw [hcell]
    cases hget : prog.getD r .halt with
    | decz c k' =>
        have hneC : entryColumn prog k ≠ entryColumn prog r + 4 := by
          intro h
          have h1 : entryColumn prog r < entryColumn prog k := by omega
          have hrk : r < k := entryColumn_lt_of_lt (prog := prog) (i := r) (j := k) h1
          have hEq : entryColumn prog (r + 1) = entryColumn prog k + 1 := by
            rw [entryColumn_succ, hget]
            norm_num [blockWidth]
            omega
          have h2 : entryColumn prog k < entryColumn prog (r + 1) := by
            rw [hEq]
            omega
          have hkr1 : k < r + 1 := entryColumn_lt_of_lt (prog := prog) (i := k) (j := r + 1) h2
          omega
        by_cases h : entryColumn prog k = entryColumn prog k'
        · right
          unfold corridorRowAt
          rw [hget]
          simp [hneC]
          simp [h]
        · left
          unfold corridorRowAt
          rw [hget]
          simp [hneC]
          simp [h]
    | jump k' =>
        have hneC : entryColumn prog k ≠ entryColumn prog r + 1 := by
          intro h
          have h1 : entryColumn prog r < entryColumn prog k := by omega
          have hrk : r < k := entryColumn_lt_of_lt (prog := prog) (i := r) (j := k) h1
          have hEq : entryColumn prog (r + 1) = entryColumn prog k + 1 := by
            rw [entryColumn_succ, hget]
            norm_num [blockWidth]
            omega
          have h2 : entryColumn prog k < entryColumn prog (r + 1) := by
            rw [hEq]
            omega
          have hkr1 : k < r + 1 := entryColumn_lt_of_lt (prog := prog) (i := k) (j := r + 1) h2
          omega
        by_cases h : entryColumn prog k = entryColumn prog k'
        · right
          unfold corridorRowAt
          rw [hget]
          simp [hneC]
          simp [h]
        · left
          unfold corridorRowAt
          rw [hget]
          simp [hneC]
          simp [h]
    | inc c0 =>
        unfold corridorRowAt
        rw [hget]
        left
        rfl
    | halt =>
        unfold corridorRowAt
        rw [hget]
        left
        rfl
  · have hblk : prog.length ≤ r := by omega
    rcases blockRow_find prog r hblk (by
        have hle : blockRow prog k ≤ playfieldHeight prog := by
          rw [playfieldHeight]
          exact blockRow_mono prog (i := k) (j := prog.length) (by omega)
        omega) with ⟨j, hj, hbj0, hbj1⟩
    have hbk : blockRow prog j < blockRow prog k := by omega
    have hjk : j < k := by
      by_contra h
      have : k ≤ j := by omega
      have hmono : blockRow prog k ≤ blockRow prog j := blockRow_mono prog this
      omega
    have hDjK : entryColumn prog j < entryColumn prog k := entryColumn_strict_mono prog hjk
    let dx := entryColumn prog k - entryColumn prog j
    let dy := r - blockRow prog j
    have hdy : dy < blockHeight (prog.getD j .halt) := by
      dsimp [dy]
      omega
    have hx : entryColumn prog j + dx < playfieldWidth prog := by
      dsimp [dx]
      omega
    have hcell := playfield_row_at prog j (by omega) dx dy (by exact hdy) hx
    have hc1 : entryColumn prog j + dx = entryColumn prog k := by
      dsimp [dx]
      omega
    have hc2 : blockRow prog j + dy = r := by
      dsimp [dy]
      omega
    rw [hc1, hc2] at hcell
    by_cases hjk1 : j + 1 < k
    · have hdxout : blockWidth (prog.getD j .halt) < dx := by
        dsimp [dx]
        have hlt : entryColumn prog (j + 1) < entryColumn prog k := entryColumn_strict_mono prog hjk1
        rw [entryColumn_succ] at hlt
        omega
      rw [blockBodyAt_out (prog.getD j .halt) dx dy hdxout] at hcell
      left
      exact hcell
    · have hjk1' : j + 1 = k := by omega
      have hdxw : dx = blockWidth (prog.getD j .halt) := by
        dsimp [dx]
        have : entryColumn prog k = entryColumn prog (j + 1) := by rw [hjk1']
        have hsucc : entryColumn prog (j + 1) = entryColumn prog j + blockWidth (prog.getD j .halt) := entryColumn_succ prog j
        omega
      rw [hdxw] at hcell
      rcases blockBodyAt_exit_or_space (prog.getD j .halt) dy hdy with hsp | hv
      · left
        rw [hsp] at hcell
        exact hcell
      · right
        rw [hv] at hcell
        exact hcell

end Completeness

end LeanFunge
