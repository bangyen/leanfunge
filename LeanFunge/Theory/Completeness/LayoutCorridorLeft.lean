/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanFunge.Theory.Completeness.LayoutCells
import LeanFunge.Theory.Completeness.LayoutCorridorCell
import LeanFunge.Theory.Completeness.LayoutCorridorRow
import LeanFunge.Theory.Completeness.LayoutCorridorRun
import LeanFunge.Theory.Completeness.LayoutHeader
import LeanFunge.Theory.Direction
import LeanFunge.Theory.Run.Relational
import LeanFunge.Theory.Step
import Mathlib.Tactic

/-!
# The Corridor Route, Left Turn

The route of a jump edge whose target lies before the branch column: the turn points left, and the along segment runs left to the drop.

## Theorems

* `corridorRunLeft`: A jump edge routes the pointer up, left, and down to a target before the branch column.
-/

namespace LeanFunge

namespace Completeness

theorem corridorRunLeft (prog : CMProgram)
    (i k : ℕ) (c : Fin 2) (hi : i < prog.length) (hk : k < prog.length) (hwell : wellFormed prog)
    (hget : prog.getD i .halt = .decz c k ∨ prog.getD i .halt = .jump k)
    (s : State (playfieldWidth prog) (playfieldHeight prog))
    (hsm : s.stringMode = false) (hpc : s.pc = (branchColumn prog i, blockRow prog i - 1))
    (hdir : s.dir = .up) (hgrid : s.grid = playfieldOf prog)
    (hge : ¬(entryColumn prog k ≥ branchColumn prog i)) :
    run ((blockRow prog i - i) + (branchColumn prog i - entryColumn prog k) + (blockRow prog k - i - 1)) s =
      some { s with pc := (entryColumn prog k, blockRow prog k), dir := .down } := by
  let w := playfieldWidth prog
  let h := playfieldHeight prog
  let C := branchColumn prog i
  let Dk := entryColumn prog k
  have hC : C = entryColumn prog i + blockWidth (prog.getD i .halt) - 1 := rfl
  have hCW : C < w := by
    have hmono : entryColumn prog (i + 1) ≤ playfieldWidth prog := by
      rw [playfieldWidth]
      exact entryColumn_mono prog (i + 1) prog.length (by omega)
    rw [entryColumn_succ] at hmono
    dsimp [w] -- no_squeeze: corridor route
    rw [hC]
    have hwi : 1 ≤ blockWidth (prog.getD i .halt) := blockWidth_pos _
    omega
  have hDK : Dk < w := by
    dsimp [w, Dk] -- no_squeeze: corridor route
    rw [playfieldWidth]
    exact entryColumn_strict_mono prog hk
  have hBRi : prog.length ≤ blockRow prog i := blockRow_ge_length prog i
  have hwi2i : 2 ≤ blockWidth (prog.getD i .halt) := by
    cases prog.getD i .halt <;> norm_num [blockWidth]
  have hCneK : C ≠ Dk := by
    by_cases hik : i < k
    · have hmono : entryColumn prog (i + 1) ≤ entryColumn prog k := entryColumn_mono prog (i + 1) k (by omega)
      rw [entryColumn_succ] at hmono
      rw [hC]
      omega
    · have hki : k ≤ i := by omega
      have hmono : entryColumn prog k ≤ entryColumn prog i := entryColumn_mono prog k i hki
      rw [hC]
      omega
  have hblock : blockRow prog i - 1 < h := by
    have hbr : blockRow prog i ≤ h := by
      dsimp [h] -- no_squeeze: corridor route
      rw [playfieldHeight]
      exact blockRow_mono prog (i := i) (j := prog.length) (by omega)
    omega
  have hiH : i + 1 < h := by
    have h1 : blockRow prog (i + 1) ≤ h := by
      dsimp [h] -- no_squeeze: corridor route
      rw [playfieldHeight]
      exact blockRow_mono prog (i := i + 1) (j := prog.length) (by omega)
    have h3 : blockRow prog i < blockRow prog (i + 1) := by
      rw [blockRow_succ]
      have hh : 1 ≤ blockHeight (prog.getD i .halt) := blockHeight_pos _
      omega
    omega
  have hkHlt : blockRow prog k < h := by
    dsimp [h] -- no_squeeze: corridor route
    rw [playfieldHeight]
    exact blockRow_strict_mono prog hk
  have hBRk : prog.length ≤ blockRow prog k := blockRow_ge_length prog k
  let nUp := blockRow prog i - i - 1
  let nAlong := C - Dk - 1
  let downSteps := blockRow prog k - i - 1
  have hUpCount : nUp + 1 = blockRow prog i - i := by
    change (blockRow prog i - i - 1) + 1 = blockRow prog i - i
    omega
  have hAlCount : nAlong + 1 = C - Dk := by
    change (C - Dk - 1) + 1 = C - Dk
    omega
  have hCgt : Dk < C := by omega
  have hCpos : C ≥ 1 := by
    have hwi : 1 ≤ blockWidth (prog.getD i .halt) := blockWidth_pos _
    rw [hC]
    omega
  have hturnCell : (playfieldOf prog).get C i = Direction.char Direction.left := by
    have hcell := playfield_header_get prog C i hi (fun c' k' hk' => hwell i hi c' k' hk') (by exact hCW)
    rw [hcell]
    change corridorRowAt prog (branchColumn prog i) i = Direction.char Direction.left
    rw [corridor_turn prog i k c hget]
    have hge' : ¬(entryColumn prog k ≥ branchColumn prog i) := hge
    simp [Direction.char, hge'] -- no_squeeze: corridor route
  have hdropCell : (playfieldOf prog).get Dk i = 'v' := by
    have hcell := playfield_header_get prog Dk i hi (fun c' k' hk' => hwell i hi c' k' hk') (by exact hDK)
    rw [hcell]
    change corridorRowAt prog (entryColumn prog k) i = 'v'
    rw [corridor_drop prog i k c hget hCneK]
  have hspacesUp : SpacesRun s.grid Direction.up C (blockRow prog i - 1) nUp := by
    intro k' hk'
    have hpos : runPos w h k' Direction.up (C % w, (blockRow prog i - 1) % h) = (C, blockRow prog i - 1 - k') := by
      rw [runPos_up_pos (x := C) (y := blockRow prog i - 1) (k := k') (hx := hCW) (hk := by omega) (hy := hblock)]
    rw [hpos]
    rw [hgrid]
    exact corridorUp_cell prog i (blockRow prog i - 1 - k') hi hwell (by omega) (by omega)
  have hturnUp : s.grid.get (runPos w h nUp Direction.up (C % w, (blockRow prog i - 1) % h)).1
      (runPos w h nUp Direction.up (C % w, (blockRow prog i - 1) % h)).2 = Direction.char Direction.left := by
    have hpos : runPos w h nUp Direction.up (C % w, (blockRow prog i - 1) % h) = (C, i) := by
      rw [runPos_up_pos (x := C) (y := blockRow prog i - 1) (k := nUp) (hx := hCW) (hk := by omega) (hy := hblock)]
      apply Prod.ext
      · rfl
      · dsimp [nUp] -- no_squeeze: corridor route
        omega
    rw [hpos]
    rw [hgrid]
    exact hturnCell
  have hUpRun := run_spaces_turn (w := w) (h := h) C (blockRow prog i - 1) nUp s Direction.up Direction.left
    (by
      rw [hpc]
      congr
      · exact (Nat.mod_eq_of_lt hCW).symm
      · exact (Nat.mod_eq_of_lt hblock).symm) hsm hdir hspacesUp hturnUp
  have hUpPos : stepPos w h Direction.left (runPos w h nUp Direction.up (C % w, (blockRow prog i - 1) % h)) = (C - 1, i) := by
    have hpos : runPos w h nUp Direction.up (C % w, (blockRow prog i - 1) % h) = (C, i) := by
      rw [runPos_up_pos (x := C) (y := blockRow prog i - 1) (k := nUp) (hx := hCW) (hk := by omega) (hy := hblock)]
      apply Prod.ext
      · rfl
      · dsimp [nUp] -- no_squeeze: corridor route
        omega
    rw [hpos]
    rw [stepPos_left_pos w h C i (by omega) hCW (by omega)]
  have hUp : run (nUp + 1) s = some { s with pc := (C - 1, i), dir := .left } := by
    rw [hUpRun]
    simp only [hUpPos]
  have hspacesAl : SpacesRun s.grid Direction.left (C - 1) i nAlong := by
    intro k' hk'
    have hpos : runPos w h k' Direction.left ((C - 1) % w, i % h) = (C - 1 - k', i) := by
      rw [runPos_left_pos (x := C - 1) (y := i) (k := k') (hy := by omega) (hk := by omega) (hx := by omega)]
    rw [hpos]
    rw [hgrid]
    exact corridorAlong_cell prog i k c (C - 1 - k') hi hwell hget (by omega) (by omega) (by omega)
  have hAlRun := run_spaces_turn (w := w) (h := h) (C - 1) i nAlong { s with pc := (C - 1, i), dir := .left }
    Direction.left Direction.down
    (by
      change (C - 1, i) = ((C - 1) % w, i % h)
      congr
      · exact (Nat.mod_eq_of_lt (by omega : C - 1 < w)).symm
      · exact (Nat.mod_eq_of_lt (by omega : i < h)).symm) (by exact hsm) (by rfl) (by simpa using hspacesAl) -- no_squeeze: corridor route
    (by
      have hpos : runPos w h nAlong Direction.left ((C - 1) % w, i % h) = (Dk, i) := by
        rw [runPos_left_pos (x := C - 1) (y := i) (k := nAlong) (hy := by omega) (hk := by omega) (hx := by omega)]
        congr
        · dsimp [nAlong] -- no_squeeze: corridor route
          omega
      rw [hpos]
      rw [hgrid]
      exact hdropCell)
  have hAlPos : stepPos w h Direction.down (runPos w h nAlong Direction.left ((C - 1) % w, i % h)) = (Dk, i + 1) := by
    have hpos : runPos w h nAlong Direction.left ((C - 1) % w, i % h) = (Dk, i) := by
      rw [runPos_left_pos (x := C - 1) (y := i) (k := nAlong) (hy := by omega) (hk := by omega) (hx := by omega)]
      apply Prod.ext
      · dsimp [nAlong] -- no_squeeze: corridor route
        omega
      · rfl
    rw [hpos]
    rw [stepPos_down w h Dk i (by omega) (by omega)]
  have hAl : run (nAlong + 1) { s with pc := (C - 1, i), dir := .left } =
      some { s with pc := (Dk, i + 1), dir := .down } := by
    rw [hAlRun]
    simp only [hAlPos]
  have hspacesDown : ∀ k' : ℕ, k' < downSteps →
      s.grid.get (runPos w h k' Direction.down (Dk % w, (i + 1) % h)).1
        (runPos w h k' Direction.down (Dk % w, (i + 1) % h)).2 = ' '
        ∨ s.grid.get (runPos w h k' Direction.down (Dk % w, (i + 1) % h)).1
          (runPos w h k' Direction.down (Dk % w, (i + 1) % h)).2 = 'v' := by
    intro k' hk'
    have hpos : runPos w h k' Direction.down (Dk % w, (i + 1) % h) = (Dk, i + 1 + k') := by
      rw [runPos_down_pos (x := Dk) (y := i + 1) (k := k') (hx := hDK) (hb := by
          have h1 : i + 1 + k' ≤ blockRow prog k := by omega
          omega)]
    rw [hpos]
    rw [hgrid]
    exact corridorDown_cell prog k hk hwell (i + 1 + k') (by omega)
  have hDown := run_down { s with pc := (Dk, i + 1), dir := .down } downSteps Dk (i + 1)
    (by exact hsm)
    (by
      change (Dk, i + 1) = (Dk % w, (i + 1) % h)
      congr
      · exact (Nat.mod_eq_of_lt hDK).symm
      · exact (Nat.mod_eq_of_lt (by omega : i + 1 < h)).symm) (by rfl)
    (by simpa using hspacesDown) -- no_squeeze: corridor route
  have hDownPos : runPos w h downSteps Direction.down (Dk % w, (i + 1) % h) = (Dk, blockRow prog k) := by
    rw [runPos_down_pos (x := Dk) (y := i + 1) (k := downSteps) (hx := hDK) (hb := by
        have : i + 1 + downSteps = blockRow prog k := by
          dsimp [downSteps] -- no_squeeze: corridor route
          omega
        rw [this]
        exact hkHlt)]
    apply Prod.ext
    · rfl
    · dsimp [downSteps] -- no_squeeze: corridor route
      omega
  have hDown : run downSteps { s with pc := (Dk, i + 1), dir := .down } =
      some { s with pc := (Dk, blockRow prog k), dir := .down } := by
    rw [hDown, hDownPos]
  have h12 : run ((nUp + 1) + (nAlong + 1)) s = some { s with pc := (Dk, i + 1), dir := .down } := by
    exact run_append s { s with pc := (C - 1, i), dir := .left }
      (some { s with pc := (Dk, i + 1), dir := .down }) (nUp + 1) (nAlong + 1) hUp hAl
  have h123 : run ((nUp + 1) + (nAlong + 1) + downSteps) s =
      some { s with pc := (Dk, blockRow prog k), dir := .down } := by
    exact run_append s { s with pc := (Dk, i + 1), dir := .down }
      (some { s with pc := (Dk, blockRow prog k), dir := .down }) ((nUp + 1) + (nAlong + 1)) downSteps h12 hDown
  have hcount : (nUp + 1) + (nAlong + 1) + downSteps
      = (blockRow prog i - i) + (C - Dk) + (blockRow prog k - i - 1) := by
    rw [hUpCount, hAlCount]
  rw [← hcount]
  exact h123

end Completeness

end LeanFunge
