/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanFunge.Theory.Completeness.Layout
import LeanFunge.Theory.Completeness.PairEncoding
import LeanFunge.Theory.Completeness.Routing

/-!
# Fall-Through on the Generated Playfield

The fall-through routing of the generated playfield: from a block's exit the
pointer drops down the entry column through the gap to the next block's `>`.
These theorems verify, for a concrete generated playfield, that both the
straight-line fall-through (from an `inc` exit) and the branch-jog fall-through
(from a `decz` decrement) reach the next block's entry.

## Theorems

* `layout_transfer_block0`: The first block executes and falls through.
* `layout_fallthrough_0`: The fall-through from the first exit, symbolically.
* `layout_fallthrough_decz`: The fall-through from the branch jog, symbolically.
-/

namespace LeanFunge

namespace Completeness

/-- The first block executes its increment and the fall-through reaches the
    next block's entry, with the encoded value multiplied by 3. -/
theorem layout_transfer_block0 :
    ((run 6 { State.init (playfieldOf layoutProgram) with
        stack := [Int.ofNat (encode 1 0)] }).map (fun s => (s.stack, s.pc)))
      = some ([Int.ofNat (encode 1 0) * 3], (4, 2)) := by
  decide

/-- The fall-through from the first block's exit: the `v` at `(3, 0)` drops
    through the space at `(3, 1)` to the `>` at `(3, 2)`. -/
theorem layout_fallthrough_0 (s : State (playfieldWidth layoutProgram) (playfieldHeight layoutProgram))
    (hpc : s.pc = (3, 0)) (hdir : s.dir = .down) (hsm : s.stringMode = false)
    (hgrid : s.grid = playfieldOf layoutProgram) :
    run 3 s = some { s with dir := .right, pc := (4, 2) } := by
  have hv : s.grid.get 3 0 = 'v' := by rw [hgrid]; decide
  have h1 : run 1 s = some { s with pc := (3, 1), dir := .down } := by
    rw [show run 1 s = step s by rfl]
    unfold step
    have hdec : decodeChar 'v' = .down := by unfold decodeChar; rfl
    simp only [hsm, hpc, hv, hdec, stepState]
    rw [show stepPos (playfieldWidth layoutProgram) (playfieldHeight layoutProgram) Direction.down (3, 0) = (3, 1) by decide]
  have hsp : s.grid.get 3 1 = ' ' := by rw [hgrid]; decide
  have h2 : run 1 { s with pc := (3, 1), dir := .down } =
      some { s with pc := (3, 2), dir := .down } := by
    rw [show run 1 { s with pc := (3, 1), dir := .down } = step { s with pc := (3, 1), dir := .down } by rfl]
    unfold step
    have hdec : decodeChar ' ' = .nop := by unfold decodeChar; rfl
    simp only [hsm, hsp, hdec, stepState]
    rw [show stepPos (playfieldWidth layoutProgram) (playfieldHeight layoutProgram) Direction.down (3, 1) = (3, 2) by decide]
  have hgt : s.grid.get 3 2 = '>' := by rw [hgrid]; decide
  have h3 : run 1 { s with pc := (3, 2), dir := .down } =
      some { s with pc := (4, 2), dir := .right } := by
    rw [show run 1 { s with pc := (3, 2), dir := .down } = step { s with pc := (3, 2), dir := .down } by rfl]
    unfold step
    have hdec : decodeChar '>' = .right := by unfold decodeChar; rfl
    simp only [hsm, hgt, hdec, stepState]
    rw [show stepPos (playfieldWidth layoutProgram) (playfieldHeight layoutProgram) Direction.right (3, 2) = (4, 2) by decide]
  have h12 : run (1 + 1) s = some { s with pc := (3, 2), dir := .down } := by
    exact run_append s { s with pc := (3, 1), dir := .down }
      (some { s with pc := (3, 2), dir := .down }) 1 1 h1 h2
  have h123 : run (1 + 1 + 1) s = some { s with pc := (4, 2), dir := .right } := by
    exact run_append s { s with pc := (3, 2), dir := .down }
      (some { s with pc := (4, 2), dir := .right }) (1 + 1) 1 h12 h3
  rw [show 3 = 1 + 1 + 1 by omega]
  exact h123

/-- The fall-through from the branch jog: the `v` at `(8, 5)` drops through
    the space at `(8, 6)` to the `>` at `(8, 7)`. -/
theorem layout_fallthrough_decz (s : State (playfieldWidth layoutProgram) (playfieldHeight layoutProgram))
    (hpc : s.pc = (8, 5)) (hsm : s.stringMode = false)
    (hgrid : s.grid = playfieldOf layoutProgram) :
    run 3 s = some { s with dir := .right, pc := (9, 7) } := by
  have hv : s.grid.get 8 5 = 'v' := by rw [hgrid]; decide
  have h1 : run 1 s = some { s with pc := (8, 6), dir := .down } := by
    rw [show run 1 s = step s by rfl]
    unfold step
    have hdec : decodeChar 'v' = .down := by unfold decodeChar; rfl
    simp only [hsm, hpc, hv, hdec, stepState]
    rw [show stepPos (playfieldWidth layoutProgram) (playfieldHeight layoutProgram) Direction.down (8, 5) = (8, 6) by decide]
  have hsp : s.grid.get 8 6 = ' ' := by rw [hgrid]; decide
  have h2 : run 1 { s with pc := (8, 6), dir := .down } =
      some { s with pc := (8, 7), dir := .down } := by
    rw [show run 1 { s with pc := (8, 6), dir := .down } = step { s with pc := (8, 6), dir := .down } by rfl]
    unfold step
    have hdec : decodeChar ' ' = .nop := by unfold decodeChar; rfl
    simp only [hsm, hsp, hdec, stepState]
    rw [show stepPos (playfieldWidth layoutProgram) (playfieldHeight layoutProgram) Direction.down (8, 6) = (8, 7) by decide]
  have hgt : s.grid.get 8 7 = '>' := by rw [hgrid]; decide
  have h3 : run 1 { s with pc := (8, 7), dir := .down } =
      some { s with pc := (9, 7), dir := .right } := by
    rw [show run 1 { s with pc := (8, 7), dir := .down } = step { s with pc := (8, 7), dir := .down } by rfl]
    unfold step
    have hdec : decodeChar '>' = .right := by unfold decodeChar; rfl
    simp only [hsm, hgt, hdec, stepState]
    rw [show stepPos (playfieldWidth layoutProgram) (playfieldHeight layoutProgram) Direction.right (8, 7) = (9, 7) by decide]
  have h12 : run (1 + 1) s = some { s with pc := (8, 7), dir := .down } := by
    exact run_append s { s with pc := (8, 6), dir := .down }
      (some { s with pc := (8, 7), dir := .down }) 1 1 h1 h2
  have h123 : run (1 + 1 + 1) s = some { s with pc := (9, 7), dir := .right } := by
    exact run_append s { s with pc := (8, 7), dir := .down }
      (some { s with pc := (9, 7), dir := .right }) (1 + 1) 1 h12 h3
  rw [show 3 = 1 + 1 + 1 by omega]
  exact h123

end Completeness

end LeanFunge
