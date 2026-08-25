/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanFunge.Theory.Completeness.LayoutBootCells
import LeanFunge.Theory.Completeness.LayoutCells
import LeanFunge.Theory.Completeness.LayoutRouting
import LeanFunge.Theory.Direction
import LeanFunge.Theory.Run.Relational
import LeanFunge.Theory.Step
import Mathlib.Tactic
/-!
# The Corridor Composition

The modular position arithmetic for straight runs inside the playfield, the

turn and drop cell lookups of a jump edge, and the direction-independent step

facts used to compose a corridor run.

The header-row cells of a jump edge are its turn and its drop; every other cell

of the corridor row is a space. The drop column down to the target holds only

spaces and the `v`s of the corridor drops and the preceding block's exit, so a

down run passes through it.

The route of a jump edge whose target lies at or beyond the branch column: the turn
points right, and the along segment runs right to the drop.

The route of a jump edge whose target lies before the branch column: the turn points
left, and the along segment runs left to the drop.

A jump edge routes the pointer up its branch column to the header, across the

corridor row, and down to the target block. `corridor_run` dispatches on the

relative position of the target: `corridorRunRight` routes a target at or

beyond the branch column, `corridorRunLeft` one before it.

## Theorems

* `mod_step_up`: `(b + k * (n - 1)) % n = b - k` for an up-run staying in range.

* `runPos_up_pos`: Iterated up steps land at the un-wrapped row.

* `runPos_right_pos`: Iterated right steps land at the un-wrapped column.

* `runPos_left_pos`: Iterated left steps land at the un-wrapped column.

* `runPos_down_pos`: Iterated down steps land at the un-wrapped row.

* `stepPos_left_pos`: A left step inside the playfield does not wrap.

* `corridor_turn`: The turn cell of a jump edge points toward the target.

* `corridor_drop`: The drop cell of a jump edge is a `v`.

* `corridorAlong_cell`: The header-row cells other than the turn and the drop are spaces.

* `corridorDown_cell`: The cells on the drop column down to the target are spaces or `v`s.

* `corridorRunRight`: A jump edge routes the pointer up, right, and down to a target at
  or beyond the branch column.

* `corridorRunLeft`: A jump edge routes the pointer up, left, and down to a target before
  the branch column.

* `corridor_run`: The up-turn, along-drop, and down segments route the pointer

  from the branch cell to the target's entry.

-/
namespace LeanFunge

namespace Completeness

/-- `(b + k * (n - 1)) % n = b - k`: stepping `k` cells upward (adding `n - 1`
    each time) lands at `b - k` when the result stays above zero. -/
theorem mod_step_up (b k n : ℕ) (hk : k ≤ b) (hb : b - k < n) :
    (b + k * (n - 1)) % n = b - k := by
  have hb' : b = (b - k) + k := by omega
  have hmul : k * n = k * (n - 1) + k := by
    calc
      k * n = k * ((n - 1) + 1) := by congr; omega
      _ = k * (n - 1) + k * 1 := Nat.mul_add k (n - 1) 1
      _ = k * (n - 1) + k := by rw [Nat.mul_one]
  have hz : b + k * (n - 1) = (b - k) + k * n := by
    calc
      b + k * (n - 1) = ((b - k) + k) + k * (n - 1) := by omega
      _ = (b - k) + k * n := by omega
  rw [hz]
  rw [Nat.add_mul_mod_self_right]
  rw [Nat.mod_eq_of_lt hb]

/-- Iterated up steps inside the playfield land at the reduced row. -/
lemma runPos_up_pos (w h : ℕ) (x y k : ℕ) (hx : x < w) (hk : k ≤ y) (hy : y < h) :
    runPos w h k Direction.up (x % w, y % h) = (x, y - k) := by
  have hmod : ∀ r : ℕ, 1 ≤ r → r ≤ h → (r + h - 1) % h = r - 1 := by
    intro r hr1 hrh
    by_cases hrlt : r < h
    · have hz : r + h - 1 = (r - 1) + h := by omega
      rw [hz, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega : r - 1 < h)]
    · have hr : r = h := by omega
      subst r
      have hz : h + h - 1 = (h - 1) + h := by omega
      rw [hz, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega : h - 1 < h)]
  induction k with
  | zero =>
      simp only [runPos]
      congr
      · exact Nat.mod_eq_of_lt hx
      · exact Nat.mod_eq_of_lt hy
  | succ k ih =>
      have hih : runPos w h k Direction.up (x % w, y % h) = (x, y - k) := ih (by omega)
      have hstep : stepPos w h Direction.up (x, y - k) = (x, y - k - 1) := by
        unfold stepPos
        rw [Nat.mod_eq_of_lt hx]
        rw [hmod (y - k) (by omega) (by omega)]
      calc
        runPos w h (k + 1) Direction.up (x % w, y % h)
            = stepPos w h Direction.up (runPos w h k Direction.up (x % w, y % h)) := by
              simp only [runPos]
        _ = stepPos w h Direction.up (x, y - k) := by rw [hih]
        _ = (x, y - k - 1) := hstep
        _ = (x, y - (k + 1)) := by simp only [Nat.sub_sub]

/-- Iterated right steps inside the playfield land at the offset column. -/
lemma runPos_right_pos (w h : ℕ) (x y k : ℕ) (hx : x + k < w) (hy : y < h) :
    runPos w h k Direction.right (x % w, y % h) = (x + k, y) := by
  rw [runPos_right]
  congr
  · rw [Nat.mod_eq_of_lt hx]
  · rw [Nat.mod_eq_of_lt hy]

/-- Iterated left steps inside the playfield land at the reduced column. -/
lemma runPos_left_pos (w h : ℕ) (x y k : ℕ) (hy : y < h) (hk : k ≤ x) (hx : x < w) :
    runPos w h k Direction.left (x % w, y % h) = (x - k, y) := by
  have hmod : ∀ r : ℕ, 1 ≤ r → r ≤ w → (r + w - 1) % w = r - 1 := by
    intro r hr1 hrw
    by_cases hrlt : r < w
    · have hz : r + w - 1 = (r - 1) + w := by omega
      rw [hz, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega : r - 1 < w)]
    · have hr : r = w := by omega
      subst r
      have hz : w + w - 1 = (w - 1) + w := by omega
      rw [hz, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega : w - 1 < w)]
  induction k with
  | zero =>
      simp only [runPos]
      congr
      · exact Nat.mod_eq_of_lt hx
      · exact Nat.mod_eq_of_lt hy
  | succ k ih =>
      have hih : runPos w h k Direction.left (x % w, y % h) = (x - k, y) := ih (by omega)
      have hstep : stepPos w h Direction.left (x - k, y) = (x - k - 1, y) := by
        unfold stepPos
        rw [Nat.mod_eq_of_lt hy]
        rw [hmod (x - k) (by omega) (by omega)]
      calc
        runPos w h (k + 1) Direction.left (x % w, y % h)
            = stepPos w h Direction.left (runPos w h k Direction.left (x % w, y % h)) := by
              simp only [runPos]
        _ = stepPos w h Direction.left (x - k, y) := by rw [hih]
        _ = (x - k - 1, y) := hstep
        _ = (x - (k + 1), y) := by simp only [Nat.sub_sub]

/-- Iterated down steps inside the playfield land at the offset row. -/
lemma runPos_down_pos (w h : ℕ) (x y k : ℕ) (hx : x < w) (hb : y + k < h) :
    runPos w h k Direction.down (x % w, y % h) = (x, y + k) := by
  rw [runPos_down]
  congr
  · rw [Nat.mod_eq_of_lt hx]
  · rw [Nat.mod_eq_of_lt hb]

/-- A left step inside the playfield does not wrap. -/
lemma stepPos_left_pos (w h : ℕ) (p y : ℕ) (hp0 : 0 < p) (hp : p < w) (hy : y < h) :
    stepPos w h Direction.left (p, y) = (p - 1, y) := by
  unfold stepPos
  have hmod : (p + w - 1) % w = p - 1 := by
    have hz : p + w - 1 = (p - 1) + w := by omega
    rw [hz]
    rw [Nat.add_mod_right]
    rw [Nat.mod_eq_of_lt (by omega)]
  rw [hmod, Nat.mod_eq_of_lt hy]

/-- The turn cell of a jump edge on its header row points toward the target. -/
theorem corridor_turn (prog : CMProgram) (i k : ℕ) (c : Fin 2)
    (hget : prog.getD i .halt = .decz c k ∨ prog.getD i .halt = .jump k) :
    corridorRowAt prog (branchColumn prog i) i
      = if entryColumn prog k ≥ branchColumn prog i then '>' else '<' := by
  rcases hget with hget | hget
  · have hCeq : branchColumn prog i = entryColumn prog i + 4 := by
      rw [branchColumn, hget]
      norm_num [blockWidth]
    unfold corridorRowAt
    rw [hget]
    simp only [hCeq, ↓reduceIte, ge_iff_le, ↓Char.isValue]
  · have hCeq : branchColumn prog i = entryColumn prog i + 1 := by
      rw [branchColumn, hget]
      norm_num [blockWidth]
    unfold corridorRowAt
    rw [hget]
    simp only [
      hCeq, ↓reduceIte, ge_iff_le, Order.add_one_le_iff, ↓Char.isValue]

/-- The drop cell of a jump edge on its header row is a `v`. -/
theorem corridor_drop (prog : CMProgram) (i k : ℕ) (c : Fin 2)
    (hget : prog.getD i .halt = .decz c k ∨ prog.getD i .halt = .jump k)
    (hCneK : branchColumn prog i ≠ entryColumn prog k) :
    corridorRowAt prog (entryColumn prog k) i = 'v' := by
  rcases hget with hget | hget
  · unfold corridorRowAt
    rw [hget]
    have hne : entryColumn prog k ≠ entryColumn prog i + 4 := by
      intro h
      exact hCneK (by
        rw [branchColumn, hget]
        norm_num [blockWidth]
        exact h.symm)
    simp only [hne, ↓reduceIte, ↓Char.isValue]
  · unfold corridorRowAt
    rw [hget]
    have hne : entryColumn prog k ≠ entryColumn prog i + 1 := by
      intro h
      exact hCneK (by
        rw [branchColumn, hget]
        norm_num [blockWidth]
        exact h.symm)
    simp only [hne, ↓reduceIte, ↓Char.isValue]

/-- The header-row cells of block `i`, other than its corridor turn and drop,
    are spaces. -/
theorem corridorAlong_cell (prog : CMProgram) (i k : ℕ) (c : Fin 2) (x : ℕ)
    (hi : i < prog.length) (hwell : wellFormed prog)
    (hget : prog.getD i .halt = .decz c k ∨ prog.getD i .halt = .jump k)
    (hxC : x ≠ branchColumn prog i) (hxK : x ≠ entryColumn prog k)
    (hx : x < playfieldWidth prog) (hb : i = 0 → 2 ≤ x) :
    (playfieldOf prog).get x i = ' ' := by
  have hcell := playfield_header_get prog x i hi (fun c' k' hk => hwell i hi c' k' hk) hx hb
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
    simp only [hxC', hxK, ↓reduceIte, ↓Char.isValue]
  · have hC' : branchColumn prog i = entryColumn prog i + 1 := by
      rw [branchColumn, hget]
      norm_num [blockWidth]
    have hxC' : x ≠ entryColumn prog i + 1 := by
      intro h
      exact hxC (by rw [hC']; exact h)
    unfold corridorRowAt
    rw [hget]
    simp only [hxC', hxK, ↓reduceIte, ↓Char.isValue]

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
  by_cases hboot : r = 0 ∧ k = 0
  · -- the boot turn sits at block zero's entry column on row zero
    obtain ⟨hr0, hk0⟩ := hboot
    subst hr0; subst hk0
    exact Or.inr (playfield_boot_turn prog (by
      intro hnil
      rw [hnil] at hk
      exact absurd hk (by simp only [List.length_nil, lt_self_iff_false,
          not_false_eq_true])))
  by_cases hhead : r < prog.length
  · have hcell := playfield_header_get prog (entryColumn prog k) r (by omega)
      (fun c k' hk' => hwell r (by omega) c k' hk') hDK (by
        intro hr0
        have hk0 : k ≠ 0 := by
          intro h; exact hboot ⟨hr0, h⟩
        have hkpos : 0 < k := Nat.pos_of_ne_zero hk0
        have := entryColumn_strict_mono prog hkpos
        have he0 : entryColumn prog 0 = 1 := rfl
        omega)
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
          simp only [
            hneC, ↓reduceIte, ↓Char.isValue, ite_eq_left_iff, Char.reduceEq, imp_false,
            Decidable.not_not]
          simp only [h]
        · left
          unfold corridorRowAt
          rw [hget]
          simp only [hneC, ↓reduceIte, ↓Char.isValue, ite_eq_right_iff, Char.reduceEq, imp_false]
          simp only [h, not_false_eq_true]
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
          simp only [
            hneC, ↓reduceIte, ↓Char.isValue, ite_eq_left_iff, Char.reduceEq, imp_false,
            Decidable.not_not]
          simp only [h]
        · left
          unfold corridorRowAt
          rw [hget]
          simp only [hneC, ↓reduceIte, ↓Char.isValue, ite_eq_right_iff, Char.reduceEq, imp_false]
          simp only [h, not_false_eq_true]
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
      dsimp only [dy]
      omega
    have hx : entryColumn prog j + dx < playfieldWidth prog := by
      dsimp only [dx]
      omega
    have hcell := playfield_row_at prog j (by omega) dx dy (by exact hdy) hx
    have hc1 : entryColumn prog j + dx = entryColumn prog k := by
      dsimp only [dx]
      omega
    have hc2 : blockRow prog j + dy = r := by
      dsimp only [dy]
      omega
    rw [hc1, hc2] at hcell
    by_cases hjk1 : j + 1 < k
    · have hdxout : blockWidth (prog.getD j .halt) < dx := by
        dsimp only [dx]
        have hlt : entryColumn prog (j + 1) < entryColumn prog k :=
          entryColumn_strict_mono prog hjk1
        rw [entryColumn_succ] at hlt
        omega
      rw [blockBodyAt_out (prog.getD j .halt) dx dy hdxout] at hcell
      left
      exact hcell
    · have hjk1' : j + 1 = k := by omega
      have hdxw : dx = blockWidth (prog.getD j .halt) := by
        dsimp only [dx]
        have : entryColumn prog k = entryColumn prog (j + 1) := by rw [hjk1']
        have hsucc : entryColumn prog (j + 1) =
          entryColumn prog j + blockWidth (prog.getD j .halt) := entryColumn_succ prog j
        omega
      rw [hdxw] at hcell
      rcases blockBodyAt_exit_or_space (prog.getD j .halt) dy hdy with hsp | hv
      · left
        rw [hsp] at hcell
        exact hcell
      · right
        rw [hv] at hcell
        exact hcell

theorem corridorRunRight (prog : CMProgram)
    (i k : ℕ) (c : Fin 2) (hi : i < prog.length) (hk : k < prog.length) (hwell : wellFormed prog)
    (hget : prog.getD i .halt = .decz c k ∨ prog.getD i .halt = .jump k)
    (s : State (playfieldWidth prog) (playfieldHeight prog))
    (hsm : s.stringMode = false) (hpc : s.pc = (branchColumn prog i, blockRow prog i - 1))
    (hdir : s.dir = .up) (hgrid : s.grid = playfieldOf prog)
    (hge : entryColumn prog k ≥ branchColumn prog i) :
    run ((blockRow prog i - i) + (entryColumn prog k - branchColumn prog i)
        + (blockRow prog k - i - 1)) s =
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
    dsimp only [w]
    rw [hC]
    have hwi : 1 ≤ blockWidth (prog.getD i .halt) := blockWidth_pos _
    omega
  have hDK : Dk < w := by
    dsimp only [w, Dk]
    rw [playfieldWidth]
    exact entryColumn_strict_mono prog hk
  have hBRi : prog.length ≤ blockRow prog i := blockRow_ge_length prog i
  have hwi2i : 2 ≤ blockWidth (prog.getD i .halt) := by
    cases prog.getD i .halt <;> norm_num [blockWidth]
  have hCneK : C ≠ Dk := by
    by_cases hik : i < k
    · have hmono : entryColumn prog (i + 1) ≤ entryColumn prog k :=
        entryColumn_mono prog (i + 1) k (by omega)
      rw [entryColumn_succ] at hmono
      rw [hC]
      omega
    · have hki : k ≤ i := by omega
      have hmono : entryColumn prog k ≤ entryColumn prog i := entryColumn_mono prog k i hki
      rw [hC]
      omega
  have hblock : blockRow prog i - 1 < h := by
    have hbr : blockRow prog i ≤ h := by
      dsimp only [h]
      rw [playfieldHeight]
      exact blockRow_mono prog (i := i) (j := prog.length) (by omega)
    omega
  have hiH : i + 1 < h := by
    have h1 : blockRow prog (i + 1) ≤ h := by
      dsimp only [h]
      rw [playfieldHeight]
      exact blockRow_mono prog (i := i + 1) (j := prog.length) (by omega)
    have h3 : blockRow prog i < blockRow prog (i + 1) := by
      rw [blockRow_succ]
      have hh : 1 ≤ blockHeight (prog.getD i .halt) := blockHeight_pos _
      omega
    omega
  have hkHlt : blockRow prog k < h := by
    dsimp only [h]
    rw [playfieldHeight]
    exact blockRow_strict_mono prog hk
  have hBRk : prog.length ≤ blockRow prog k := blockRow_ge_length prog k
  let nUp := blockRow prog i - i - 1
  let nAlong := Dk - C - 1
  let downSteps := blockRow prog k - i - 1
  have hUpCount : nUp + 1 = blockRow prog i - i := by
    change (blockRow prog i - i - 1) + 1 = blockRow prog i - i
    omega
  have hAlCount : nAlong + 1 = Dk - C := by
    change (Dk - C - 1) + 1 = Dk - C
    omega
  have hC1 : C + 1 < w := by omega
  have hC1pos : C + 1 ≥ 1 := by omega
  have hCzero : C ≥ 1 := by
    have hwi : 1 ≤ blockWidth (prog.getD i .halt) := blockWidth_pos _
    rw [hC]
    omega
  have hturnCell : (playfieldOf prog).get C i = Direction.char Direction.right := by
    have hcell := playfield_header_get prog C i hi (fun c' k' hk' => hwell i hi c' k' hk')
      (by exact hCW) (fun _ => branchColumn_two prog i)
    rw [hcell]
    change corridorRowAt prog (branchColumn prog i) i = Direction.char Direction.right
    rw [corridor_turn prog i k c hget]
    have hge' : entryColumn prog k ≥ branchColumn prog i := hge
    simp only [Direction.char, hge', ↓reduceIte, ↓Char.isValue]
  have hdropCell : (playfieldOf prog).get Dk i = 'v' := by
    refine playfield_drop_get prog Dk i hi (fun c' k' hk' => hwell i hi c' k' hk')
      (by exact hDK) ?_ (by
        intro hnil
        rw [hnil] at hi
        exact absurd hi (by simp only [List.length_nil, not_lt_zero, not_false_eq_true]))
    change corridorRowAt prog (entryColumn prog k) i = 'v'
    rw [corridor_drop prog i k c hget hCneK]
  have hspacesUp : SpacesRun s.grid Direction.up C (blockRow prog i - 1) nUp := by
    intro k' hk'
    have hpos : runPos w h k' Direction.up (C % w, (blockRow prog i - 1) % h) =
      (C, blockRow prog i - 1 - k') := by
      rw [runPos_up_pos (x := C) (y := blockRow prog i - 1) (k := k')
        (hx := hCW) (hk := by omega) (hy := hblock)]
    rw [hpos]
    rw [hgrid]
    exact corridorUp_cell prog i (blockRow prog i - 1 - k') hi hwell (by omega) (by omega)
  have hturnUp : s.grid.get (runPos w h nUp Direction.up (C % w, (blockRow prog i - 1) % h)).1
      (runPos w h nUp Direction.up (C % w, (blockRow prog i - 1) % h)).2 =
        Direction.char Direction.right := by
    have hpos : runPos w h nUp Direction.up (C % w, (blockRow prog i - 1) % h) = (C, i) := by
      rw [runPos_up_pos (x := C) (y := blockRow prog i - 1) (k := nUp)
        (hx := hCW) (hk := by omega) (hy := hblock)]
      apply Prod.ext
      · rfl
      · dsimp only [nUp]
        omega
    rw [hpos]
    rw [hgrid]
    exact hturnCell
  have hUpRun := run_spaces_turn (w := w) (h := h) C (blockRow prog i - 1) nUp s
    Direction.up Direction.right
    (by
      rw [hpc]
      congr
      · exact (Nat.mod_eq_of_lt hCW).symm
      · exact (Nat.mod_eq_of_lt hblock).symm) hsm hdir hspacesUp hturnUp
  have hUpPos : stepPos w h Direction.right
    (runPos w h nUp Direction.up (C % w, (blockRow prog i - 1) % h)) = (C + 1, i) := by
    have hpos : runPos w h nUp Direction.up (C % w, (blockRow prog i - 1) % h) = (C, i) := by
      rw [runPos_up_pos (x := C) (y := blockRow prog i - 1) (k := nUp)
        (hx := hCW) (hk := by omega) (hy := hblock)]
      apply Prod.ext
      · rfl
      · dsimp only [nUp]
        omega
    rw [hpos]
    rw [stepPos_right w h C i (by omega) (by omega)]
  have hUp : run (nUp + 1) s = some { s with pc := (C + 1, i), dir := .right } := by
    rw [hUpRun]
    simp only [hUpPos]
  have hspacesAl : SpacesRun s.grid Direction.right (C + 1) i nAlong := by
    intro k' hk'
    have hpos : runPos w h k' Direction.right ((C + 1) % w, i % h) = (C + 1 + k', i) := by
      rw [runPos_right_pos (x := C + 1) (y := i) (k := k') (hx := by omega) (hy := by omega)]
    rw [hpos]
    rw [hgrid]
    exact corridorAlong_cell prog i k c (C + 1 + k') hi hwell hget (by omega) (by omega)
      (by omega) (by
        have hC2 : 2 ≤ C := branchColumn_two prog i
        omega)
  have hturnAl : s.grid.get (runPos w h nAlong Direction.right ((C + 1) % w, i % h)).1
      (runPos w h nAlong Direction.right ((C + 1) % w, i % h)).2 = 'v' := by
    have hpos : runPos w h nAlong Direction.right ((C + 1) % w, i % h) = (Dk, i) := by
      rw [runPos_right_pos (x := C + 1) (y := i) (k := nAlong) (hx := by omega) (hy := by omega)]
      apply Prod.ext
      · dsimp only [nAlong]
        omega
      · rfl
    rw [hpos]
    rw [hgrid]
    exact hdropCell
  have hAlRun := run_spaces_v (w := w) (h := h) (C + 1) i nAlong
    { s with pc := (C + 1, i), dir := .right }
    (by
      change (C + 1, i) = ((C + 1) % w, i % h)
      congr
      · exact (Nat.mod_eq_of_lt (by omega : C + 1 < w)).symm
      · exact (Nat.mod_eq_of_lt (by omega : i < h)).symm)
    (by exact hsm) (by rfl) (by simpa only [] using hspacesAl) hturnAl
  have hAlPos : stepPos w h Direction.down
    (runPos w h nAlong Direction.right ((C + 1) % w, i % h)) = (Dk, i + 1) := by
    have hpos : runPos w h nAlong Direction.right ((C + 1) % w, i % h) = (Dk, i) := by
      rw [runPos_right_pos (x := C + 1) (y := i) (k := nAlong) (hx := by omega) (hy := by omega)]
      apply Prod.ext
      · dsimp only [nAlong]
        omega
      · rfl
    rw [hpos]
    rw [stepPos_down w h Dk i (by omega) (by omega)]
  have hAl : run (nAlong + 1) { s with pc := (C + 1, i), dir := .right } =
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
    (by simpa only [↓Char.isValue] using hspacesDown)
  have hDownPos : runPos w h downSteps Direction.down (Dk % w, (i + 1) % h) =
    (Dk, blockRow prog k) := by
    rw [runPos_down_pos (x := Dk) (y := i + 1) (k := downSteps) (hx := hDK) (hb := by
        have : i + 1 + downSteps = blockRow prog k := by
          dsimp only [downSteps]
          omega
        rw [this]
        exact hkHlt)]
    apply Prod.ext
    · rfl
    · dsimp only [downSteps]
      omega
  have hDown : run downSteps { s with pc := (Dk, i + 1), dir := .down } =
      some { s with pc := (Dk, blockRow prog k), dir := .down } := by
    rw [hDown, hDownPos]
  have h12 : run ((nUp + 1) + (nAlong + 1)) s =
    some { s with pc := (Dk, i + 1), dir := .down } := by
    exact run_append s { s with pc := (C + 1, i), dir := .right }
      (some { s with pc := (Dk, i + 1), dir := .down }) (nUp + 1) (nAlong + 1) hUp hAl
  have h123 : run ((nUp + 1) + (nAlong + 1) + downSteps) s =
      some { s with pc := (Dk, blockRow prog k), dir := .down } := by
    exact run_append s { s with pc := (Dk, i + 1), dir := .down }
      (some { s with pc := (Dk, blockRow prog k), dir := .down })
        ((nUp + 1) + (nAlong + 1)) downSteps h12 hDown
  have hcount : (nUp + 1) + (nAlong + 1) + downSteps
      = (blockRow prog i - i) + (Dk - C) + (blockRow prog k - i - 1) := by
    rw [hUpCount, hAlCount]
  rw [← hcount]
  exact h123

theorem corridorRunLeft (prog : CMProgram)
    (i k : ℕ) (c : Fin 2) (hi : i < prog.length) (hk : k < prog.length) (hwell : wellFormed prog)
    (hget : prog.getD i .halt = .decz c k ∨ prog.getD i .halt = .jump k)
    (s : State (playfieldWidth prog) (playfieldHeight prog))
    (hsm : s.stringMode = false) (hpc : s.pc = (branchColumn prog i, blockRow prog i - 1))
    (hdir : s.dir = .up) (hgrid : s.grid = playfieldOf prog)
    (hge : ¬(entryColumn prog k ≥ branchColumn prog i)) :
    run ((blockRow prog i - i) + (branchColumn prog i - entryColumn prog k)
        + (blockRow prog k - i - 1)) s =
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
    dsimp only [w]
    rw [hC]
    have hwi : 1 ≤ blockWidth (prog.getD i .halt) := blockWidth_pos _
    omega
  have hDK : Dk < w := by
    dsimp only [w, Dk]
    rw [playfieldWidth]
    exact entryColumn_strict_mono prog hk
  have hBRi : prog.length ≤ blockRow prog i := blockRow_ge_length prog i
  have hwi2i : 2 ≤ blockWidth (prog.getD i .halt) := by
    cases prog.getD i .halt <;> norm_num [blockWidth]
  have hCneK : C ≠ Dk := by
    by_cases hik : i < k
    · have hmono : entryColumn prog (i + 1) ≤ entryColumn prog k :=
        entryColumn_mono prog (i + 1) k (by omega)
      rw [entryColumn_succ] at hmono
      rw [hC]
      omega
    · have hki : k ≤ i := by omega
      have hmono : entryColumn prog k ≤ entryColumn prog i := entryColumn_mono prog k i hki
      rw [hC]
      omega
  have hblock : blockRow prog i - 1 < h := by
    have hbr : blockRow prog i ≤ h := by
      dsimp only [h]
      rw [playfieldHeight]
      exact blockRow_mono prog (i := i) (j := prog.length) (by omega)
    omega
  have hiH : i + 1 < h := by
    have h1 : blockRow prog (i + 1) ≤ h := by
      dsimp only [h]
      rw [playfieldHeight]
      exact blockRow_mono prog (i := i + 1) (j := prog.length) (by omega)
    have h3 : blockRow prog i < blockRow prog (i + 1) := by
      rw [blockRow_succ]
      have hh : 1 ≤ blockHeight (prog.getD i .halt) := blockHeight_pos _
      omega
    omega
  have hkHlt : blockRow prog k < h := by
    dsimp only [h]
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
    have hcell := playfield_header_get prog C i hi (fun c' k' hk' => hwell i hi c' k' hk')
      (by exact hCW) (fun _ => branchColumn_two prog i)
    rw [hcell]
    change corridorRowAt prog (branchColumn prog i) i = Direction.char Direction.left
    rw [corridor_turn prog i k c hget]
    have hge' : ¬(entryColumn prog k ≥ branchColumn prog i) := hge
    simp only [Direction.char, hge', ↓reduceIte, ↓Char.isValue]
  have hdropCell : (playfieldOf prog).get Dk i = 'v' := by
    refine playfield_drop_get prog Dk i hi (fun c' k' hk' => hwell i hi c' k' hk')
      (by exact hDK) ?_ (by
        intro hnil
        rw [hnil] at hi
        exact absurd hi (by simp only [List.length_nil, not_lt_zero, not_false_eq_true]))
    change corridorRowAt prog (entryColumn prog k) i = 'v'
    rw [corridor_drop prog i k c hget hCneK]
  have hspacesUp : SpacesRun s.grid Direction.up C (blockRow prog i - 1) nUp := by
    intro k' hk'
    have hpos : runPos w h k' Direction.up (C % w, (blockRow prog i - 1) % h) =
      (C, blockRow prog i - 1 - k') := by
      rw [runPos_up_pos (x := C) (y := blockRow prog i - 1) (k := k')
        (hx := hCW) (hk := by omega) (hy := hblock)]
    rw [hpos]
    rw [hgrid]
    exact corridorUp_cell prog i (blockRow prog i - 1 - k') hi hwell (by omega) (by omega)
  have hturnUp : s.grid.get (runPos w h nUp Direction.up (C % w, (blockRow prog i - 1) % h)).1
      (runPos w h nUp Direction.up (C % w, (blockRow prog i - 1) % h)).2 =
        Direction.char Direction.left := by
    have hpos : runPos w h nUp Direction.up (C % w, (blockRow prog i - 1) % h) = (C, i) := by
      rw [runPos_up_pos (x := C) (y := blockRow prog i - 1) (k := nUp)
        (hx := hCW) (hk := by omega) (hy := hblock)]
      apply Prod.ext
      · rfl
      · dsimp only [nUp]
        omega
    rw [hpos]
    rw [hgrid]
    exact hturnCell
  have hUpRun := run_spaces_turn (w := w) (h := h) C (blockRow prog i - 1) nUp s
    Direction.up Direction.left
    (by
      rw [hpc]
      congr
      · exact (Nat.mod_eq_of_lt hCW).symm
      · exact (Nat.mod_eq_of_lt hblock).symm) hsm hdir hspacesUp hturnUp
  have hUpPos : stepPos w h Direction.left
    (runPos w h nUp Direction.up (C % w, (blockRow prog i - 1) % h)) = (C - 1, i) := by
    have hpos : runPos w h nUp Direction.up (C % w, (blockRow prog i - 1) % h) = (C, i) := by
      rw [runPos_up_pos (x := C) (y := blockRow prog i - 1) (k := nUp)
        (hx := hCW) (hk := by omega) (hy := hblock)]
      apply Prod.ext
      · rfl
      · dsimp only [nUp]
        omega
    rw [hpos]
    rw [stepPos_left_pos w h C i (by omega) hCW (by omega)]
  have hUp : run (nUp + 1) s = some { s with pc := (C - 1, i), dir := .left } := by
    rw [hUpRun]
    simp only [hUpPos]
  have hspacesAl : SpacesRun s.grid Direction.left (C - 1) i nAlong := by
    intro k' hk'
    have hpos : runPos w h k' Direction.left ((C - 1) % w, i % h) = (C - 1 - k', i) := by
      rw [runPos_left_pos (x := C - 1) (y := i) (k := k')
        (hy := by omega) (hk := by omega) (hx := by omega)]
    rw [hpos]
    rw [hgrid]
    exact corridorAlong_cell prog i k c (C - 1 - k') hi hwell hget (by omega) (by omega)
      (by omega) (by
        have hek := entryColumn_pos prog k
        omega)
  have hAlRun := run_spaces_turn (w := w) (h := h) (C - 1) i nAlong
    { s with pc := (C - 1, i), dir := .left }
    Direction.left Direction.down
    (by
      change (C - 1, i) = ((C - 1) % w, i % h)
      congr
      · exact (Nat.mod_eq_of_lt (by omega : C - 1 < w)).symm
      · exact (Nat.mod_eq_of_lt (by omega : i < h)).symm)
    (by exact hsm) (by rfl) (by simpa only [] using hspacesAl)
    (by
      have hpos : runPos w h nAlong Direction.left ((C - 1) % w, i % h) = (Dk, i) := by
        rw [runPos_left_pos (x := C - 1) (y := i) (k := nAlong)
          (hy := by omega) (hk := by omega) (hx := by omega)]
        congr
        · dsimp only [nAlong]
          omega
      rw [hpos]
      rw [hgrid]
      exact hdropCell)
  have hAlPos : stepPos w h Direction.down
    (runPos w h nAlong Direction.left ((C - 1) % w, i % h)) = (Dk, i + 1) := by
    have hpos : runPos w h nAlong Direction.left ((C - 1) % w, i % h) = (Dk, i) := by
      rw [runPos_left_pos (x := C - 1) (y := i) (k := nAlong)
        (hy := by omega) (hk := by omega) (hx := by omega)]
      apply Prod.ext
      · dsimp only [nAlong]
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
    (by simpa only [↓Char.isValue] using hspacesDown)
  have hDownPos : runPos w h downSteps Direction.down (Dk % w, (i + 1) % h) =
    (Dk, blockRow prog k) := by
    rw [runPos_down_pos (x := Dk) (y := i + 1) (k := downSteps) (hx := hDK) (hb := by
        have : i + 1 + downSteps = blockRow prog k := by
          dsimp only [downSteps]
          omega
        rw [this]
        exact hkHlt)]
    apply Prod.ext
    · rfl
    · dsimp only [downSteps]
      omega
  have hDown : run downSteps { s with pc := (Dk, i + 1), dir := .down } =
      some { s with pc := (Dk, blockRow prog k), dir := .down } := by
    rw [hDown, hDownPos]
  have h12 : run ((nUp + 1) + (nAlong + 1)) s =
    some { s with pc := (Dk, i + 1), dir := .down } := by
    exact run_append s { s with pc := (C - 1, i), dir := .left }
      (some { s with pc := (Dk, i + 1), dir := .down }) (nUp + 1) (nAlong + 1) hUp hAl
  have h123 : run ((nUp + 1) + (nAlong + 1) + downSteps) s =
      some { s with pc := (Dk, blockRow prog k), dir := .down } := by
    exact run_append s { s with pc := (Dk, i + 1), dir := .down }
      (some { s with pc := (Dk, blockRow prog k), dir := .down })
        ((nUp + 1) + (nAlong + 1)) downSteps h12 hDown
  have hcount : (nUp + 1) + (nAlong + 1) + downSteps
      = (blockRow prog i - i) + (C - Dk) + (blockRow prog k - i - 1) := by
    rw [hUpCount, hAlCount]
  rw [← hcount]
  exact h123

/-- The up-turn, along-drop, and down segments route the pointer from a jump
    edge's branch cell to the target block's entry. -/
theorem corridor_run (prog : CMProgram) (i k : ℕ) (c : Fin 2)
    (hi : i < prog.length) (hk : k < prog.length) (hwell : wellFormed prog)
    (hget : prog.getD i .halt = .decz c k ∨ prog.getD i .halt = .jump k)
    (s : State (playfieldWidth prog) (playfieldHeight prog))
    (hsm : s.stringMode = false) (hpc : s.pc = (branchColumn prog i, blockRow prog i - 1))
    (hdir : s.dir = .up) (hgrid : s.grid = playfieldOf prog) :
    run ((blockRow prog i - i)
        + (if entryColumn prog k ≥ branchColumn prog i then entryColumn prog k - branchColumn prog i
           else branchColumn prog i - entryColumn prog k)
        + (blockRow prog k - i - 1)) s =
      some { s with pc := (entryColumn prog k, blockRow prog k), dir := .down } := by
  by_cases hge : entryColumn prog k ≥ branchColumn prog i
  · have h := corridorRunRight prog i k c hi hk hwell hget s hsm hpc hdir hgrid hge
    rw [show (blockRow prog i - i)
        + (if entryColumn prog k ≥ branchColumn prog i then entryColumn prog k - branchColumn prog i
           else branchColumn prog i - entryColumn prog k)
        + (blockRow prog k - i - 1)
        = (blockRow prog i - i) + (entryColumn prog k - branchColumn prog i)
          + (blockRow prog k - i - 1) by
      simp only [hge, ↓reduceIte] ]
    exact h
  · have h := corridorRunLeft prog i k c hi hk hwell hget s hsm hpc hdir hgrid hge
    rw [show (blockRow prog i - i)
        + (if entryColumn prog k ≥ branchColumn prog i then entryColumn prog k - branchColumn prog i
           else branchColumn prog i - entryColumn prog k)
        + (blockRow prog k - i - 1)
        = (blockRow prog i - i) + (branchColumn prog i - entryColumn prog k)
          + (blockRow prog k - i - 1) by
      simp only [hge, ↓reduceIte] ]
    exact h

end Completeness

end LeanFunge
