/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import Mathlib.Computability.Primrec.List
import LeanFunge.Theory.Completeness.Encodable
import LeanFunge.Theory.Completeness.LayoutCells
import LeanFunge.Theory.Completeness.LayoutRows
import LeanFunge.Theory.Completeness.LayoutSimulationNormalize

/-!
# The Compiler is Primitive Recursive

The undecidability reduction composes a hypothetical decider with the
machine-to-playfield compiler, so the compiler has to be computable. This
module builds that up from the bottom: the per-instruction data, then the
geometry, then the cell lists, then the rows.

Everything is proven at the `Primrec` level, which has the richer combinator
library, and converted to `Computable` at the end with `Primrec.to_comp`.

Functions out of `CMInstr` transport along `CMInstr.equivSum`, since that is
how the `Primcodable` instance is built. Functions defined by recursion on a
block index go through the `entryColumn_foldl` and `blockRow_foldl` closed
forms, since a `Primrec` argument cannot follow the recursion itself.

## Theorems

* `primrec_blockWidth`, `primrec_blockHeight`: The per-instruction geometry.
* `primrec_counterDigit`: The counter digit character.
* `primrec_playfieldRowsOf`: The generated playfield as text.
* `primrec_normalize`: Clamping the targets and appending a `halt`.
-/

namespace LeanFunge

namespace Completeness

open Primrec

/-- The sum type `CMInstr` is encoded through. -/
abbrev InstrSum := Fin 2 ⊕ (Fin 2 × ℕ) ⊕ ℕ ⊕ Unit

/-- The block width, as a function of the encoded instruction. -/
theorem primrec_blockWidth : Primrec blockWidth := by
  have h : blockWidth = (fun i : CMInstr =>
      Sum.elim (fun _ => 3)
        (Sum.elim (fun _ => 5) (Sum.elim (fun _ => 2) (fun _ => 2)))
        (CMInstr.equivSum i)) := by
    funext i; cases i <;> rfl
  rw [h]
  refine Primrec.sumCasesOn (Primrec.of_equiv (α := InstrSum)) (const 3).to₂ ?_
  refine Primrec₂.mk (Primrec.sumCasesOn snd (const 5).to₂ ?_)
  exact Primrec₂.mk (Primrec.sumCasesOn snd (const 2).to₂ (const 2).to₂)

/-- The block height, as a function of the encoded instruction. -/
theorem primrec_blockHeight : Primrec blockHeight := by
  have h : blockHeight = (fun i : CMInstr =>
      Sum.elim (fun _ => 2)
        (Sum.elim (fun _ => 5) (Sum.elim (fun _ => 2) (fun _ => 2)))
        (CMInstr.equivSum i)) := by
    funext i; cases i <;> rfl
  rw [h]
  refine Primrec.sumCasesOn (Primrec.of_equiv (α := InstrSum)) (const 2).to₂ ?_
  refine Primrec₂.mk (Primrec.sumCasesOn snd (const 5).to₂ ?_)
  exact Primrec₂.mk (Primrec.sumCasesOn snd (const 2).to₂ (const 2).to₂)

/-- Reading the instruction at an index. -/
theorem primrec_instrAt : Primrec₂ (fun prog : CMProgram => fun i : ℕ =>
    prog.getD i CMInstr.halt) :=
  Primrec.list_getD CMInstr.halt

/-- The entry column, via its closed form. -/
theorem primrec_entryColumn :
    Primrec (fun p : CMProgram × ℕ => entryColumn p.1 p.2) := by
  refine Primrec.of_eq ?_ (fun p : CMProgram × ℕ => (entryColumn_foldl p.1 p.2).symm)
  refine Primrec.list_foldl
    (f := fun p : CMProgram × ℕ => List.range p.2)
    (g := fun _ : CMProgram × ℕ => (1 : ℕ))
    (h := fun p : CMProgram × ℕ => fun q : ℕ × ℕ =>
      q.1 + blockWidth (p.1.getD q.2 CMInstr.halt))
    (Primrec.list_range.comp Primrec.snd) (Primrec.const 1) ?_
  exact Primrec₂.mk (Primrec.nat_add.comp (Primrec.fst.comp Primrec.snd)
    (primrec_blockWidth.comp
      (primrec_instrAt.comp (Primrec.fst.comp Primrec.fst)
        (Primrec.snd.comp Primrec.snd))))

/-- The block row, via its closed form. -/
theorem primrec_blockRow :
    Primrec (fun p : CMProgram × ℕ => blockRow p.1 p.2) := by
  refine Primrec.of_eq ?_ (fun p : CMProgram × ℕ => (blockRow_foldl p.1 p.2).symm)
  refine Primrec.list_foldl
    (f := fun p : CMProgram × ℕ => List.range p.2)
    (g := fun p : CMProgram × ℕ => p.1.length)
    (h := fun p : CMProgram × ℕ => fun q : ℕ × ℕ =>
      q.1 + blockHeight (p.1.getD q.2 CMInstr.halt))
    (Primrec.list_range.comp Primrec.snd)
    (Primrec.list_length.comp Primrec.fst) ?_
  exact Primrec₂.mk (Primrec.nat_add.comp (Primrec.fst.comp Primrec.snd)
    (primrec_blockHeight.comp
      (primrec_instrAt.comp (Primrec.fst.comp Primrec.fst)
        (Primrec.snd.comp Primrec.snd))))

/-- The counter digit character. -/
theorem primrec_counterDigit : Primrec counterDigit := by
  have h : counterDigit = (fun c : Fin 2 => if c = 0 then '2' else '3') := rfl
  rw [h]
  exact Primrec.ite (Primrec.eq.comp Primrec.id (Primrec.const 0))
    (Primrec.const '2') (Primrec.const '3')

/-- The playfield width. -/
theorem primrec_playfieldWidth : Primrec playfieldWidth := by
  refine Primrec.of_eq (primrec_entryColumn.comp
    (Primrec.pair Primrec.id Primrec.list_length)) (fun prog => rfl)

/-- The playfield height. -/
theorem primrec_playfieldHeight : Primrec playfieldHeight := by
  refine Primrec.of_eq (primrec_blockRow.comp
    (Primrec.pair Primrec.id Primrec.list_length)) (fun prog => rfl)

/-- The corridor cells of a jump edge. -/
theorem primrec_corridorCells :
    Primrec (fun p : CMProgram × ℕ × ℕ => corridorCells p.1 p.2.1 p.2.2) := by
  -- the entry columns of source and target, and the branch column
  have hD : Primrec (fun p : CMProgram × ℕ × ℕ => entryColumn p.1 p.2.1) :=
    primrec_entryColumn.comp (Primrec.pair Primrec.fst
      (Primrec.fst.comp Primrec.snd))
  have hDk : Primrec (fun p : CMProgram × ℕ × ℕ => entryColumn p.1 p.2.2) :=
    primrec_entryColumn.comp (Primrec.pair Primrec.fst
      (Primrec.snd.comp Primrec.snd))
  have hW : Primrec (fun p : CMProgram × ℕ × ℕ =>
      blockWidth (p.1.getD p.2.1 CMInstr.halt)) :=
    primrec_blockWidth.comp (primrec_instrAt.comp Primrec.fst
      (Primrec.fst.comp Primrec.snd))
  have hC : Primrec (fun p : CMProgram × ℕ × ℕ =>
      entryColumn p.1 p.2.1 + blockWidth (p.1.getD p.2.1 CMInstr.halt) - 1) :=
    Primrec.nat_sub.comp (Primrec.nat_add.comp hD hW) (Primrec.const 1)
  have hturn : Primrec (fun p : CMProgram × ℕ × ℕ =>
      if entryColumn p.1 p.2.2
          ≥ entryColumn p.1 p.2.1 + blockWidth (p.1.getD p.2.1 CMInstr.halt) - 1
        then '>' else '<') :=
    Primrec.ite (Primrec.nat_le.comp hC hDk)
      (Primrec.const '>') (Primrec.const '<')
  refine Primrec.of_eq ?_ (fun p => rfl)
  exact Primrec.list_cons.comp
    (Primrec.pair (Primrec.pair hC (Primrec.fst.comp Primrec.snd)) hturn)
    (Primrec.list_cons.comp
      (Primrec.pair (Primrec.pair hDk (Primrec.fst.comp Primrec.snd))
        (Primrec.const 'v'))
      (Primrec.const []))

/-! ### Instruction accessors

`blockCellList` matches on the instruction and uses its payload. Splitting the
match into a test and total accessors lets the computability proof dispatch with
`ite` and feed each branch the payload it needs. -/

/-- The jump target an instruction names, or zero. -/
def CMInstr.target : CMInstr → ℕ
  | .decz _ k => k
  | .jump k => k
  | _ => 0

/-- The counter an instruction names, or zero. -/
def CMInstr.counter : CMInstr → Fin 2
  | .inc c => c
  | .decz c _ => c
  | _ => 0

/-- Whether an instruction is an `inc`. -/
def CMInstr.isInc : CMInstr → Bool
  | .inc _ => true
  | _ => false

/-- Whether an instruction is a `decz`. -/
def CMInstr.isDecz : CMInstr → Bool
  | .decz _ _ => true
  | _ => false

/-- Whether an instruction is a `jump`. -/
def CMInstr.isJump : CMInstr → Bool
  | .jump _ => true
  | _ => false

/-- `blockCellList` restated as nested tests on the instruction, so that the
    computability proof can dispatch without matching. -/
theorem blockCellList_cases (prog : CMProgram) (i : ℕ) :
    blockCellList prog i =
      (if (prog.getD i .halt).isInc then
        [((entryColumn prog i, blockRow prog i), '>'),
         ((entryColumn prog i + 1, blockRow prog i),
           counterDigit (prog.getD i .halt).counter),
         ((entryColumn prog i + 2, blockRow prog i), '*'),
         ((entryColumn prog i + 3, blockRow prog i), 'v')]
      else if (prog.getD i .halt).isDecz then
        [((entryColumn prog i, blockRow prog i), '>'),
         ((entryColumn prog i + 1, blockRow prog i), ':'),
         ((entryColumn prog i + 2, blockRow prog i),
           counterDigit (prog.getD i .halt).counter),
         ((entryColumn prog i + 3, blockRow prog i), '%'),
         ((entryColumn prog i + 4, blockRow prog i), '|'),
         ((entryColumn prog i + 4, blockRow prog i + 1),
           counterDigit (prog.getD i .halt).counter),
         ((entryColumn prog i + 4, blockRow prog i + 2), '/'),
         ((entryColumn prog i + 4, blockRow prog i + 3), '>'),
         ((entryColumn prog i + 5, blockRow prog i + 3), 'v')]
          ++ corridorCells prog i (prog.getD i .halt).target
      else if (prog.getD i .halt).isJump then
        [((entryColumn prog i, blockRow prog i), '>'),
         ((entryColumn prog i + 1, blockRow prog i), '^')]
          ++ corridorCells prog i (prog.getD i .halt).target
      else
        [((entryColumn prog i, blockRow prog i), '>'),
         ((entryColumn prog i + 1, blockRow prog i), '@')]) := by
  unfold blockCellList
  cases hget : prog.getD i .halt <;>
    simp [CMInstr.isInc, CMInstr.isDecz, CMInstr.isJump,
      CMInstr.target, CMInstr.counter]

/-- The accessors are primitive recursive. -/
theorem primrec_target : Primrec CMInstr.target := by
  have h : CMInstr.target = (fun i : CMInstr =>
      Sum.elim (fun _ => 0)
        (Sum.elim (fun p : Fin 2 × ℕ => p.2)
          (Sum.elim (fun k : ℕ => k) (fun _ => 0)))
        (CMInstr.equivSum i)) := by
    funext i; cases i <;> rfl
  rw [h]
  refine Primrec.sumCasesOn (Primrec.of_equiv (α := InstrSum)) (Primrec.const 0).to₂ ?_
  refine Primrec₂.mk (Primrec.sumCasesOn Primrec.snd
    (Primrec.snd.comp Primrec.snd).to₂ ?_)
  exact Primrec₂.mk (Primrec.sumCasesOn Primrec.snd Primrec.snd.to₂
    (Primrec.const 0).to₂)

theorem primrec_counter : Primrec CMInstr.counter := by
  have h : CMInstr.counter = (fun i : CMInstr =>
      Sum.elim (fun c : Fin 2 => c)
        (Sum.elim (fun p : Fin 2 × ℕ => p.1)
          (Sum.elim (fun _ : ℕ => (0 : Fin 2)) (fun _ => (0 : Fin 2))))
        (CMInstr.equivSum i)) := by
    funext i; cases i <;> rfl
  rw [h]
  refine Primrec.sumCasesOn (Primrec.of_equiv (α := InstrSum)) Primrec.snd.to₂ ?_
  refine Primrec₂.mk (Primrec.sumCasesOn Primrec.snd
    (Primrec.fst.comp Primrec.snd).to₂ ?_)
  exact Primrec₂.mk (Primrec.sumCasesOn Primrec.snd
    (Primrec.const 0).to₂ (Primrec.const 0).to₂)

theorem primrec_isInc : Primrec CMInstr.isInc := by
  have h : CMInstr.isInc = (fun i : CMInstr =>
      Sum.elim (fun _ => true)
        (Sum.elim (fun _ => false) (Sum.elim (fun _ => false) (fun _ => false)))
        (CMInstr.equivSum i)) := by
    funext i; cases i <;> rfl
  rw [h]
  refine Primrec.sumCasesOn (Primrec.of_equiv (α := InstrSum))
    (Primrec.const true).to₂ ?_
  refine Primrec₂.mk (Primrec.sumCasesOn Primrec.snd (Primrec.const false).to₂ ?_)
  exact Primrec₂.mk (Primrec.sumCasesOn Primrec.snd
    (Primrec.const false).to₂ (Primrec.const false).to₂)

theorem primrec_isDecz : Primrec CMInstr.isDecz := by
  have h : CMInstr.isDecz = (fun i : CMInstr =>
      Sum.elim (fun _ => false)
        (Sum.elim (fun _ => true) (Sum.elim (fun _ => false) (fun _ => false)))
        (CMInstr.equivSum i)) := by
    funext i; cases i <;> rfl
  rw [h]
  refine Primrec.sumCasesOn (Primrec.of_equiv (α := InstrSum))
    (Primrec.const false).to₂ ?_
  refine Primrec₂.mk (Primrec.sumCasesOn Primrec.snd (Primrec.const true).to₂ ?_)
  exact Primrec₂.mk (Primrec.sumCasesOn Primrec.snd
    (Primrec.const false).to₂ (Primrec.const false).to₂)

theorem primrec_isJump : Primrec CMInstr.isJump := by
  have h : CMInstr.isJump = (fun i : CMInstr =>
      Sum.elim (fun _ => false)
        (Sum.elim (fun _ => false) (Sum.elim (fun _ => true) (fun _ => false)))
        (CMInstr.equivSum i)) := by
    funext i; cases i <;> rfl
  rw [h]
  refine Primrec.sumCasesOn (Primrec.of_equiv (α := InstrSum))
    (Primrec.const false).to₂ ?_
  refine Primrec₂.mk (Primrec.sumCasesOn Primrec.snd (Primrec.const false).to₂ ?_)
  exact Primrec₂.mk (Primrec.sumCasesOn Primrec.snd
    (Primrec.const true).to₂ (Primrec.const false).to₂)

/-- A positioned cell at a fixed offset from a block's origin, as a `Primrec`
    builder. Used to assemble each branch's literal cell list. -/
private theorem cell_at {α : Type} [Primcodable α]
    {D Y : α → ℕ} {ch : α → Char} (hD : Primrec D) (hY : Primrec Y)
    (hch : Primrec ch) (dx dy : ℕ) :
    Primrec (fun a : α => ((D a + dx, Y a + dy), ch a)) :=
  Primrec.pair (Primrec.pair (Primrec.nat_add.comp hD (Primrec.const dx))
    (Primrec.nat_add.comp hY (Primrec.const dy))) hch

/-- The cells of a block. The four branches are dispatched on the encoded
    instruction; each is a literal list of positioned characters. -/
theorem primrec_blockCellList :
    Primrec (fun p : CMProgram × ℕ => blockCellList p.1 p.2) := by
  have hD : Primrec (fun p : CMProgram × ℕ => entryColumn p.1 p.2) :=
    primrec_entryColumn
  have hY : Primrec (fun p : CMProgram × ℕ => blockRow p.1 p.2) := primrec_blockRow
  have hI : Primrec (fun p : CMProgram × ℕ => p.1.getD p.2 CMInstr.halt) :=
    primrec_instrAt.comp Primrec.fst Primrec.snd
  -- the corridor of whichever target the instruction names (zero when none)
  have hTarget : Primrec (fun p : CMProgram × ℕ =>
      CMInstr.target (p.1.getD p.2 CMInstr.halt)) := primrec_target.comp hI
  have hCorr : Primrec (fun p : CMProgram × ℕ =>
      corridorCells p.1 p.2 (CMInstr.target (p.1.getD p.2 CMInstr.halt))) :=
    primrec_corridorCells.comp
      (Primrec.pair Primrec.fst (Primrec.pair Primrec.snd hTarget))
  -- the counter digit of whichever counter the instruction names
  have hDig : Primrec (fun p : CMProgram × ℕ =>
      counterDigit (CMInstr.counter (p.1.getD p.2 CMInstr.halt))) :=
    primrec_counterDigit.comp (primrec_counter.comp hI)
  refine Primrec.of_eq ?_ (fun p => (blockCellList_cases p.1 p.2).symm)
  refine Primrec.ite (Primrec.eq.comp (primrec_isInc.comp hI) (Primrec.const true)) ?_ ?_
  · exact Primrec.list_cons.comp (cell_at hD hY (Primrec.const '>') 0 0)
      (Primrec.list_cons.comp (cell_at hD hY hDig 1 0)
        (Primrec.list_cons.comp (cell_at hD hY (Primrec.const '*') 2 0)
          (Primrec.list_cons.comp (cell_at hD hY (Primrec.const 'v') 3 0)
            (Primrec.const []))))
  refine Primrec.ite (Primrec.eq.comp (primrec_isDecz.comp hI) (Primrec.const true)) ?_ ?_
  · refine Primrec.list_append.comp ?_ hCorr
    exact Primrec.list_cons.comp (cell_at hD hY (Primrec.const '>') 0 0)
      (Primrec.list_cons.comp (cell_at hD hY (Primrec.const ':') 1 0)
        (Primrec.list_cons.comp (cell_at hD hY hDig 2 0)
          (Primrec.list_cons.comp (cell_at hD hY (Primrec.const '%') 3 0)
            (Primrec.list_cons.comp (cell_at hD hY (Primrec.const '|') 4 0)
              (Primrec.list_cons.comp (cell_at hD hY hDig 4 1)
                (Primrec.list_cons.comp (cell_at hD hY (Primrec.const '/') 4 2)
                  (Primrec.list_cons.comp (cell_at hD hY (Primrec.const '>') 4 3)
                    (Primrec.list_cons.comp
                      (cell_at hD hY (Primrec.const 'v') 5 3)
                      (Primrec.const [])))))))))
  refine Primrec.ite (Primrec.eq.comp (primrec_isJump.comp hI) (Primrec.const true)) ?_ ?_
  · refine Primrec.list_append.comp ?_ hCorr
    exact Primrec.list_cons.comp (cell_at hD hY (Primrec.const '>') 0 0)
      (Primrec.list_cons.comp (cell_at hD hY (Primrec.const '^') 1 0)
        (Primrec.const []))
  · exact Primrec.list_cons.comp (cell_at hD hY (Primrec.const '>') 0 0)
      (Primrec.list_cons.comp (cell_at hD hY (Primrec.const '@') 1 0)
        (Primrec.const []))

/-- The boot prelude's cells. -/
theorem primrec_bootCells : Primrec bootCells := by
  refine Primrec.of_eq ?_ (fun prog => rfl)
  refine Primrec.list_cons.comp
    (Primrec.pair (Primrec.pair (Primrec.const 0) (Primrec.const 0))
      (Primrec.const '1')) ?_
  exact Primrec.list_cons.comp
    (Primrec.pair (Primrec.pair (primrec_entryColumn.comp
      (Primrec.pair Primrec.id (Primrec.const 0))) (Primrec.const 0))
      (Primrec.const 'v'))
    (Primrec.const [])

/-- Every placed cell of the playfield. -/
theorem primrec_playfieldCells : Primrec playfieldCells := by
  refine Primrec.of_eq ?_ (fun prog => rfl)
  refine Primrec.list_append.comp primrec_bootCells ?_
  refine Primrec.list_flatMap (Primrec.list_range.comp Primrec.list_length) ?_
  exact Primrec₂.mk (primrec_blockCellList.comp
    (Primrec.pair Primrec.fst Primrec.snd))

/-- The last-cell lookup: a fold with a positional test. -/
theorem primrec_lastCellAt :
    Primrec (fun q : (ℕ × ℕ) × List ((ℕ × ℕ) × Char) × (ℕ × ℕ) =>
      lastCellAt q.1.1 q.1.2 ' ' q.2.1 q.2.2.1 q.2.2.2) := by
  refine Primrec.of_eq ?_ (fun q => rfl)
  refine Primrec.list_foldl
    (f := fun q : (ℕ × ℕ) × List ((ℕ × ℕ) × Char) × (ℕ × ℕ) => q.2.1)
    (g := fun _ => ' ')
    (h := fun q : (ℕ × ℕ) × List ((ℕ × ℕ) × Char) × (ℕ × ℕ) =>
      fun r : Char × ((ℕ × ℕ) × Char) =>
        if r.2.1.1 % q.1.1 = q.2.2.1 % q.1.1 ∧ r.2.1.2 % q.1.2 = q.2.2.2 % q.1.2
          then r.2.2 else r.1)
    (Primrec.fst.comp Primrec.snd) (Primrec.const ' ') ?_
  refine Primrec₂.mk (Primrec.ite (PrimrecPred.and ?_ ?_) ?_ ?_)
  · exact Primrec.eq.comp
      (Primrec.nat_mod.comp (Primrec.fst.comp (Primrec.fst.comp
        (Primrec.snd.comp Primrec.snd)))
        (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)))
      (Primrec.nat_mod.comp (Primrec.fst.comp (Primrec.snd.comp
        (Primrec.snd.comp Primrec.fst)))
        (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)))
  · exact Primrec.eq.comp
      (Primrec.nat_mod.comp (Primrec.snd.comp (Primrec.fst.comp
        (Primrec.snd.comp Primrec.snd)))
        (Primrec.snd.comp (Primrec.fst.comp Primrec.fst)))
      (Primrec.nat_mod.comp (Primrec.snd.comp (Primrec.snd.comp
        (Primrec.snd.comp Primrec.fst)))
        (Primrec.snd.comp (Primrec.fst.comp Primrec.fst)))
  · exact Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
  · exact Primrec.fst.comp Primrec.snd

/-- The playfield as text: a nested map over the row and column ranges. -/
theorem primrec_playfieldRowsOf : Primrec playfieldRowsOf := by
  refine Primrec.of_eq ?_ (fun prog => rfl)
  refine Primrec.list_map (Primrec.list_range.comp primrec_playfieldHeight) ?_
  refine Primrec₂.mk ?_
  -- for each row `y`, map the column range
  refine Primrec.list_map
    (Primrec.list_range.comp (primrec_playfieldWidth.comp Primrec.fst)) ?_
  refine Primrec₂.mk ?_
  -- the cell at (x, y) is the last placed cell there
  exact primrec_lastCellAt.comp
    (Primrec.pair
      (Primrec.pair (primrec_playfieldWidth.comp (Primrec.fst.comp Primrec.fst))
        (primrec_playfieldHeight.comp (Primrec.fst.comp Primrec.fst)))
      (Primrec.pair
        (primrec_playfieldCells.comp (Primrec.fst.comp Primrec.fst))
        (Primrec.pair Primrec.snd (Primrec.snd.comp Primrec.fst))))

/-- The instruction constructors are primitive recursive: they are the equiv's
    inverse applied to the corresponding sum injection. -/
theorem primrec_jump : Primrec CMInstr.jump := by
  have h : CMInstr.jump = (fun k : ℕ =>
      CMInstr.equivSum.symm (Sum.inr (Sum.inr (Sum.inl k)))) := by
    funext k; rfl
  rw [h]
  exact (Primrec.of_equiv_symm (α := InstrSum)).comp
    (Primrec.sumInr.comp (Primrec.sumInr.comp Primrec.sumInl))

theorem primrec_decz : Primrec₂ CMInstr.decz := by
  have h : (fun p : Fin 2 × ℕ => CMInstr.decz p.1 p.2)
      = (fun p : Fin 2 × ℕ => CMInstr.equivSum.symm (Sum.inr (Sum.inl p))) := by
    funext p; rfl
  refine Primrec₂.mk (h ▸ ?_)
  exact (Primrec.of_equiv_symm (α := InstrSum)).comp
    (Primrec.sumInr.comp Primrec.sumInl)

/-! ### Normalization

The compiler normalizes before laying out, so that every program — not just the
well-placed ones — maps to a playfield that simulates it. -/

/-- Clamping a jump target into range. -/
theorem primrec_clampInstr :
    Primrec (fun p : ℕ × CMInstr => clampInstr p.1 p.2) := by
  -- rebuild through the accessors: only the target changes
  have h : (fun p : ℕ × CMInstr => clampInstr p.1 p.2)
      = fun p : ℕ × CMInstr =>
        if p.2.isJump then CMInstr.jump (min p.2.target p.1)
        else if p.2.isDecz then CMInstr.decz p.2.counter (min p.2.target p.1)
        else p.2 := by
    funext p
    cases p.2 <;> simp [clampInstr, CMInstr.isJump, CMInstr.isDecz,
      CMInstr.target, CMInstr.counter]
  rw [h]
  have hmin : Primrec (fun p : ℕ × CMInstr => min p.2.target p.1) :=
    Primrec.nat_min.comp (primrec_target.comp Primrec.snd) Primrec.fst
  refine Primrec.ite (Primrec.eq.comp (primrec_isJump.comp Primrec.snd)
    (Primrec.const true)) ?_ ?_
  · exact primrec_jump.comp hmin
  refine Primrec.ite (Primrec.eq.comp (primrec_isDecz.comp Primrec.snd)
    (Primrec.const true)) ?_ Primrec.snd
  exact primrec_decz.comp (primrec_counter.comp Primrec.snd) hmin

/-- Normalization is primitive recursive. -/
theorem primrec_normalize : Primrec normalize := by
  refine Primrec.of_eq ?_ (fun prog => rfl)
  refine Primrec.list_append.comp ?_ (Primrec.const [CMInstr.halt])
  refine Primrec.list_map Primrec.id ?_
  exact Primrec₂.mk (primrec_clampInstr.comp
    (Primrec.pair (Primrec.list_length.comp Primrec.fst) Primrec.snd))

end Completeness

end LeanFunge
