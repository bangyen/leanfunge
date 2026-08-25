/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import Mathlib.Computability.Primrec.List
import LeanFunge.Theory.Completeness.Encodable
import LeanFunge.Theory.Completeness.Layout

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

end Completeness

end LeanFunge
