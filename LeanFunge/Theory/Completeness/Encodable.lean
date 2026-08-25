/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanFunge.Theory.Completeness.TwoCounter
import Mathlib.Computability.Primrec.List

/-!
# Encodings for Two-Counter Machines

`ComputablePred` requires its domain to be `Primcodable` — encodable as a
natural number. This module supplies the instances the undecidability reduction
needs (see `UNDECIDABILITY.md`): the two-counter machine syntax and state, and
`Char`, which mathlib does not provide — and hence `List (List Char)`, the
playfield text form that the compiler emits.

Each instance goes through an explicit `Equiv` into an already-`Primcodable`
type, since there is no `deriving` handler for `Primcodable`. `CMProgram` is a
`List CMInstr`, so it comes free from the `List` instance.

## Main definitions

* `CMInstr.equivSum`: `CMInstr` as a sum of its four constructors' payloads.
* `CMState.equivProd`: `CMState` as a triple of naturals.
* `charEquivSubtype`: `Char` as the valid code points.

## Theorems

* `primrec_isValidChar`: Validity of a code point is primitive recursive.

## Instances

* `Primcodable Char`: via the valid-code-point subtype of `ℕ`.
* `Primcodable CMInstr`, `Primcodable CMState`.
-/

namespace LeanFunge

namespace Completeness

/-! ### `Char` -/

/-- `Char` is exactly the valid Unicode code points. `Char.toNat` and
    `Char.ofNatAux` are mutually inverse on that subtype — unlike `Char.ofNat`,
    which clamps invalid inputs to `'\0'` and so is not injective on `ℕ`. -/
def charEquivSubtype : Char ≃ { n : ℕ // n.isValidChar } where
  toFun c := ⟨c.toNat, c.valid⟩
  invFun n := Char.ofNatAux n.1 n.2
  left_inv _ := Char.ext rfl
  right_inv _ := Subtype.ext rfl

/-- Validity of a code point is primitive recursive: it unfolds to a
    disjunction of comparisons against literals, excluding the surrogate
    range. -/
theorem primrec_isValidChar : PrimrecPred (fun n : ℕ => n.isValidChar) :=
  PrimrecPred.or
    (Primrec.nat_lt.comp .id (.const _))
    (PrimrecPred.and
      (Primrec.nat_lt.comp (.const _) .id)
      (Primrec.nat_lt.comp .id (.const _)))

/-- `Primcodable Char`, which mathlib does not provide. `Primcodable.subtype`
    is a `def` rather than an instance, so it is supplied explicitly here. -/
instance : Primcodable Char :=
  letI : Primcodable { n : ℕ // n.isValidChar } :=
    Primcodable.subtype primrec_isValidChar
  Primcodable.ofEquiv _ charEquivSubtype

/-! ### Two-counter machine syntax -/

/-- `CMInstr` as a sum of its constructors' payloads: `inc c`, `decz c k`,
    `jump k`, and the payload-free `halt`. -/
def CMInstr.equivSum : CMInstr ≃ Fin 2 ⊕ (Fin 2 × ℕ) ⊕ ℕ ⊕ Unit where
  toFun
    | .inc c => .inl c
    | .decz c k => .inr (.inl (c, k))
    | .jump k => .inr (.inr (.inl k))
    | .halt => .inr (.inr (.inr ()))
  invFun
    | .inl c => .inc c
    | .inr (.inl (c, k)) => .decz c k
    | .inr (.inr (.inl k)) => .jump k
    | .inr (.inr (.inr ())) => .halt
  left_inv := by intro i; cases i <;> rfl
  right_inv := by
    rintro (_ | (_ | (_ | ⟨⟩))) <;> rfl

instance : Primcodable CMInstr :=
  Primcodable.ofEquiv _ CMInstr.equivSum

/-- `CMState` as the triple of its program counter and two counters. -/
def CMState.equivProd : CMState ≃ ℕ × ℕ × ℕ where
  toFun s := (s.pc, s.c1, s.c2)
  invFun t := { pc := t.1, c1 := t.2.1, c2 := t.2.2 }
  left_inv := by intro s; cases s; rfl
  right_inv := by intro t; cases t; rfl

instance : Primcodable CMState :=
  Primcodable.ofEquiv _ CMState.equivProd

end Completeness

end LeanFunge
