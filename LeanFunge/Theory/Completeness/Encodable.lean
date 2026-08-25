/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import Mathlib.Computability.Primrec.List
import LeanFunge.Theory.Completeness.TwoCounter

/-!
# Encodings for Two-Counter Machines

`ComputablePred` requires its domain to be `Primcodable` — encodable as a
natural number. This module supplies the instances the undecidability reduction
needs (see `UNDECIDABILITY.md`): the two-counter machine syntax and state, and
`Char`, which mathlib does not provide.

Each instance goes through an explicit `Equiv` into an already-`Primcodable`
type, since there is no `deriving` handler for `Primcodable`. `CMProgram` is a
`List CMInstr`, so it comes free from the `List` instance.

## Main definitions

* `CMInstr.equivSum`: `CMInstr` as a sum of its four constructors' payloads.
* `CMState.equivProd`: `CMState` as a triple of naturals.

## Instances

* `Primcodable Char`: via the Unicode scalar value.
* `Primcodable CMInstr`, `Primcodable CMState`.
-/

namespace LeanFunge

namespace Completeness

/-! ### `Char`

`Char` is a `UInt32` paired with a validity proof. Mathlib has no `Primcodable`
(nor even `Encodable`) instance for it, and the only builder available is
`Primcodable.ofEquiv`, which needs a genuine `Equiv` — so the route is
`Primcodable.subtype`, which in turn requires a `PrimrecPred` for
`UInt32.isValidChar`. That is left for the module that needs it (piece C of
`UNDECIDABILITY.md`); the two-counter instances below do not depend on it. -/

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
