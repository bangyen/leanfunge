/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanFunge.Core.Stack

/-!
# Stack Algebra

## Theorems

* `pop_push`: Popping immediately after pushing returns the original stack.
* `top_push`: The top of a stack after a push is the pushed value.
* `drop_push`: Dropping immediately after pushing returns the original stack.
* `dup_push`: Duplicating pushes a copy of the top value.
* `swap_swap`: Swapping is an involution.
* `swap_top`: Swapping places the old second element on top.
* `swap_second`: Swapping places the old top second.
* `applyBinary_top2`: A binary operation on two elements pushes `op b a`.
* `applyBinary_drop2`: A binary operation consumes exactly two elements.
* `pop_nil`: Popping the empty stack yields the empty stack and zero.
* `top_nil`: The top of the empty stack is zero.
* `drop_nil`: Dropping from the empty stack leaves it empty.
* `dup_nil`: Duplicating the empty stack pushes a single zero.
* `swap_nil`: Swapping the empty stack pushes a single zero.
* `swap_singleton`: Swapping a one-element stack fills the missing element
  with zero.
* `applyBinary_nil`: A binary operation on the empty stack applies it to two
  zeros.
* `applyBinary_singleton`: A binary operation on a one-element stack supplies
  zero as the second-popped operand.
-/

namespace LeanFunge
namespace Stack

/-- Popping immediately after pushing returns the original stack. -/
theorem pop_push (s : Stack) (v : Int) : Stack.pop (Stack.push s v) = (s, v) :=
  rfl

/-- The top of a stack after a push is the pushed value. -/
theorem top_push (s : Stack) (v : Int) : Stack.top (Stack.push s v) = v :=
  rfl

/-- Dropping immediately after pushing returns the original stack. -/
theorem drop_push (s : Stack) (v : Int) : Stack.drop (v :: s) = s :=
  rfl

/-- Duplicating pushes a copy of the top value. -/
theorem dup_push (s : Stack) (v : Int) : Stack.dup (v :: s) = v :: v :: s :=
  rfl

/-- Swapping is an involution. -/
theorem swap_swap (a b : Int) (s : Stack) :
    Stack.swap (Stack.swap (a :: b :: s)) = a :: b :: s :=
  rfl

/-- Swapping places the old second element on top. -/
theorem swap_top (a b : Int) (s : Stack) : Stack.top (Stack.swap (a :: b :: s)) = b :=
  rfl

/-- Swapping places the old top second. -/
theorem swap_second (a b : Int) (s : Stack) :
    Stack.top (Stack.drop (Stack.swap (a :: b :: s))) = a :=
  rfl

/-- A binary operation on two elements pushes `op b a`. -/
theorem applyBinary_top2 (op : Int → Int → Int) (a b : Int) (s : Stack) :
    Stack.applyBinary op (a :: b :: s) = op b a :: s :=
  rfl

/-- A binary operation consumes exactly two elements. -/
theorem applyBinary_drop2 (op : Int → Int → Int) (a b : Int) (s : Stack) :
    Stack.drop (Stack.applyBinary op (a :: b :: s)) = s :=
  rfl

/-! ### Underflow

Befunge-93 leaves the behaviour of the stack instructions on an empty or short
stack unspecified. This formalization fills every missing operand with `0`;
the lemmas below pin that choice down for each accessor. -/

/-- Popping the empty stack yields the empty stack and `0`. -/
theorem pop_nil : Stack.pop ([] : Stack) = ([], 0) :=
  rfl

/-- The top of the empty stack is `0`. -/
theorem top_nil : Stack.top ([] : Stack) = 0 :=
  rfl

/-- Dropping from the empty stack leaves it empty. -/
theorem drop_nil : Stack.drop ([] : Stack) = [] :=
  rfl

/-- Duplicating the empty stack pushes a single `0`. -/
theorem dup_nil : Stack.dup ([] : Stack) = [0] :=
  rfl

/-- Swapping the empty stack pushes a single `0`. -/
theorem swap_nil : Stack.swap ([] : Stack) = [0] :=
  rfl

/-- Swapping a one-element stack fills the missing element with `0`, leaving
    the original value on top. -/
theorem swap_singleton (a : Int) : Stack.swap [a] = [0, a] :=
  rfl

/-- A binary operation on the empty stack applies it to two zeros. -/
theorem applyBinary_nil (op : Int → Int → Int) :
    Stack.applyBinary op ([] : Stack) = [op 0 0] :=
  rfl

/-- A binary operation on a one-element stack supplies `0` as the
    second-popped operand — the first argument of `op`. So `-` on `[5]`
    computes `0 - 5 = -5`. -/
theorem applyBinary_singleton (op : Int → Int → Int) (a : Int) :
    Stack.applyBinary op [a] = [op 0 a] :=
  rfl

end Stack

end LeanFunge
