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

end Stack
end LeanFunge
