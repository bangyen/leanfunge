/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanFunge.Theory.Stack

/-!
# Stack Tests
-/

namespace LeanFunge.Tests

open LeanFunge

example (s : Stack) (v : Int) : Stack.top (Stack.push s v) = v :=
  Stack.top_push s v

example (s : Stack) (v : Int) : Stack.drop (Stack.push s v) = s :=
  Stack.drop_push s v

example (s : Stack) (v : Int) : Stack.dup (v :: s) = v :: v :: s :=
  Stack.dup_push s v

example (a b : Int) (s : Stack) :
    Stack.swap (Stack.swap (a :: b :: s)) = a :: b :: s :=
  Stack.swap_swap a b s

example (a b : Int) (s : Stack) : Stack.top (Stack.swap (a :: b :: s)) = b :=
  Stack.swap_top a b s

example (a b : Int) (s : Stack) :
    Stack.top (Stack.drop (Stack.swap (a :: b :: s))) = a :=
  Stack.swap_second a b s

example (op : Int → Int → Int) (a b : Int) (s : Stack) :
    Stack.applyBinary op (a :: b :: s) = op b a :: s :=
  Stack.applyBinary_top2 op a b s

example (op : Int → Int → Int) (a b : Int) (s : Stack) :
    Stack.drop (Stack.applyBinary op (a :: b :: s)) = s :=
  Stack.applyBinary_drop2 op a b s

example : Stack.pop ([] : Stack) = ([], 0) := Stack.pop_nil

example : Stack.top ([] : Stack) = 0 := Stack.top_nil

example : Stack.drop ([] : Stack) = [] := Stack.drop_nil

example : Stack.dup ([] : Stack) = [0] := Stack.dup_nil

example : Stack.swap ([] : Stack) = [0] := Stack.swap_nil

example (a : Int) : Stack.swap [a] = [0, a] := Stack.swap_singleton a

example (op : Int → Int → Int) : Stack.applyBinary op ([] : Stack) = [op 0 0] :=
  Stack.applyBinary_nil op

example (op : Int → Int → Int) (a : Int) : Stack.applyBinary op [a] = [op 0 a] :=
  Stack.applyBinary_singleton op a

end LeanFunge.Tests
