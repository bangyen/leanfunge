/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/

/-!
# The Befunge Stack

## Main definitions

* `Stack`: The Befunge data stack (a list of integers, top at the head).
* `Stack.push`: Push a value onto the top of the stack.
* `Stack.pop`: Pop the top of the stack.
* `Stack.top`: The top of the stack.
* `Stack.drop`: Discard the top of the stack.
* `Stack.dup`: Duplicate the top of the stack (`:`).
* `Stack.swap`: Swap the top two elements (`\`).
* `Stack.applyBinary`: Apply a binary operation to the top two elements.
-/

namespace LeanFunge

/-- The Befunge stack: a list of integers with the top at the head. -/
abbrev Stack := List Int

namespace Stack

/-- Push a value onto the top of the stack. -/
def push (s : Stack) (v : Int) : Stack := v :: s

/-- Pop the top of the stack, returning the remaining stack and the value.
    Popping an empty stack yields `0`. -/
def pop (s : Stack) : Stack × Int :=
  match s with
  | [] => ([], 0)
  | v :: rest => (rest, v)

/-- The top of the stack (`0` on the empty stack). -/
def top (s : Stack) : Int :=
  (pop s).2

/-- Discard the top of the stack. -/
def drop (s : Stack) : Stack :=
  match s with
  | [] => []
  | _ :: rest => rest

/-- Duplicate the top of the stack (`:`). -/
def dup (s : Stack) : Stack :=
  match s with
  | [] => [0]
  | v :: rest => v :: v :: rest

/-- Swap the top two elements of the stack (`\`). -/
def swap (s : Stack) : Stack :=
  match s with
  | a :: b :: rest => b :: a :: rest
  | a :: [] => [0, a]
  | [] => [0]

/-- Apply a binary operation to the top two elements (underflow yields `0`).
    The first argument of `op` is the second-popped value. -/
def applyBinary (op : Int → Int → Int) (s : Stack) : Stack :=
  match s with
  | a :: b :: rest => op b a :: rest
  | a :: rest => op 0 a :: rest
  | [] => [op 0 0]

end Stack

end LeanFunge
