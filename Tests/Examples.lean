/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanFunge.Examples

/-!
# Example Program Tests
-/

namespace LeanFunge.Tests

open LeanFunge.Examples

example : (run 26 helloState).map (fun s => s.output) = some "Hello World!" :=
  hello_world_output

example : run 27 helloState = none :=
  hello_world_halts

example : (run 3 arithmeticState).map (fun s => Stack.top s.stack) = some 5 :=
  arithmetic_stack_top

example : (run 4 arithmeticState).map (fun s => s.output) = some "5" :=
  arithmetic_output

example : run 5 arithmeticState = none :=
  arithmetic_halts

example : (run 4 trampState).map (fun s => s.stack) = some [3] :=
  trampoline_skips

example : run 5 trampState = none :=
  trampoline_halts

example : (run 8 putState).map (fun s => s.output) = some "5" :=
  put_get_roundtrip

example : run 9 putState = none :=
  put_get_halts

example : (run 131 countdownState).map (fun s => s.output) = some "321" :=
  countdown_output

example : run 133 countdownState = none :=
  countdown_halts

example : (run 133 factorialState).map (fun s => s.stack) = some [6] :=
  factorial_stack

example : run 134 factorialState = none :=
  factorial_halts

example : (run 4 inputState).map (fun s => s.output) = some "7" :=
  input_output

example : run 5 inputState = none :=
  input_halts

example : (run 2 multiState).map (fun s => s.output) = some "12" :=
  multi_output

example : run 3 multiState = none :=
  multi_halts

example : (run 1 negState).map (fun s => Stack.top s.stack) = some (-3) :=
  neg_stack

example : run 2 negState = none :=
  neg_halts

example : (run 8 selfmodState).map (fun s => s.grid.get 8 0) = some '@' :=
  selfmod_writes

example : run 9 selfmodState = none :=
  selfmod_halts

example : (run 7 execState).map (fun s => s.grid.get 7 0) = some '1' :=
  exec_writes

example : (run 9 execState).map (fun s => s.stack) = some [1] :=
  exec_stack

example : run 10 execState = none :=
  exec_halts

example : (run 2407 quineState).map (fun s => s.output) = some quineStr :=
  quine_output

example : run 2408 quineState = none :=
  quine_halts

end LeanFunge.Tests
