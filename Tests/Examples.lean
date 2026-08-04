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

end LeanFunge.Tests
