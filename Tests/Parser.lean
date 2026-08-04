/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanFunge.Core.Parser
import LeanFunge.Theory.Parser

/-!
# Parser Tests
-/

namespace LeanFunge.Tests

open LeanFunge

example : parseInt [] = ([], 0) :=
  parseInt_empty

example : parseInt (String.toList "5") = ([], 5) := by
  decide

example : parseInt (String.toList "-7") = ([], -7) := by
  decide

example : parseInt (String.toList "42") = ([], 42) := by
  decide

example : parseInt (String.toList " 5") = ([], 5) := by
  decide

example : parseInt (String.toList "5x") = (String.toList "x", 5) := by
  decide

example (n : Nat) : natDigitsValue (natDigits n) = n :=
  natDigitsValue_natDigits n

end LeanFunge.Tests
