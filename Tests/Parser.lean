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

example (n : Nat) : ∀ d ∈ natDigits n, d < 10 :=
  natDigits_digit_lt n

example (n : Nat) :
    digitsValue (natDigits n |>.map (fun d => Char.ofNat (d + 48))) = n :=
  digitsValue_natDigits n

example (d : Nat) (hd : d < 10) : digitValue (Char.ofNat (d + 48)) = d :=
  digitValue_ofNat d hd

end LeanFunge.Tests
