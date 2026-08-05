/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanFunge.Theory.Output

/-!
# Output Round-trip Tests
-/

namespace LeanFunge.Tests

open LeanFunge

example (n : Nat) :
    Nat.toDigits 10 n = (natDigits n |>.map digitChar) :=
  toDigits_natDigits n

example (n : Nat) : parseInt (Nat.toDigits 10 n) = ([], (n : Int)) :=
  parseInt_formatNat n

example (n : Int) : parseInt (formatInt n) = ([], n) :=
  parseInt_formatInt n

example : formatInt 0 = ['0'] := by
  decide

example : formatInt 5 = ['5'] := by
  decide

example : formatInt (-3) = ['-', '3'] := by
  decide

end LeanFunge.Tests
