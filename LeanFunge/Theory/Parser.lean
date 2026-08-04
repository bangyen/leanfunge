/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanFunge.Core.Parser
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Init

/-!
# Integer Input Parsing

## Theorems

* `parseInt_empty`: Parsing the empty stream yields `0` and consumes nothing.
* `natDigitsValue_natDigits`: Interpreting the decimal digits of a natural
  number reconstructs the number.
-/

namespace LeanFunge

/-- Parsing the empty stream yields `0` and consumes nothing. -/
theorem parseInt_empty : parseInt [] = ([], 0) :=
  rfl

/-- Interpreting the decimal digits of a natural number reconstructs the
    number. -/
theorem natDigitsValue_natDigits (n : Nat) : natDigitsValue (natDigits n) = n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      by_cases hn : n < 10
      · unfold natDigits
        rw [if_pos hn]
        simp only [natDigitsValue, List.foldl_cons, List.foldl_nil, Nat.zero_mul, Nat.zero_add]
      · have hdiv : n / 10 < n := by omega
        have hmain : natDigitsValue (natDigits (n / 10) ++ [n % 10]) = n := by
          change List.foldl (fun acc d => acc * 10 + d) 0 (natDigits (n / 10) ++ [n % 10]) = n
          rw [List.foldl_append]
          have hih : List.foldl (fun acc d => acc * 10 + d) 0 (natDigits (n / 10)) = n / 10 := by
            simpa only [natDigitsValue] using (ih (n / 10) hdiv)
          rw [hih]
          change (n / 10) * 10 + (n % 10) = n
          omega
        unfold natDigits
        rw [if_neg hn]
        exact hmain

end LeanFunge
