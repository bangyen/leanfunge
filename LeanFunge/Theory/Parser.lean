/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanFunge.Core.Parser
import Batteries.Data.Char.Basic
import Batteries.Data.Char.AsciiCasing
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

/-- The digit character at value `d` decodes back to `d`. -/
theorem digitValue_ofNat (d : Nat) (hd : d < 10) :
    digitValue (Char.ofNat (d + 48)) = d := by
  unfold digitValue
  have hvalid : (d + 48).isValidChar := by omega
  rw [Char.toNat_ofNat]
  simp [hvalid]
  omega

/-- Every decimal digit of a natural number is a single digit. -/
theorem natDigits_digit_lt (n : Nat) : ∀ d ∈ natDigits n, d < 10 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      by_cases hn : n < 10
      · unfold natDigits
        rw [if_pos hn]
        intro d hd
        rw [List.mem_singleton] at hd
        subst d
        exact hn
      · have hdiv : n / 10 < n := by omega
        unfold natDigits
        rw [if_neg hn]
        intro d hd
        rw [List.mem_append] at hd
        rcases hd with hd | hd
        · exact ih (n / 10) hdiv d hd
        · rw [List.mem_singleton] at hd
          subst d
          exact Nat.mod_lt n (by decide)

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

/-- Reconstructing the digit characters of a natural number via `digitsValue`
    returns the original number. -/
theorem digitsValue_natDigits (n : Nat) :
    digitsValue (natDigits n |>.map (fun d => Char.ofNat (d + 48))) = n := by
  unfold digitsValue
  rw [List.foldl_map]
  trans natDigitsValue (natDigits n)
  · have hstep : ∀ (ds : List Nat) (a : Nat), (∀ d ∈ ds, d < 10) →
        List.foldl (fun acc d => acc * 10 + digitValue (Char.ofNat (d + 48))) a ds =
          List.foldl (fun acc d => acc * 10 + d) a ds := by
      intro ds
      induction ds with
      | nil => intro a h; rfl
      | cons d ds ih =>
          intro a h
          have hds : ∀ d ∈ ds, d < 10 := by
            intro d' hd'
            exact h d' (by simp [hd'])
          change List.foldl (fun acc d => acc * 10 + digitValue (Char.ofNat (d + 48)))
              (a * 10 + digitValue (Char.ofNat (d + 48))) ds =
            List.foldl (fun acc d => acc * 10 + d) (a * 10 + d) ds
          rw [digitValue_ofNat d (h d (by simp))]
          rw [ih (a * 10 + d) hds]
    exact hstep (natDigits n) 0 (natDigits_digit_lt n)
  · unfold natDigitsValue
    exact natDigitsValue_natDigits n

end LeanFunge
