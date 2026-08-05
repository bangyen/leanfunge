/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import Batteries.Data.Char.AsciiCasing
import Batteries.Data.Char.Basic
import LeanFunge.Core.Parser
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Init

/-!
# Integer Input Parsing

## Definitions

* `isDigitChar`: A character is a decimal digit.

## Theorems

* `parseInt_empty`: Parsing the empty stream yields `0` and consumes nothing.
* `digitValue_ofNat`: The digit character at value `d` decodes back to `d`.
* `natDigits_digit_lt`: Every decimal digit of a natural number is a single digit.
* `natDigitsValue_natDigits`: Interpreting the decimal digits of a natural
  number reconstructs the number.
* `digitsValue_natDigits`: Reconstructing the digit characters of a natural
  number returns the original number.
* `takeDigits_all_digits`: `takeDigits` consumes the whole stream when every
  character is a digit.
* `skipSpaces_no_space`: `skipSpaces` leaves a stream without spaces unchanged.
* `parseInt_natDigits`: Parsing the digit characters of a natural number
  consumes everything and reconstructs the number.
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
  simp only [hvalid, ↓reduceIte, Nat.le_add_left, Nat.reduceLeDiff, true_and, Nat.add_sub_cancel,
    ite_eq_left_iff, Nat.not_le]
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
            exact h d' (by simp only [List.mem_cons, hd', or_true])
          change List.foldl (fun acc d => acc * 10 + digitValue (Char.ofNat (d + 48)))
              (a * 10 + digitValue (Char.ofNat (d + 48))) ds =
            List.foldl (fun acc d => acc * 10 + d) (a * 10 + d) ds
          rw [digitValue_ofNat d (h d (by simp only [List.mem_cons, true_or]))]
          rw [ih (a * 10 + d) hds]
    exact hstep (natDigits n) 0 (natDigits_digit_lt n)
  · unfold natDigitsValue
    exact natDigitsValue_natDigits n

/-- A character is a decimal digit. -/
def isDigitChar (c : Char) : Prop :=
  48 ≤ c.toNat ∧ c.toNat ≤ 57

/-- `takeDigits` consumes the whole stream when every character is a digit. -/
theorem takeDigits_all_digits (ds : List Char) :
    (∀ c ∈ ds, isDigitChar c) → takeDigits ds = (ds, []) := by
  induction ds with
  | nil => intro h; rfl
  | cons c cs ih =>
      intro h
      have hc : 48 ≤ c.toNat ∧ c.toNat ≤ 57 := h c (by simp only [List.mem_cons, true_or])
      have hcs : ∀ c ∈ cs, isDigitChar c := by
        intro c' hc'
        exact h c' (by simp only [List.mem_cons, hc', or_true])
      unfold takeDigits
      rw [if_pos hc]
      rw [ih hcs]

/-- `skipSpaces` leaves a stream without spaces unchanged. -/
theorem skipSpaces_no_space (ds : List Char) :
    (∀ c ∈ ds, c ≠ ' ') → skipSpaces ds = ds := by
  induction ds with
  | nil => intro h; rfl
  | cons c cs ih =>
      intro h
      have hc : c ≠ ' ' := h c (by simp only [List.mem_cons, true_or])
      unfold skipSpaces
      rw [if_neg hc]

/-- Parsing the digit characters of a natural number consumes everything and
    reconstructs the number. -/
theorem parseInt_natDigits (n : Nat) :
    parseInt (natDigits n |>.map digitChar) = ([], (n : Int)) := by
  have hdigits : ∀ c ∈ natDigits n |>.map digitChar, isDigitChar c := by
    intro c hc
    rw [List.mem_map] at hc
    rcases hc with ⟨d, hd, rfl⟩
    unfold digitChar
    have hlt := natDigits_digit_lt n d hd
    unfold isDigitChar
    have hvalid : (d + 48).isValidChar := by omega
    rw [Char.toNat_ofNat]
    simp only [hvalid, ↓reduceIte, Nat.le_add_left, Nat.reduceLeDiff, true_and, ge_iff_le]
    omega
  have hnoSpace : ∀ c ∈ natDigits n |>.map digitChar, c ≠ ' ' := by
    intro c hc hspace
    have hb := hdigits c hc
    rw [hspace] at hb
    unfold isDigitChar at hb
    have hb' : ' '.toNat = 32 := by decide
    rw [hb'] at hb
    omega
  unfold parseInt
  rw [skipSpaces_no_space _ hnoSpace]
  have htake : takeDigits (natDigits n |>.map digitChar) =
      (natDigits n |>.map digitChar, []) :=
    takeDigits_all_digits _ hdigits
  have hne : natDigits n ≠ [] := by
    intro h
    by_cases hn : n < 10
    · unfold natDigits at h
      rw [if_pos hn] at h
      exact (by simp only [ne_eq, List.cons_ne_self, not_false_eq_true] : [n] ≠ []) h
    · unfold natDigits at h
      rw [if_neg hn] at h
      exact (by
        simp only [List.append_eq_nil_iff, List.cons_ne_self, and_false, not_false_eq_true] :
          ¬ natDigits (n / 10) ++ [n % 10] = []) h
  have hmap_ne : (natDigits n).map digitChar ≠ [] := by
    intro h
    have hlen : ((natDigits n).map digitChar).length = (natDigits n).length := by
      rw [List.length_map]
    rw [h] at hlen
    simp only [List.length_nil] at hlen
    apply hne
    apply List.eq_nil_of_length_eq_zero
    omega
  dsimp only [Int.ofNat_eq_natCast, Lean.Elab.WF.paramLet]
  cases hc : natDigits n |>.map digitChar with
  | nil => exact False.elim (hmap_ne hc)
  | cons c cs =>
      have hc' : c ≠ '-' := by
        intro hneg
        have hb := hdigits c (by simp only [hc, List.mem_cons, true_or])
        rw [hneg] at hb
        unfold isDigitChar at hb
        have hb' : '-'.toNat = 45 := by decide
        rw [hb'] at hb
        omega
      simp only [↓Char.isValue, List.cons.injEq, hc', false_and, imp_self, implies_true,
        Prod.mk.injEq]
      rw [← hc, htake]
      simp only [true_and]
      simpa only using congrArg (fun v : Nat => (v : Int)) (digitsValue_natDigits n)

end LeanFunge
