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
* `skipSpaces_suffix`: `skipSpaces` returns a suffix of the input stream.
* `takeDigits_suffix`: `takeDigits` returns the leading digits and the rest,
  a suffix of the input.
* `parseInt_skip_nil`: Parsing an all-space input consumes everything and
  yields the value zero.
* `parseInt_skip_digits`: Parsing a non-negative input consumes the leading
  digits after skipping spaces.
* `parseInt_skip_minus_zero`: A minus sign with no following digits leaves
  the stream unchanged.
* `parseInt_skip_minus`: A minus sign with digits consumes the sign and the
  leading digits.
* `parseInt_suffix`: Parsing consumes only a prefix of the input, leaving a
  suffix.
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

/-- `skipSpaces` returns a suffix of the input stream. -/
theorem skipSpaces_suffix (input : List Char) :
    ∃ pre : List Char, input = pre ++ skipSpaces input := by
  induction input with
  | nil => exact ⟨[], rfl⟩
  | cons c rest ih =>
      by_cases hc : c = ' '
      · rw [hc]
        rcases ih with ⟨pre, hpre⟩
        refine ⟨c :: pre, ?_⟩
        simp only [↓Char.isValue, hc, skipSpaces, ↓reduceIte, List.cons_append, List.cons.injEq,
          true_and]
        rw [← hpre]
      · refine ⟨[], ?_⟩
        simp [skipSpaces, hc] -- no_squeeze: space prefix

/-- `takeDigits` returns the leading digits and the rest, which is a suffix of
    the input. -/
theorem takeDigits_suffix (input : List Char) :
    input = (takeDigits input).1 ++ (takeDigits input).2 := by
  induction input with
  | nil => rfl
  | cons c rest ih =>
      by_cases hc : 48 ≤ c.toNat ∧ c.toNat ≤ 57
      · unfold takeDigits
        rw [if_pos hc]
        rcases htake : takeDigits rest with ⟨ds, rest'⟩
        have hih : rest = ds ++ rest' := by simpa [htake] using ih -- no_squeeze: digit prefix
        simp [hih] -- no_squeeze: digit prefix
      · unfold takeDigits
        rw [if_neg hc]
        rfl

/-- Parsing an all-space input consumes everything and yields `0`. -/
theorem parseInt_skip_nil (input : List Char) (hsp : skipSpaces input = []) :
    parseInt input = ([], 0) := by
  unfold parseInt
  rw [hsp]
  rfl

/-- Parsing a non-negative input leaves the digit-run remainder: the parse
    consumes the leading digits of the stream after skipping spaces. -/
theorem parseInt_skip_digits (input : List Char) (c : Char) (rest : List Char)
    (hsp : skipSpaces input = c :: rest) (hc : c ≠ '-') :
    parseInt input =
      ((takeDigits (c :: rest)).2, Int.ofNat (digitsValue (takeDigits (c :: rest)).1)) := by
  unfold parseInt
  rw [hsp]
  simp [hc] -- no_squeeze: non-negative parse

/-- Parsing a minus sign with no following digits consumes nothing after the
    sign. -/
theorem parseInt_skip_minus_zero (input : List Char) (rest ds rest' : List Char)
    (hsp : skipSpaces input = '-' :: rest) (htake : takeDigits rest = (ds, rest'))
    (hds : ds = []) :
    parseInt input = ('-' :: rest, 0) := by
  unfold parseInt
  rw [hsp]
  simp [htake, hds] -- no_squeeze: no digits

/-- Parsing a minus sign with digits leaves the remainder after the digits:
    the parse consumes the sign and the leading digits. -/
theorem parseInt_skip_minus (input : List Char) (rest ds rest' : List Char)
    (hsp : skipSpaces input = '-' :: rest) (htake : takeDigits rest = (ds, rest'))
    (hds : ds ≠ []) :
    parseInt input = (rest', -Int.ofNat (digitsValue ds)) := by
  unfold parseInt
  rw [hsp]
  simp [htake, hds] -- no_squeeze: minus digits

/-- Parsing consumes only a prefix of the input: the remaining stream is a
    suffix of the original. -/
theorem parseInt_suffix (input : List Char) :
    ∃ pre : List Char, input = pre ++ (parseInt input).1 := by
  cases hsp : skipSpaces input with
  | nil =>
      exact ⟨input, by simp [parseInt_skip_nil input hsp] -- no_squeeze: empty input
        ⟩
  | cons c rest =>
      by_cases hneg : c = '-'
      · rw [hneg] at hsp
        rcases htake : takeDigits rest with ⟨ds, rest'⟩
        by_cases hds : ds = []
        · rcases skipSpaces_suffix input with ⟨pre, hpre⟩
          refine ⟨pre, ?_⟩
          conv => lhs; rw [hpre]
          rw [parseInt_skip_minus_zero input rest ds rest' hsp htake hds]
          simp [hsp] -- no_squeeze: minus no digits
        · rcases skipSpaces_suffix input with ⟨pre, hpre⟩
          have hre : rest = ds ++ rest' := by
            simpa [htake] using takeDigits_suffix rest -- no_squeeze: digit remainder
          refine ⟨pre ++ ('-' :: ds), ?_⟩
          conv => lhs; rw [hpre]
          rw [parseInt_skip_minus input rest ds rest' hsp htake hds]
          rw [hsp, hre]
          simp [List.append_assoc] -- no_squeeze: minus digits
      · rcases skipSpaces_suffix input with ⟨pre, hpre⟩
        refine ⟨pre ++ (takeDigits (c :: rest)).1, ?_⟩
        conv => lhs; rw [hpre]
        rw [parseInt_skip_digits input c rest hsp hneg]
        rw [hsp]
        conv => lhs; rw [takeDigits_suffix (c :: rest)]
        simp only [List.append_assoc]

end LeanFunge
