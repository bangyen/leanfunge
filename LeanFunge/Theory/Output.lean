/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanFunge.Theory.Parser
import Mathlib.Tactic.IntervalCases

/-!
# Integer Output Round-trip

The `.` instruction prints an integer through the redefinable `formatInt`
encoding (`Core/Parser`), the dual of the `&` parser. This module proves that
re-parsing any `formatInt` output with `&` (`parseInt`) recovers the original
integer, closing the gap left by the non-reducible `toString` encoding.

## Theorems

* `natDigits_ne_empty`: The decimal digits of a natural number are non-empty.
* `Nat_digitChar_lt10`: Core's digit character for a single digit.
* `toDigitsCore_10_sufficient`: Core's decimal encoding extracts every digit
  when given enough fuel.
* `toDigits_natDigits`: Core's decimal encoding of a natural number is its
  digit characters.
* `parseInt_formatNat`: Parsing core's decimal encoding of a natural number
  consumes everything and reconstructs the number.
* `parseInt_neg_of_digits`: Parsing a minus sign followed by an all-digit
  stream reconstructs the negated value.
* `parseInt_neg_natDigits`: Parsing a minus sign followed by the digits of a
  natural number consumes everything and reconstructs the negative number.
* `parseInt_formatInt`: The `.` output encoding round-trips with `&`: parsing
  the encoded integer consumes everything and reconstructs it.
-/

namespace LeanFunge

/-- The decimal digits of a natural number are non-empty. -/
theorem natDigits_ne_empty (n : Nat) : natDigits n ≠ [] := by
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

/-- Core's digit character for a single digit is the same as `digitChar`. -/
theorem Nat_digitChar_lt10 (d : Nat) (hd : d < 10) :
    Nat.digitChar d = digitChar d := by
  interval_cases d <;> decide

/-- Core's decimal encoding of a natural number produces the digits of
    `natDigits`. -/
theorem toDigitsCore_10_sufficient :
    ∀ (n fuel : ℕ) (acc : List Char), n + 1 ≤ fuel →
      Nat.toDigitsCore 10 fuel n acc = (natDigits n |>.map digitChar) ++ acc := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro fuel acc hfuel
      rcases fuel with _ | fuel'
      · exfalso
        omega
      · by_cases hz : n / 10 = 0
        · have hnlt : n < 10 := by
            have hmod : n = n % 10 := by
              rw [← Nat.div_add_mod n 10]
              rw [hz]
              omega
            rw [hmod]
            exact Nat.mod_lt n (by decide)
          have hmod : n % 10 = n := Nat.mod_eq_of_lt hnlt
          have hdigit : Nat.digitChar n = digitChar n := Nat_digitChar_lt10 n hnlt
          simp only [Nat.toDigitsCore, hz, hmod, hdigit]
          unfold natDigits
          rw [if_pos hnlt]
          rfl
        · have hdiv : n / 10 < n := by
            have hnpos : 0 < n := by
              by_contra hnn
              have hn : n = 0 := Nat.eq_zero_of_not_pos hnn
              rw [hn] at hz
              exact hz (by decide : 0 / 10 = 0)
            exact Nat.div_lt_self hnpos (by decide)
          have hfuel' : n / 10 + 1 ≤ fuel' := by
            have hdivle : n / 10 + 1 ≤ n := Nat.succ_le_of_lt hdiv
            omega
          simp only [Nat.toDigitsCore, hz]
          rw [ih (n / 10) hdiv fuel' (Nat.digitChar (n % 10) :: acc) hfuel']
          have hnat : natDigits n = natDigits (n / 10) ++ [n % 10] := by
            have hnge : ¬ n < 10 := by
              intro hlt
              have : n / 10 = 0 := Nat.div_eq_of_lt hlt
              omega
            conv =>
              lhs
              unfold natDigits
              rw [if_neg hnge]
          have hdig : Nat.digitChar (n % 10) = digitChar (n % 10) :=
            Nat_digitChar_lt10 (n % 10) (Nat.mod_lt n (by decide))
          rw [hdig, hnat]
          rw [List.map_append, List.append_assoc]
          rfl

/-- Core's decimal encoding of a natural number is the digits of `natDigits`. -/
theorem toDigits_natDigits (n : Nat) :
    Nat.toDigits 10 n = (natDigits n |>.map digitChar) := by
  unfold Nat.toDigits
  simpa only [List.append_nil] using
    toDigitsCore_10_sufficient (n := n) (fuel := n + 1) [] (by omega)

/-- Parsing core's decimal encoding of a natural number consumes everything and
    reconstructs the number. -/
theorem parseInt_formatNat (n : Nat) : parseInt (Nat.toDigits 10 n) = ([], (n : Int)) := by
  rw [toDigits_natDigits n]
  exact parseInt_natDigits n

/-- Parsing a minus sign followed by an all-digit stream reconstructs the
    negated value. -/
theorem parseInt_neg_of_digits (ds : List Char) (hdigits : ∀ c ∈ ds, isDigitChar c)
    (hne : ds ≠ []) : parseInt ('-' :: ds) = ([], -Int.ofNat (digitsValue ds)) := by
  have hnoSpace' : ∀ c ∈ ('-' :: ds), c ≠ ' ' := by
    intro c hc
    rw [List.mem_cons] at hc
    rcases hc with hc | hc
    · rw [hc]
      decide
    · intro hspace
      have hb := hdigits c hc
      rw [hspace] at hb
      unfold isDigitChar at hb
      have hb' : ' '.toNat = 32 := by decide
      rw [hb'] at hb
      omega
  unfold parseInt
  simp only [skipSpaces_no_space _ hnoSpace', takeDigits_all_digits _ hdigits, hne]
  rfl

/-- Parsing a minus sign followed by the digit characters of a natural number
    consumes everything and reconstructs the negative number. -/
theorem parseInt_neg_natDigits (m : Nat) :
    parseInt ('-' :: (natDigits m |>.map digitChar)) = ([], -(m : Int)) := by
  have hdigits : ∀ c ∈ natDigits m |>.map digitChar, isDigitChar c := by
    intro c hc
    rw [List.mem_map] at hc
    rcases hc with ⟨d, hd, rfl⟩
    have hlt := natDigits_digit_lt m d hd
    unfold digitChar isDigitChar
    have hvalid : (d + 48).isValidChar := by omega
    rw [Char.toNat_ofNat]
    simp only [hvalid, ↓reduceIte, Nat.le_add_left, Nat.reduceLeDiff, true_and, ge_iff_le]
    omega
  have hmap_ne : (natDigits m).map digitChar ≠ [] := by
    intro h
    have hlen : ((natDigits m).map digitChar).length = (natDigits m).length := by
      rw [List.length_map]
    rw [h] at hlen
    simp only [List.length_nil] at hlen
    apply natDigits_ne_empty m
    apply List.eq_nil_of_length_eq_zero
    omega
  rw [parseInt_neg_of_digits _ hdigits hmap_ne]
  change
    ([], -Int.ofNat (digitsValue (natDigits m |>.map (fun d => Char.ofNat (d + 48))))) = ([], -↑m)
  rw [digitsValue_natDigits m]
  rfl

/-- The `.` output encoding round-trips with `&`: parsing `formatInt n`
    consumes everything and reconstructs `n`. -/
theorem parseInt_formatInt (n : Int) : parseInt (formatInt n) = ([], n) := by
  cases n with
  | ofNat m =>
      change parseInt (Nat.toDigits 10 m) = ([], Int.ofNat m)
      exact parseInt_formatNat m
  | negSucc k =>
      change parseInt ('-' :: Nat.toDigits 10 (k + 1)) = ([], Int.negSucc k)
      rw [toDigits_natDigits (k + 1)]
      rw [parseInt_neg_natDigits (k + 1)]
      rfl

end LeanFunge
