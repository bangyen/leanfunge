/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import Mathlib.Data.Nat.Notation

/-!
# Integer Input Parsing

## Main definitions

* `digitValue`: The decimal value of a digit character.
* `takeDigits`: Split the leading decimal digits from an input stream.
* `digitsValue`: The value of a list of digit characters.
* `skipSpaces`: Drop leading spaces.
* `parseInt`: Parse a (possibly negative) decimal integer from an input stream.
* `natDigits`: The decimal digits of a natural number.
* `natDigitsValue`: The value of a list of decimal digits.
-/

namespace LeanFunge

/-- The decimal value of a digit character (`0` for non-digits). -/
def digitValue (c : Char) : Nat :=
  if 48 ≤ c.toNat ∧ c.toNat ≤ 57 then c.toNat - 48 else 0

/-- Split the leading decimal digits from an input stream, returning the
    digits taken and the remaining stream. -/
def takeDigits (input : List Char) : List Char × List Char :=
  match input with
  | [] => ([], [])
  | c :: rest =>
      if 48 ≤ c.toNat ∧ c.toNat ≤ 57 then
        let (ds, rest') := takeDigits rest
        (c :: ds, rest')
      else
        ([], input)

/-- The value of a list of digit characters (most significant first). -/
def digitsValue : List Char → Nat :=
  List.foldl (fun acc c => acc * 10 + digitValue c) 0

/-- Drop leading spaces. -/
def skipSpaces : List Char → List Char :=
  fun input =>
    match input with
    | [] => []
    | c :: rest => if c = ' ' then skipSpaces rest else input

/-- Parse a (possibly negative) decimal integer from the front of an input
    stream, returning the remaining stream and the value. Leading spaces are
    skipped, and an empty digit run yields `0` without consuming input. -/
def parseInt (input : List Char) : List Char × Int :=
  let input' := skipSpaces input
  match input' with
  | '-' :: rest =>
      let (ds, rest') := takeDigits rest
      if ds = [] then (input', 0) else (rest', -Int.ofNat (digitsValue ds))
  | _ =>
      let (ds, rest') := takeDigits input'
      (rest', Int.ofNat (digitsValue ds))

/-- The decimal digits of a natural number, most significant first. -/
def natDigits (n : Nat) : List Nat :=
  if n < 10 then [n] else natDigits (n / 10) ++ [n % 10]
termination_by n
decreasing_by
  omega

/-- The value of a list of decimal digits (most significant first). -/
def natDigitsValue (ds : List Nat) : Nat :=
  ds.foldl (fun acc d => acc * 10 + d) 0

end LeanFunge
