/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import Mathlib.Data.Int.Basic
import Mathlib.Data.Nat.Notation
import Mathlib.Tactic.Ring

/-!
# The Counter Pair Encoding

The two counters of a two-counter machine are encoded as a single natural
number `encode c1 c2 = 2^c1 * 3^c2`. Because the prime factors `2` and `3`
are coprime, both counters can be recovered by arithmetic on the encoded
value alone:

* `c1` is nonzero exactly when the value is even, so `decz` on counter 1
  tests `value % 2`.
* `c2` is nonzero exactly when the value is divisible by `3`, so `decz` on
  counter 2 tests `value % 3`.

Incrementing counter 1 is multiplication by `2`, decrementing counter 1 (when
nonzero) is division by `2`, and symmetrically for counter 2 with `3`. This
module proves these identities at both the `ℕ` and `Int` level, since the
Befunge stack holds `Int` values.

## Main definitions

* `encode`: Encode `(c1, c2)` as `2^c1 * 3^c2`.

## Theorems

* `encode_inc_c1`: Incrementing counter 1 multiplies the encoding by 2.
* `encode_inc_c2`: Incrementing counter 2 multiplies the encoding by 3.
* `encode_decz_c1`: Decrementing counter 1 divides the encoding by 2.
* `encode_decz_c2`: Decrementing counter 2 divides the encoding by 3.
* `encode_c1_pos`: Counter 1 is positive exactly when the encoding is even.
* `encode_c1_eq_zero`: Counter 1 is zero exactly when the encoding is odd.
* `encode_c2_pos`: Counter 2 is positive exactly when the encoding is
  divisible by 3.
* `encode_c2_eq_zero`: Counter 2 is zero exactly when the encoding is not
  divisible by 3.
* `pow_two_mod_three_ne_zero`: A power of two is never divisible by three.
* `encode_inc_c1_int`: The `Int` version of `encode_inc_c1`.
* `encode_inc_c2_int`: The `Int` version of `encode_inc_c2`.
* `encode_decz_c1_int`: The `Int` version of `encode_decz_c1`.
* `encode_decz_c2_int`: The `Int` version of `encode_decz_c2`.
* `encode_c1_pos_int`: The `Int` version of `encode_c1_pos`.
* `encode_c2_pos_int`: The `Int` version of `encode_c2_pos`.
-/

namespace LeanFunge

namespace Completeness

/-- Encode the two counters as a single natural: `2^c1 * 3^c2`. -/
def encode (c1 c2 : ℕ) : ℕ :=
  2 ^ c1 * 3 ^ c2

/-- Incrementing counter 1 multiplies the encoding by 2. -/
theorem encode_inc_c1 (c1 c2 : ℕ) : encode (c1 + 1) c2 = 2 * encode c1 c2 := by
  unfold encode
  rw [pow_succ]
  ring

/-- Incrementing counter 2 multiplies the encoding by 3. -/
theorem encode_inc_c2 (c1 c2 : ℕ) : encode c1 (c2 + 1) = 3 * encode c1 c2 := by
  unfold encode
  rw [pow_succ]
  ring

/-- Decrementing counter 1 (when positive) divides the encoding by 2. -/
theorem encode_decz_c1 {c1 c2 : ℕ} (h : 0 < c1) :
    encode (c1 - 1) c2 = encode c1 c2 / 2 := by
  unfold encode
  have hc : (c1 - 1) + 1 = c1 := Nat.sub_add_cancel (Nat.succ_le_of_lt h)
  conv =>
    rhs
    rw [← hc, pow_succ]
  rw [show 2 ^ (c1 - 1) * 2 * 3 ^ c2 = (2 ^ (c1 - 1) * 3 ^ c2) * 2 by ring]
  rw [Nat.mul_div_cancel _ (by norm_num : 0 < 2)]

/-- Decrementing counter 2 (when positive) divides the encoding by 3. -/
theorem encode_decz_c2 {c1 c2 : ℕ} (h : 0 < c2) :
    encode c1 (c2 - 1) = encode c1 c2 / 3 := by
  unfold encode
  have hc : (c2 - 1) + 1 = c2 := Nat.sub_add_cancel (Nat.succ_le_of_lt h)
  conv =>
    rhs
    rw [← hc, pow_succ]
  rw [show 2 ^ c1 * (3 ^ (c2 - 1) * 3) = (2 ^ c1 * 3 ^ (c2 - 1)) * 3 by ring]
  rw [Nat.mul_div_cancel _ (by norm_num : 0 < 3)]

/-- Counter 1 is positive exactly when the encoding is even. -/
theorem encode_c1_pos (c1 c2 : ℕ) : c1 > 0 ↔ encode c1 c2 % 2 = 0 := by
  constructor
  · intro hpos
    unfold encode
    have hc : (c1 - 1) + 1 = c1 := Nat.sub_add_cancel (Nat.succ_le_of_lt hpos)
    conv =>
      lhs
      rw [← hc, pow_succ]
    rw [show 2 ^ (c1 - 1) * 2 * 3 ^ c2 = 2 * (2 ^ (c1 - 1) * 3 ^ c2) by ring]
    rw [Nat.mul_mod]
    norm_num
  · intro hmod
    by_contra hnot
    have hzero : c1 = 0 := Nat.eq_zero_of_not_pos hnot
    subst c1
    unfold encode at hmod
    norm_num at hmod
    rw [Nat.pow_mod] at hmod
    norm_num at hmod

/-- Counter 1 is zero exactly when the encoding is odd. -/
theorem encode_c1_eq_zero (c1 c2 : ℕ) : c1 = 0 ↔ encode c1 c2 % 2 = 1 := by
  constructor
  · intro h
    subst c1
    unfold encode
    norm_num
    rw [Nat.pow_mod]
    norm_num
  · intro h
    by_contra hnot
    have hpos : 0 < c1 := Nat.pos_of_ne_zero hnot
    have hmod : encode c1 c2 % 2 = 0 := (encode_c1_pos c1 c2).mp hpos
    omega

/-- A power of two is never divisible by three. -/
theorem pow_two_mod_three_ne_zero (n : ℕ) : 2 ^ n % 3 ≠ 0 := by
  intro hz
  have hdvd : 3 ∣ 2 ^ n := (Nat.dvd_iff_mod_eq_zero).2 hz
  have hcop : Nat.Coprime 3 (2 ^ n) :=
    Nat.Coprime.symm (Nat.Coprime.pow_left n (by decide : Nat.Coprime 2 3))
  have hdvd1 : 3 ∣ 1 := hcop.dvd_of_dvd_mul_right (by simpa only [one_mul] using hdvd)
  norm_num at hdvd1

/-- Counter 2 is positive exactly when the encoding is divisible by 3. -/
theorem encode_c2_pos (c1 c2 : ℕ) : c2 > 0 ↔ encode c1 c2 % 3 = 0 := by
  constructor
  · intro hpos
    unfold encode
    have hc : (c2 - 1) + 1 = c2 := Nat.sub_add_cancel (Nat.succ_le_of_lt hpos)
    conv =>
      lhs
      rw [← hc, pow_succ]
    rw [show 2 ^ c1 * (3 ^ (c2 - 1) * 3) = 3 * (2 ^ c1 * 3 ^ (c2 - 1)) by ring]
    rw [Nat.mul_mod]
    norm_num
  · intro hmod
    by_contra hnot
    have hzero : c2 = 0 := Nat.eq_zero_of_not_pos hnot
    subst c2
    unfold encode at hmod
    rw [pow_zero, mul_one] at hmod
    exact pow_two_mod_three_ne_zero c1 hmod

/-- Counter 2 is zero exactly when the encoding is not divisible by 3. -/
theorem encode_c2_eq_zero (c1 c2 : ℕ) : c2 = 0 ↔ encode c1 c2 % 3 ≠ 0 := by
  constructor
  · intro h
    subst c2
    unfold encode
    rw [pow_zero, mul_one]
    exact pow_two_mod_three_ne_zero c1
  · intro h
    by_contra hnot
    have hpos : 0 < c2 := Nat.pos_of_ne_zero hnot
    exact h ((encode_c2_pos c1 c2).mp hpos)

/-- The `Int` version of `encode_inc_c1`: multiplying by 2 increments counter
    1. -/
theorem encode_inc_c1_int (c1 c2 : ℕ) :
    (encode c1 c2 : Int) * 2 = (encode (c1 + 1) c2 : Int) := by
  rw (config := { transparency := .default }) [← Int.natCast_mul]
  congr 1
  rw [encode_inc_c1]
  ring

/-- The `Int` version of `encode_inc_c2`: multiplying by 3 increments counter
    2. -/
theorem encode_inc_c2_int (c1 c2 : ℕ) :
    (encode c1 c2 : Int) * 3 = (encode c1 (c2 + 1) : Int) := by
  rw (config := { transparency := .default }) [← Int.natCast_mul]
  congr 1
  rw [encode_inc_c2]
  ring

/-- The `Int` version of `encode_decz_c1`: dividing by 2 decrements counter 1
    (when positive). -/
theorem encode_decz_c1_int (c1 c2 : ℕ) (h : 0 < c1) :
    (encode c1 c2 : Int) / 2 = (encode (c1 - 1) c2 : Int) := by
  rw (config := { transparency := .default }) [← Int.natCast_ediv]
  congr 1
  exact (encode_decz_c1 h).symm

/-- The `Int` version of `encode_decz_c2`: dividing by 3 decrements counter 2
    (when positive). -/
theorem encode_decz_c2_int (c1 c2 : ℕ) (h : 0 < c2) :
    (encode c1 c2 : Int) / 3 = (encode c1 (c2 - 1) : Int) := by
  rw (config := { transparency := .default }) [← Int.natCast_ediv]
  congr 1
  exact (encode_decz_c2 h).symm

/-- The `Int` version of `encode_c1_pos`: the stack-top test for counter 1. -/
theorem encode_c1_pos_int (c1 c2 : ℕ) :
    (encode c1 c2 : Int) % 2 = 0 ↔ c1 > 0 := by
  rw (config := { transparency := .default }) [← Int.natCast_emod, Int.ofNat_eq_zero]
  exact (encode_c1_pos c1 c2).symm

/-- The `Int` version of `encode_c2_pos`: the stack-top test for counter 2. -/
theorem encode_c2_pos_int (c1 c2 : ℕ) :
    (encode c1 c2 : Int) % 3 = 0 ↔ c2 > 0 := by
  rw (config := { transparency := .default }) [← Int.natCast_emod, Int.ofNat_eq_zero]
  exact (encode_c2_pos c1 c2).symm

end Completeness

end LeanFunge
