/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanFunge.Theory.Completeness.PairEncoding

/-!
# Counter Pair Encoding Tests
-/

namespace LeanFunge.Tests

open LeanFunge.Completeness

example (c1 c2 : ℕ) : encode (c1 + 1) c2 = 2 * encode c1 c2 :=
  encode_inc_c1 c1 c2

example (c1 c2 : ℕ) : encode c1 (c2 + 1) = 3 * encode c1 c2 :=
  encode_inc_c2 c1 c2

example (c1 c2 : ℕ) (h : 0 < c1) : encode (c1 - 1) c2 = encode c1 c2 / 2 :=
  encode_decz_c1 h

example (c1 c2 : ℕ) (h : 0 < c2) : encode c1 (c2 - 1) = encode c1 c2 / 3 :=
  encode_decz_c2 h

example (c1 c2 : ℕ) : c1 = 0 ↔ encode c1 c2 % 2 = 1 :=
  encode_c1_eq_zero c1 c2

example (c1 c2 : ℕ) : c1 > 0 ↔ encode c1 c2 % 2 = 0 :=
  encode_c1_pos c1 c2

example (c1 c2 : ℕ) : c2 = 0 ↔ encode c1 c2 % 3 ≠ 0 :=
  encode_c2_eq_zero c1 c2

example (c1 c2 : ℕ) : c2 > 0 ↔ encode c1 c2 % 3 = 0 :=
  encode_c2_pos c1 c2

example (n : ℕ) : 2 ^ n % 3 ≠ 0 :=
  pow_two_mod_three_ne_zero n

example (c1 c2 : ℕ) : (encode c1 c2 : Int) * 2 = (encode (c1 + 1) c2 : Int) :=
  encode_inc_c1_int c1 c2

example (c1 c2 : ℕ) : (encode c1 c2 : Int) * 3 = (encode c1 (c2 + 1) : Int) :=
  encode_inc_c2_int c1 c2

example (c1 c2 : ℕ) (h : 0 < c1) :
    (encode c1 c2 : Int) / 2 = (encode (c1 - 1) c2 : Int) :=
  encode_decz_c1_int c1 c2 h

example (c1 c2 : ℕ) (h : 0 < c2) :
    (encode c1 c2 : Int) / 3 = (encode c1 (c2 - 1) : Int) :=
  encode_decz_c2_int c1 c2 h

example (c1 c2 : ℕ) : (encode c1 c2 : Int) % 2 = 0 ↔ c1 > 0 :=
  encode_c1_pos_int c1 c2

example (c1 c2 : ℕ) : (encode c1 c2 : Int) % 3 = 0 ↔ c2 > 0 :=
  encode_c2_pos_int c1 c2

end LeanFunge.Tests
