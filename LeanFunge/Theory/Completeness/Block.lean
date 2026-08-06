/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanFunge.Theory.Completeness.Linear
import LeanFunge.Theory.Completeness.PairEncoding
import LeanFunge.Theory.Completeness.Routing
import LeanFunge.Theory.StepOps

/-!
# The `decz` Block Snippets

The arithmetic of a `decz` block: running the test cells `: 2 % |` (or
`: 3 % |`) on the encoded pair leaves the value on the stack and branches
down on the even (divisible) case, up on the odd (non-divisible) case, and
running the decrement cells `2 /` (or `3 /`) divides the value. Combined with
the counter-pair encoding, a `decz` on counter 1 decrements it by dividing
the encoding by 2.

## Theorems

* `decz_test_prefix_c1`: Running `: 2 %` leaves the test on top of the value.
* `decz_test_prefix_c2`: Running `: 3 %` leaves the test on top of the value.
* `decz_test_c1_even`: Running `: 2 % |` on an even value branches down.
* `decz_test_c1_odd`: Running `: 2 % |` on an odd value branches up.
* `decz_test_c2_even`: Running `: 3 % |` on a divisible value branches down.
* `decz_test_c2_odd`: Running `: 3 % |` on a non-divisible value branches up.
* `decz_dec_c1`: Running `2 /` divides the value by 2.
* `decz_dec_c2`: Running `3 /` divides the value by 3.
-/

namespace LeanFunge

namespace Completeness

/-- Running `: 2 %` leaves the test `n % 2` on top of the value. -/
theorem decz_test_prefix_c1 (s : State w h) (p : ℕ) (n : Int)
    (hsm : s.stringMode = false) (hdir : s.dir = Direction.right)
    (hpc : s.pc = (p, 0)) (hno : p + 3 < w)
    (hstack : s.stack = [n])
    (hc1 : s.grid.get p 0 = ':') (hc2 : s.grid.get (p + 1) 0 = '2')
    (hc3 : s.grid.get (p + 2) 0 = '%') :
    run 3 s = some { s with stack := [n % 2, n], pc := (p + 3, 0) } := by
  have h1 : run 1 s = some { s with stack := [n, n], pc := (p + 1, 0) } := by
    rw [show run 1 s = step s by rfl]
    unfold step
    have hdec : decodeChar ':' = .dup := by unfold decodeChar; rfl
    simp only [hsm, hc1, hpc, hdec, hstack, stepState, Stack.dup]
    rw [hdir, stepPos_right_no_wrap p w h (by omega)]
  have h2 : run 1 { s with stack := [n, n], pc := (p + 1, 0) } =
      some { s with stack := [2, n, n], pc := (p + 2, 0) } := by
    rw [show run 1 { s with stack := [n, n], pc := (p + 1, 0) } = step { s with stack := [n, n], pc := (p + 1, 0) } by rfl]
    unfold step
    have hdec : decodeChar '2' = .push 2 := by unfold decodeChar; rfl
    simp only [hsm, hc2, hdec, stepState, Stack.push]
    rw [hdir, stepPos_right_no_wrap (p + 1) w h (by omega)]
  have h3 : run 1 { s with stack := [2, n, n], pc := (p + 2, 0) } =
      some { s with stack := [n % 2, n], pc := (p + 3, 0) } := by
    rw [show run 1 { s with stack := [2, n, n], pc := (p + 2, 0) } = step { s with stack := [2, n, n], pc := (p + 2, 0) } by rfl]
    unfold step
    have hdec : decodeChar '%' = .mod := by unfold decodeChar; rfl
    simp only [hsm, hc3, hdec, stepState, Stack.applyBinary]
    rw [hdir, stepPos_right_no_wrap (p + 2) w h (by omega)]
  have h12 : run (1 + 1) s = some { s with stack := [2, n, n], pc := (p + 2, 0) } := by
    exact run_append s { s with stack := [n, n], pc := (p + 1, 0) }
      (some { s with stack := [2, n, n], pc := (p + 2, 0) }) 1 1 h1 h2
  have h123 : run (1 + 1 + 1) s = some { s with stack := [n % 2, n], pc := (p + 3, 0) } := by
    exact run_append s { s with stack := [2, n, n], pc := (p + 2, 0) }
      (some { s with stack := [n % 2, n], pc := (p + 3, 0) }) (1 + 1) 1 h12 h3
  rw [show 3 = 1 + 1 + 1 by omega]
  exact h123

/-- Running `: 3 %` leaves the test `n % 3` on top of the value. -/
theorem decz_test_prefix_c2 (s : State w h) (p : ℕ) (n : Int)
    (hsm : s.stringMode = false) (hdir : s.dir = Direction.right)
    (hpc : s.pc = (p, 0)) (hno : p + 3 < w)
    (hstack : s.stack = [n])
    (hc1 : s.grid.get p 0 = ':') (hc2 : s.grid.get (p + 1) 0 = '3')
    (hc3 : s.grid.get (p + 2) 0 = '%') :
    run 3 s = some { s with stack := [n % 3, n], pc := (p + 3, 0) } := by
  have h1 : run 1 s = some { s with stack := [n, n], pc := (p + 1, 0) } := by
    rw [show run 1 s = step s by rfl]
    unfold step
    have hdec : decodeChar ':' = .dup := by unfold decodeChar; rfl
    simp only [hsm, hc1, hpc, hdec, hstack, stepState, Stack.dup]
    rw [hdir, stepPos_right_no_wrap p w h (by omega)]
  have h2 : run 1 { s with stack := [n, n], pc := (p + 1, 0) } =
      some { s with stack := [3, n, n], pc := (p + 2, 0) } := by
    rw [show run 1 { s with stack := [n, n], pc := (p + 1, 0) } = step { s with stack := [n, n], pc := (p + 1, 0) } by rfl]
    unfold step
    have hdec : decodeChar '3' = .push 3 := by unfold decodeChar; rfl
    simp only [hsm, hc2, hdec, stepState, Stack.push]
    rw [hdir, stepPos_right_no_wrap (p + 1) w h (by omega)]
  have h3 : run 1 { s with stack := [3, n, n], pc := (p + 2, 0) } =
      some { s with stack := [n % 3, n], pc := (p + 3, 0) } := by
    rw [show run 1 { s with stack := [3, n, n], pc := (p + 2, 0) } = step { s with stack := [3, n, n], pc := (p + 2, 0) } by rfl]
    unfold step
    have hdec : decodeChar '%' = .mod := by unfold decodeChar; rfl
    simp only [hsm, hc3, hdec, stepState, Stack.applyBinary]
    rw [hdir, stepPos_right_no_wrap (p + 2) w h (by omega)]
  have h12 : run (1 + 1) s = some { s with stack := [3, n, n], pc := (p + 2, 0) } := by
    exact run_append s { s with stack := [n, n], pc := (p + 1, 0) }
      (some { s with stack := [3, n, n], pc := (p + 2, 0) }) 1 1 h1 h2
  have h123 : run (1 + 1 + 1) s = some { s with stack := [n % 3, n], pc := (p + 3, 0) } := by
    exact run_append s { s with stack := [3, n, n], pc := (p + 2, 0) }
      (some { s with stack := [n % 3, n], pc := (p + 3, 0) }) (1 + 1) 1 h12 h3
  rw [show 3 = 1 + 1 + 1 by omega]
  exact h123

/-- Running `: 2 % |` on an even value leaves it on the stack and branches
    down. -/
theorem decz_test_c1_even (s : State w h) (p : ℕ) (n : Int)
    (hsm : s.stringMode = false) (hdir : s.dir = Direction.right)
    (hpc : s.pc = (p, 0)) (hno : p + 3 < w)
    (hstack : s.stack = [n])
    (hc1 : s.grid.get p 0 = ':') (hc2 : s.grid.get (p + 1) 0 = '2')
    (hc3 : s.grid.get (p + 2) 0 = '%') (hc4 : s.grid.get (p + 3) 0 = '|')
    (hn : n % 2 = 0) :
    run 4 s = some { s with
      dir := Direction.down,
      stack := [n], pc := stepPos w h Direction.down (p + 3, 0) } := by
  have hpre : run 3 s = some { s with stack := [n % 2, n], pc := (p + 3, 0) } :=
    decz_test_prefix_c1 s p n hsm hdir hpc hno hstack hc1 hc2 hc3
  have h4 : run 1 { s with stack := [n % 2, n], pc := (p + 3, 0) } =
      some { s with
        dir := Direction.down,
        stack := [n], pc := stepPos w h Direction.down (p + 3, 0) } := by
    rw [show run 1 { s with stack := [n % 2, n], pc := (p + 3, 0) } = step { s with stack := [n % 2, n], pc := (p + 3, 0) } by rfl]
    unfold step
    have hdec : decodeChar '|' = .chooseV := by unfold decodeChar; rfl
    simp only [hsm, hc4, hdec, stepState, Stack.top, Stack.pop, Stack.drop]
    rw [hn]
    rfl
  have h1234 : run (3 + 1) s =
      some { s with
        dir := Direction.down,
        stack := [n], pc := stepPos w h Direction.down (p + 3, 0) } := by
    exact run_append s { s with stack := [n % 2, n], pc := (p + 3, 0) }
      (some { s with
        dir := Direction.down,
        stack := [n], pc := stepPos w h Direction.down (p + 3, 0) }) 3 1 hpre h4
  rw [show 4 = 3 + 1 by omega]
  exact h1234

/-- Running `: 2 % |` on an odd value leaves it on the stack and branches
    up. -/
theorem decz_test_c1_odd (s : State w h) (p : ℕ) (n : Int)
    (hsm : s.stringMode = false) (hdir : s.dir = Direction.right)
    (hpc : s.pc = (p, 0)) (hno : p + 3 < w)
    (hstack : s.stack = [n])
    (hc1 : s.grid.get p 0 = ':') (hc2 : s.grid.get (p + 1) 0 = '2')
    (hc3 : s.grid.get (p + 2) 0 = '%') (hc4 : s.grid.get (p + 3) 0 = '|')
    (hn : n % 2 ≠ 0) :
    run 4 s = some { s with
      dir := Direction.up,
      stack := [n], pc := stepPos w h Direction.up (p + 3, 0) } := by
  have hpre : run 3 s = some { s with stack := [n % 2, n], pc := (p + 3, 0) } :=
    decz_test_prefix_c1 s p n hsm hdir hpc hno hstack hc1 hc2 hc3
  have h4 : run 1 { s with stack := [n % 2, n], pc := (p + 3, 0) } =
      some { s with
        dir := Direction.up,
        stack := [n], pc := stepPos w h Direction.up (p + 3, 0) } := by
    rw [show run 1 { s with stack := [n % 2, n], pc := (p + 3, 0) } = step { s with stack := [n % 2, n], pc := (p + 3, 0) } by rfl]
    unfold step
    have hdec : decodeChar '|' = .chooseV := by unfold decodeChar; rfl
    simp only [hsm, hc4, hdec, stepState, Stack.top, Stack.pop, Stack.drop]
    rw [show Direction.chooseV (n % 2) = Direction.up by
        simp only [Direction.chooseV, if_neg hn]]
  have h1234 : run (3 + 1) s =
      some { s with
        dir := Direction.up,
        stack := [n], pc := stepPos w h Direction.up (p + 3, 0) } := by
    exact run_append s { s with stack := [n % 2, n], pc := (p + 3, 0) }
      (some { s with
        dir := Direction.up,
        stack := [n], pc := stepPos w h Direction.up (p + 3, 0) }) 3 1 hpre h4
  rw [show 4 = 3 + 1 by omega]
  exact h1234

/-- Running `2 /` divides the value by 2. -/
theorem decz_dec_c1 (s : State w h) (p : ℕ) (n : Int)
    (hsm : s.stringMode = false) (hdir : s.dir = Direction.right)
    (hpc : s.pc = (p, 0)) (hno : p + 2 < w)
    (hstack : s.stack = [n])
    (hc1 : s.grid.get p 0 = '2') (hc2 : s.grid.get (p + 1) 0 = '/') :
    run 2 s = some { s with stack := [n / 2], pc := (p + 2, 0) } := by
  have h1 : run 1 s = some { s with stack := [2, n], pc := (p + 1, 0) } := by
    rw [show run 1 s = step s by rfl]
    unfold step
    have hdec : decodeChar '2' = .push 2 := by unfold decodeChar; rfl
    simp only [hsm, hc1, hpc, hdec, hstack, stepState, Stack.push]
    rw [hdir, stepPos_right_no_wrap p w h (by omega)]
  have h2 : run 1 { s with stack := [2, n], pc := (p + 1, 0) } =
      some { s with stack := [n / 2], pc := (p + 2, 0) } := by
    rw [show run 1 { s with stack := [2, n], pc := (p + 1, 0) } = step { s with stack := [2, n], pc := (p + 1, 0) } by rfl]
    unfold step
    have hdec : decodeChar '/' = .div := by unfold decodeChar; rfl
    simp only [hsm, hc2, hdec, stepState, Stack.applyBinary]
    rw [hdir, stepPos_right_no_wrap (p + 1) w h (by omega)]
  have h12 : run (1 + 1) s = some { s with stack := [n / 2], pc := (p + 2, 0) } := by
    exact run_append s { s with stack := [2, n], pc := (p + 1, 0) }
      (some { s with stack := [n / 2], pc := (p + 2, 0) }) 1 1 h1 h2
  rw [show 2 = 1 + 1 by omega]
  exact h12

end Completeness

end LeanFunge
