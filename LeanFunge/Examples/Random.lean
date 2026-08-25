/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanFunge.Theory.Random
import LeanFunge.Theory.Run.Relational

/-!
# The Coin Flip

Every other verified example is deterministic: `run` fixes `?` to "keep the
current direction", so the interpreter alone never exhibits the branching.
This program is verified against the *relational* semantics instead, where a
`?` may choose any of the four directions.

The 3×3 playfield

```
?@@
@
@
```

puts a `?` at the origin and an `@` at each of its four toroidal neighbours:
right is `(1, 0)`, down is `(0, 1)`, left wraps to `(2, 0)`, and up wraps to
`(0, 2)`. Whichever direction the `?` picks, the pointer lands on a halt cell,
so the program halts in two steps along every branch.

## Main definitions

* `coinRow₀`, `coinRow₁`, `coinGrid`, `coinState`: The program, its playfield,
  and its initial state.

## Theorems

* `coin_step_any`: The `?` may step to any direction, and the resulting
  pointer sits on a `@`.
* `coin_halts_any`: For every direction the `?` may choose, the relational run
  halts after two steps.
* `coin_halts_nondeterministic`: The two-step relational run halts, and the
  four choices are genuinely distinct intermediate states.
* `coin_deterministic_halts`: The deterministic interpreter also halts in two
  steps, taking the "keep going right" branch.
-/

namespace LeanFunge.Examples

/-- The first row `?@@`: the `?` at the origin, with the right neighbour and
    the left wrap-around neighbour both halting. -/
def coinRow₀ : List Char := String.toList "?@@"

/-- The second and third rows, each holding a wrap-around `@`. -/
def coinRow₁ : List Char := String.toList "@  "

/-- The 3×3 coin-flip playfield. -/
def coinGrid : Grid 3 3 := Grid.ofRows 3 3 [coinRow₀, coinRow₁, coinRow₁]

/-- The initial state of the coin-flip program. -/
def coinState : State 3 3 := State.init coinGrid

/-- The state reached after the `?` chooses direction `d`. -/
def coinAfter (d : Direction) : State 3 3 :=
  { coinState with dir := d, pc := stepPos 3 3 d coinState.pc }

/-- The `?` may step to any direction, and every resulting pointer sits on a
    `@`. -/
theorem coin_step_any (d : Direction) :
    stepRel coinState (some (coinAfter d)) ∧
      decodeChar ((coinAfter d).grid.get (coinAfter d).pc.1 (coinAfter d).pc.2)
        = .halt := by
  refine ⟨stepRel_random_choice coinState rfl (by decide) d, ?_⟩
  cases d <;> decide

/-- For every direction the `?` may choose, the relational run halts after two
    steps. -/
theorem coin_halts_any (d : Direction) : runRel 2 coinState none := by
  refine runRel_append coinState (coinAfter d) none 1 1 ?_ ?_
  · exact (runRel_one _ _).2 (stepRel_random_choice coinState rfl (by decide) d)
  · refine (runRel_one _ _).2 (step_none_refines_stepRel _ ?_)
    cases d <;> decide

/-- The nondeterminism is genuine: the branches taken by `?` are pairwise
    distinct states, yet each of them halts. -/
theorem coin_halts_nondeterministic :
    (coinAfter .up).pc ≠ (coinAfter .down).pc ∧
      (coinAfter .left).pc ≠ (coinAfter .right).pc ∧
      runRel 2 coinState none :=
  ⟨by decide, by decide, coin_halts_any .right⟩

/-- The deterministic interpreter halts in two steps as well, taking the
    "keep the current direction" branch. -/
theorem coin_deterministic_halts : run 2 coinState = none := by
  decide

end LeanFunge.Examples
