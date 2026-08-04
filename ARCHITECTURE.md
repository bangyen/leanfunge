# LeanFunge Architecture

This document provides a technical overview of the `LeanFunge` project's design
patterns and core abstractions. It is intended for developers who wish to
contribute to the formal verification of the Befunge esolang.

## Core Abstractions

### Directions (`LeanFunge.Core.Direction`)

`Direction` is an inductive type with four constructors (`up`, `down`, `left`,
`right`). The `_` and `|` instructions pick a new direction from the top of the
stack via `Direction.chooseH` and `Direction.chooseV`:

- `chooseH v` = `.right` when `v = 0`, `.left` otherwise.
- `chooseV v` = `.down` when `v = 0`, `.up` otherwise.

`stepPos` moves a position one cell in a direction, reducing each coordinate
modulo the playfield size. This single function implements the toroidal wrap.

### The Stack (`LeanFunge.Core.Stack`)

`Stack` is an abbreviation for `List Int` with the top at the head. All
operations are total:

- `pop` returns `(rest, value)`; popping the empty stack yields `0`.
- `top`, `drop`, `dup`, and `swap` are defined in terms of `pop`/`push`.
- `applyBinary op` combines the top two elements; the first argument of `op` is
  the second-popped value (so `-` computes `second - top`).

> [!TIP]
> Because `pop` never fails, `step` remains a total function and every state
> transition is well-defined — no `Option` plumbing is needed for underflow.

### The Playfield (`LeanFunge.Core.Grid`)

A `Grid w h` is a structure wrapping a raw cell function `ℕ → ℕ → Char`.
Accessors reduce coordinates modulo `w`/`h`:

- `Grid.get g x y` reads `g.cells (y % h) (x % w)`.
- `Grid.put g x y c` writes the wrapped coordinate `(y % h, x % w)`.

Because every access is modulo the playfield size, the playfield is a torus and
`p`/`g` may address any cell regardless of the program's bounding box.
`Grid.ofRows` builds a grid from a list of rows, treating missing cells as
spaces.

### Instructions (`LeanFunge.Core.Instruction`)

`Instruction` covers the Befunge-93 instruction set plus `.nop` for any
undecoded character. `decodeChar` is the total character decoder.

### State and Semantics (`LeanFunge.Core.State`, `LeanFunge.Core.Semantics`)

`State w h` bundles the playfield, stack, instruction pointer, direction,
string-mode flag, output string, and an explicit character input stream.

`stepString` and `stepState` implement the string-mode and normal steps. The
top-level transition `step : State w h → Option (State w h)` returns `none`
when `@` is executed outside string mode:

```
step s =
  let ch := s.grid.get s.pc.1 s.pc.2
  match (s.stringMode, decodeChar ch) with
  | (true, _)      => some (stepString s ch)   -- string mode: push codes
  | (false, halt)  => none                     -- @ halts
  | (false, instr) => some (stepState s instr)
```

`run n s` iterates `step` `n` times, threading `none` once the program halts,
and `halts s` asserts that some finite `run` reaches `none`.

> [!NOTE]
> `?` (random direction) is modeled deterministically as "keep the current
> direction", which is one of the possible outcomes of the nondeterministic
> instruction. The interpreter is therefore a sound refinement of Befunge's
> nondeterministic semantics, and every verified example is deterministic.

> [!NOTE]
> `~` consumes the head of the input stream and pushes its code (`0` at EOF).
> `&` is not modeled and pushes `0`; the integer-input instruction is out of
> scope for the current verification.

## The Theory Layer

Theorems are kept separate from definitions (`LeanFunge/Theory`), mirroring the
project convention that `Core` files contain only definitions.

- `Theory/Stack.lean`: identity and involutive properties of the stack
  operations. These proofs are definitional (`rfl`).
- `Theory/Grid.lean`: `get_put_self`, `put_put`, and `get_put_other` —
  algebra of the self-modifying playfield. The proofs expose the `if`/`dite`
  behind `put` with `change`, then reason with `dif_pos`/`dif_neg`.
- `Theory/Direction.lean`: toroidal wrapping (`stepPos_right_from_last`,
  `stepPos_left_from_zero`, `stepPos_down_from_last`, `stepPos_up_from_zero`),
  proved with `Nat.mod` arithmetic under `[NeZero]` assumptions.
- `Theory/Step.lean`: single-step semantics for the instruction set. Each
  theorem unfolds `step`, rewrites the cell/stack/string-mode hypotheses, and
  simplifies with the relevant definitions. `run_halts_mono` shows that halting
  is monotone in the step count.

## Verified Example Programs

`LeanFunge/Examples` runs small programs through `run` and asserts their
behavior with the kernel `decide` tactic. Because everything in `Core` is
computable, each `run n state` call is evaluated and checked by Lean itself —
no external interpreter is trusted.

| Program | Playfield | Verified behavior |
| :--- | :--- | :--- |
| `HelloWorld` | `"!dlroW olleH",,,,,,,,,,,,@` (27×1) | output `Hello World!`, halts after 27 steps |
| `Arithmetic` | `23+.@` (5×1) | stack top `5`, output `5`, halts |
| `Trampoline` | `12#3+@` (6×1) | `#` skips the `3`; final stack `[3]` |
| `PutGet` | `521p21g.@` over a blank row (9×2) | `p` stores `5`, `g` retrieves it, output `5` |

## Project Structure

- `LeanFunge/Core`: Definitions (Direction, Stack, Grid, Instruction, State,
  Semantics).
- `LeanFunge/Theory`: Theorems (Stack, Grid, Direction, Step).
- `LeanFunge/Examples`: Verified example programs.
- `Tests`: Executable `example` statements that re-assert the theorems.
- `scripts`: Repository guard checks (naming, imports, copyright, formatting).

## Build Notes

The project requires Mathlib pinned at `v4.28.0` (see `lakefile.toml`). The
playfield and position arithmetic rely on the `ℕ` notation from
`Mathlib.Data.Nat.Notation`; `Core` files import it directly. In Lean 4.28
`List.get?` was removed, so `Grid.ofRows` uses `List.getD`.
