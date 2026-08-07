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
> The full nondeterminism of `?` is captured by the transition relation
> `stepRel : State w h → Option (State w h) → Prop`, which allows any of the
> four directions at a `?` outside string mode. The executable interpreter
> fixes `?` to "keep the current direction" — one of the relation's possible
> outcomes — and `Theory.Random` proves this interpreter is a sound refinement
> of `stepRel`. Every verified example is deterministic.

> [!NOTE]
> `~` consumes the head of the input stream and pushes its code (`0` at EOF).
> `&` parses a decimal integer from the input stream: leading spaces are
> skipped, an optional `-` sign is honored, and a maximal run of digits is
> consumed (`Core/Parser`). `Theory/Parser` proves that interpreting a
> number's decimal digits reconstructs the number.

## The Theory Layer

Theorems are kept separate from definitions (`LeanFunge/Theory`), mirroring the
project convention that `Core` files contain only definitions.

- `Theory/Stack.lean`: identity and involutive properties of the stack
  operations. These proofs are definitional (`rfl`).
- `Theory/Grid.lean`: `get_put_self`, `put_put`, and `get_put_other` —
  algebra of the self-modifying playfield. The proofs expose the `if`/`dite`
  behind `put` with `change`, then reason with `dif_pos`/`dif_neg`.
  `ofRows_cells_out_of_rows` and `ofRows_cells_out_of_col` prove that the
  playfield construction fills missing rows and cells with spaces, and
  `put_get_roundtrip` proves the interpreter's `p`/`g` round-trip for valid
  non-negative codes.
- `Theory/Direction.lean`: toroidal wrapping (`stepPos_right_from_last`,
  `stepPos_left_from_zero`, `stepPos_down_from_last`, `stepPos_up_from_zero`),
  proved with `Nat.mod` arithmetic under `[NeZero]` assumptions;
  `runPos_right`/`runPos_down`/`runPos_up`/`runPos_left` generalize this to
  `k` steps in each direction, landing at the modular offset.
- `Theory/Step.lean`: single-step semantics for the instruction set. Each
  theorem unfolds `step`, rewrites the cell/stack/string-mode hypotheses, and
  simplifies with the relevant definitions. `run_halts_mono` shows that halting
  is monotone in the step count.
- `Theory/StepOps.lean`: single-step semantics for the remaining instructions —
  `/`, `%`, the comparison instruction, `:`, `\`, `$`, `~` (including the
  end-of-input case), and `&` — completing single-step coverage of the
  instruction set. `step_trampoline_right_from_last` proves that `#` at the
  last column skips across the torus wrap to column 1.
- `Theory/Invariance.lean`: program-level equivalence. A space is a pure no-op;
  every instruction except `p` leaves the playfield unchanged; and `p` writes
  exactly the addressed cell (bridging to `Theory/Grid`). These are the
  foundational "only `p` mutates the playfield" properties of the language.
- `Theory/Random.lean`: nondeterminism. The transition relation `stepRel`
  allows any direction at `?`; `step_refines_stepRel` shows the deterministic
  interpreter is a sound refinement, `stepRel_random_four` shows all four
  directions are reachable `?` outcomes, and the uniqueness/non-uniqueness
  theorems characterize the determinism boundary.
- `Theory/Parser.lean`: integer input. `parseInt` (in `Core/Parser`) reads a
  signed decimal integer from the input stream; `natDigitsValue_natDigits`
  proves the decimal digits round-trip, and `parseInt_natDigits` shows parsing
  the digit characters of a number consumes the stream and recovers it.
- `Theory/Output.lean`: integer output. `formatInt` (in `Core/Parser`) is the
  redefinable decimal encoding used by the `.` instruction, a reducible
  counterpart of `toString`; `toDigits_natDigits` identifies it with the
  digits of `natDigits`, and `parseInt_formatInt` proves that re-parsing any
  `formatInt` output with `&` recovers the original integer — the generic dual
  of the `&` parser.
- `Theory/Run.lean`: run-level invariance. A grid-preserving run leaves the
  playfield unchanged across the whole run (`run_grid_invariant`), so a cell
  never written by the put instruction keeps its value; a nop-only run leaves
  the stack unchanged (`run_stack_invariant`).
- `Theory/Run/Divergence.lean`: divergence. A run on an all-space playfield
  never halts (`run_space_some`), and every successor state keeps the all-space
  playfield and stays out of string mode (`run_space_step`).
- `Theory/Run/Relational.lean`: multi-step relational semantics. `runRel`
  lifts `stepRel` to finite runs, including halt propagation; deterministic
  runs refine it, one-step relational runs coincide with `stepRel`, and both
  deterministic and relational runs compose across continuations.
- `Theory/Termination.lean`: termination analysis. `decreasing_machine_terminates`
  covers single counters, and `rankedMachine_terminates` generalizes it to any
  state type with a strictly decreasing ranking function, instantiated by the
  two-counter machine.
- `Theory/Completeness/`: Turing-completeness groundwork. `TwoCounter.lean`
  formalizes a Minsky two-counter machine (`inc`, `decz`, `halt`) with total,
  deterministic `step`/`run` semantics. `PairEncoding.lean` proves the
  arithmetic of the counter-pair encoding `2^c1 * 3^c2` used to carry both
  counters in a single stack value: increment is multiplication by `2`/`3`,
  decrement is division by `2`/`3`, and the zero tests are `value % 2 = 0`
  (counter 1 positive, even) and `value % 3 = 0` (counter 2 positive,
  divisible by 3). Both the `ℕ`-level identities and their `Int`-level
  counterparts (via `Int.natCast_ediv`/`natCast_emod`) are proven.
  `Routing.lean` proves the run-level geometry of the corridors: `run_spaces`
  moves the pointer through a run of spaces via `runPos` without touching the
  stack, the grid, the direction, string mode, the output, or the input, and
  `run_spaces_turn` (with `run_spaces_v` as a special case) composes a run of
  spaces with a turn cell of any direction, the general corridor pattern.
  `Block.lean`/`BlockC2.lean` prove the `decz` block snippets: the test cells
  `: 2 % |`/`: 3 % |` leave the encoded pair on the stack and branch down on
  the even/divisible case and up on the odd/non-divisible case, and the
  decrement cells `2 /`/`3 /` divide the value by 2/3.
  `Loop.lean`/`LoopC2.lean` verify concrete looping programs that move one
  counter into the other — testing counter 1 with `% 2` and counter 2 with
  `% 3` respectively — by kernel computation. `Layout.lean` begins the generic
  simulation: it defines the block geometry (entry columns chain by the block
  widths, block rows by the heights, both strictly increasing) and a
  `playfieldOf` generator that places every instruction's block cells, with
  concrete placement checks verified by kernel computation.
  `Linear.lean`/`LinearRow.lean`/`LinearSimulation.lean`/`LinearMain.lean`
  then prove a fully generic simulation of the branch-free fragment: a
  program of `inc` instructions followed by a `halt` is compiled to a single
  playfield row `> 2* 3* ... @`, the list and cell lemmas read each
  instruction's cells out of the row, `linear_prefix` shows by induction that
  the interpreter reaches each instruction with the encoded prefix on the
  stack, and `linear_simulation` equates the interpreter stack with the
  encoding of the two-counter machine's final counters.
  `Simulation.lean` lays out a concrete playfield for a small 2CM program —
  one horizontal instruction block per instruction, a `|` branch that falls
  through to the decrement `2/` on an even encoding and jumps to the halt
  block on an odd one, and `^`/`<` corridors for routing — and verifies by
  kernel computation that the interpreter simulates the machine with the
  encoded pair on the stack. `Loop.lean` does the same for a program with a
  genuine backward jump (`jump 0`), routing the loop-back up a dedicated
  column and into instruction 0's block; the two-counter machine instruction
  set includes the standard unconditional `jump`. The loop's backward-jump
  corridor is also proved symbolically (`loop_routing_back`) by composing
  `run_spaces_turn` segments with `run_append`, so the corridor geometry is
  verified by proof rather than kernel computation alone.
  `LayoutFallthrough.lean`, `LayoutJump.lean`, and `LoopCorridor.lean` verify
  the generated playfield end to end: the fall-through drops and the forward
  and backward jump corridors of the transfer and looping programs, all on
  the playfield emitted by `playfieldOf`. The corridor rows are a header of
  one row per block, so every jump edge has a dedicated route and a jump
  involving block 0 does not collide.
  The generic cell lookup is proven by
  `LayoutCells.lean`/`LayoutCellRange.lean`/`LayoutCellMain.lean`: the
  playfield readback equals a last-cell lookup over the flattened placed
  cells, each block's body cells sit in its own row range and its corridor on
  its header row, and therefore any cell within a block's row range reads
  back exactly the block's body cell (`playfield_block_get`), for arbitrary
  programs. `LayoutBlock.lean` proves the generic block executions: an `inc`
  block multiplies the stack top by its counter digit and exits down its
  fall-through column, a `decz` block tests the remainder at the branch cell
  and either divides the value and falls through (counter positive) or sends
  the pointer up its corridor column (counter zero), a `jump` block sends the
  pointer up its corridor column, and `halt` stops the machine.
  `LayoutRouting.lean` proves the generic fall-through drop: the bottom-right
  corner of a block's body is a space, and one step down from a block's
  bottom row lands the pointer on the next block's entry. Remaining: the
  generic corridor routing for arbitrary jump targets, then the simulation
  induction equating the interpreter run with the two-counter machine's run
  for every program.

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
| `Countdown` | 26×4 loop with cell counter | output `321`, halts after 133 steps |
| `Factorial` | 26×4 loop with cell counter | computes `3!`, final stack `[6]`, halts |
| `Input` | `&2+.@`, `&.@`, `&@` (5×1, 3×1, 2×1) | reads `5`→prints `7`, reads `12`→prints `12`, reads `-3` onto the stack |
| `DecimalOutput` | 48×10 extraction/print loops | reads `0`, `5`, `123`, `12345` and prints each back as characters; the printed output re-parses to the original number |
| `SelfMod` | `>88*80p  `, `>77*70p  @` (10×1) | writes its own `@` and halts; writes a `1` and executes it |
| `Quine` | `01->1# +# :# 0# g# ,# :# 5# 8# *# 4# +# -# _@` (45×1) | reads each playfield cell with `g` and prints it with `,`; after 2407 steps the output is exactly its own source, halting one step later |
| `Echo` | `~,@` (3×1) | reads a character with `~` and prints it back with `,`; output `x`, halts after 3 steps |
| `Wrap` | `88*00p` (6×1) | computes `64`, writes `@` into its own first cell with `p`, then wraps off the right edge to column 0 and executes the `@`, halting after 7 steps |

`SelfMod` showcases Befunge's self-modifying playfield: both programs compute
a character code, store it into an empty cell with `p`, and then let the
instruction pointer reach and execute the written instruction.

`DecimalOutput` is the first verified "library" program: a reusable routine
that reads a non-negative integer with `&` and prints it back as characters.
The running value lives in `(0, 0)` and the digit count in `(1, 0)`; an
extraction loop divides by 10 (`55+/`), stores each remainder digit in a cell
of column 0, and stores the quotient back, while a print loop fetches the
digits in reverse order, adds 48, and prints with `,`. The theorem
`decimal_roundtrip` re-parses each printed output with `parseInt`,
reconstructing the original number — the dual of the `&` parser.

The two looping programs use a common structure: the counter lives in the cell
`(0, 0)`, the loop check is `00g!|` (fetch, logical-not, vertical branch), and
the `|` exits upward to `@` when the counter reaches zero while the loop body
runs downward, multiplies/prints, decrements, and stores the counter back.

Because `run n` evaluations can be deep (130+ steps), the project raises
`maxRecDepth` to `10000` in `lakefile.toml` so the kernel `decide` tactic can
verify the loop programs without hitting the default recursion limit.

## Project Structure

- `LeanFunge/Core`: Definitions (Direction, Stack, Grid, Instruction, State,
  Semantics, Parser).
- `LeanFunge/Theory`: Theorems (Stack, Grid, Direction, Step, StepOps,
  Invariance, Random, Parser, Output, Run, Termination, Completeness).
- `LeanFunge/Examples`: Verified example programs.
- `Tests`: Executable `example` statements that re-assert the theorems.
- `scripts`: Repository guard checks (naming, imports, copyright, formatting).

## Build Notes

The project requires Mathlib pinned at `v4.28.0` (see `lakefile.toml`). The
playfield and position arithmetic rely on the `ℕ` notation from
`Mathlib.Data.Nat.Notation`; `Core` files import it directly. In Lean 4.28
`List.get?` was removed, so `Grid.ofRows` uses `List.getD`.
