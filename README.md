# LeanFunge

**Formal Verification of the Befunge Esolang in Lean 4.**

[![CI](https://github.com/bangyen/leanfunge/actions/workflows/lean_action_ci.yml/badge.svg)](https://github.com/bangyen/leanfunge/actions/workflows/lean_action_ci.yml)
[![Lean 4 Version](https://img.shields.io/badge/Lean-4.28.0-blue.svg)](https://leanprover.github.io/)
[![Mathlib4](https://img.shields.io/badge/Mathlib-4-brightgreen.svg)](https://github.com/leanprover-community/mathlib4)
[![License: MIT](https://img.shields.io/badge/License-MIT-yellow.svg)](LICENSE)

LeanFunge constructs a fully machine-checked, executable formalization of the
[Befunge-93](https://en.wikipedia.org/wiki/Befunge) esolang in the
[Lean 4](https://leanprover.github.io/) interactive theorem prover, and proves
properties about the language: stack algebra, toroidal wrapping, the
self-modifying playfield, string mode, and the single-step semantics of the
instruction set. Esolangs like Befunge are defined by loose, human-readable
specifications that leave many details ambiguous (stack underflow, `p`/`g`
coordinate order, wrapping behavior, input at end-of-file). LeanFunge pins down
one precise, total, deterministic formalization — every transition of the
interpreter is a pure Lean function — and then proves theorems about it.

## Architecture

For a detailed overview of the project's design — the toroidal playfield, the
total stack, the single-step transition function, and the relational treatment
of `?` — see [ARCHITECTURE.md](ARCHITECTURE.md).

The implementation is organized into `Core` (definitions), `Theory`
(verified theorems), `Examples` (verified example programs), and `Tests`
(kernel re-assertions of the theorems and examples).

## Results

**Core primitives** (`LeanFunge.Core`)

- `Direction`: the four cardinal directions and the `_`/`|` choice functions.
- `Stack`: the Befunge data stack (a list of integers) with push/pop/top/drop/
  dup/swap/binary-op. Underflow yields `0`.
- `Grid`: the `w`×`h` playfield. Cells are addressed modulo the playfield size,
  so the playfield is a torus; `p` and `g` may read and write any cell.
- `Instruction` + `decodeChar`: the Befunge-93 instruction set and its
  character decoder.
- `State`: the full interpreter state (playfield, stack, instruction pointer,
  direction, string mode, output, and input streams).
- `Semantics`: `stepString`, `stepState`, `step`, `run`, and `halts` — a total,
  deterministic single-step transition function.

**Verified properties** (`LeanFunge.Theory`)

- *Stack algebra* (`Theory.Stack`): popping after pushing restores the stack,
  swapping is an involution, duplication copies the top, and binary operations
  consume exactly two elements.
- *Playfield algebra* (`Theory.Grid`): reading immediately after writing
  returns the stored value (`get_put_self`), writing twice keeps the last write
  (`put_put`), and writing to one cell does not disturb distinct cells
  (`get_put_other`).
- *Toroidal wrapping* (`Theory.Direction`): moving right from the last column
  wraps to column `0`, moving left from column `0` wraps to the last column,
  and symmetrically for rows; iterating rightward steps lands at the modular
  column (`runPos_right`).
- *Step semantics* (`Theory.Step`, `Theory.StepOps`): the `@` instruction
  halts; digits push; `+`, `-`, `*`, `/`, `%` combine the top two values; the
  comparison pushes `1` when the second-popped value exceeds the top; `:`, `\`,
  `$` duplicate, swap, and discard the top; the direction arrows reorient the
  pointer; `_` and `|` branch on the top of the stack; `"` toggles string mode
  (in which characters are pushed as their codes); `#` skips the next cell;
  `p`/`g` store and fetch playfield values; `.`/`,` write to the output; and
  `~`/`&` read from the input stream.
- *Program-level invariance* (`Theory.Invariance`): a space is a pure no-op
  (`step_nop`), every instruction except `p` leaves the playfield unchanged
  (`stepState_grid_of_ne_put`), and `p` stores its value at the addressed cell
  (`step_put_grid`), bridging the instruction semantics to the grid algebra.
- *Run-level invariance* (`Theory.Run`): a grid-preserving run leaves the
  playfield unchanged across the whole run (`run_grid_invariant`), and a
  nop-only run leaves the stack unchanged (`run_stack_invariant`).
- *Nondeterminism* (`Theory.Random`): the transition relation `stepRel` allows
  any of the four directions at `?`; the deterministic interpreter is a sound
  refinement of it, and all four directions are reachable `?` outcomes.
- *Termination* (`Theory.Termination`): a machine whose transitions strictly
  decrease a ranking function halts or reaches rank zero in finitely many
  steps, covering the looping examples.
- *Integer output round-trip* (`Theory.Output`): the `.` instruction prints
  through a redefinable `formatInt` encoding (`Core/Parser`), and
  `parseInt_formatInt` proves that re-parsing any `formatInt` output with `&`
  recovers the original integer — the generic dual of the `&` parser.

**Verified example programs** (`LeanFunge.Examples`)

Each example is executed by the interpreter itself and its behavior checked by
the Lean kernel:

- `HelloWorld`: `"!dlroW olleH",,,,,,,,,,,,@` prints `Hello World!` and halts.
- `Arithmetic`: `23+.@` computes `2 + 3 = 5`, prints it, and halts.
- `Trampoline`: `12#3+@` shows that `#` skips the `3`, so the sum is `3`.
- `PutGet`: `521p21g.@` stores `5` into the playfield with `p` and retrieves it
  with `g`, demonstrating self-modification.
- `Countdown`: a loop driven by `|` prints `321` — each iteration fetches,
  prints, and decrements a counter held in a cell, then exits upward on zero.
- `Factorial`: a loop computes `3! = 6` — the accumulator lives on the stack
  and the counter in a cell, multiplied with `*` each iteration.
- `Input`: `&2+.@` reads `5` and prints `7`; `&.@` reads a multi-digit or
  negative integer (`12`, `-3`) from the input stream.
- `DecimalOutput`: a "library" routine that reads a non-negative integer with
  `&` and prints it back as characters — an extraction loop divides by 10
  (`/`, `%`) storing the digits in cells, and a print loop fetches them in
  reverse order and prints with `,`. Verified for `0`, `5`, `123`, and
  `12345`, and `decimal_roundtrip` shows the printed output re-parses to the
  original number (the dual of the `&` parser).
- `SelfMod`: `>88*80p  ` writes its own `@` instruction with `p` and then runs
  into it and halts; `>77*70p  @` writes a `1` instruction and executes it.
- `Quine`: the classic `01->1# +# :# 0# g# ,# :# 5# 8# *# 4# +# -# _@` prints
  its own source code by reading each cell of the playfield with `g` and
  printing it with `,`; after 2407 steps the output is exactly the program's
  own source, and it halts one step later.
- `Echo`: `~,@` reads one character from the input stream with `~` and prints
  it back with `,`, then halts — the first example exercising character input.

## Roadmap

| Task | Priority | Justification |
| :--- | :--- | :--- |
| **String-mode block semantics** | Medium | `Theory.Step` covers the single-step `"` toggle, but there is no block-level theorem: proving that a balanced `"..."` region pushes exactly its interior character codes requires threading `run` through a variable-width playfield, a multi-step induction. |
| **Toroidal iteration family** | Low | `runPos_right` covers only rightward steps; analogous lemmas for `left`/`up`/`down` would complete the modular generalization of the wrapping theorems. |
| **Trampoline wrapping** | Low | `#` skips one cell, but there is no theorem about it doing so across the torus edge (e.g. `#` at the last column skipping to column 1). |
| **`ofRows` missing-cell behavior** | Low | The playfield construction treats missing cells as spaces, but no theorem proves that `Grid.ofRows` returns `' '` for rows or cells beyond the given list. |

## Scope & Limitations

**Scope.** LeanFunge formalizes Befunge-93 and proves properties about the
language — stack algebra, toroidal wrapping, the self-modifying playfield,
string mode, and the single-step semantics of the instruction set — together
with verified example programs. It deliberately does not develop verified
program transformations or optimizations (spacing, rotation, dead no-op
elimination, constant folding); the program-equivalence framework that
supported them was removed as out of scope. A Befunge-98 fingerprint and
self-interpreters (programs that interpret Befunge, verified to match direct
execution) are also out of scope, as their correctness proofs are
program-equivalence reasoning rather than properties of the language.

**Design choices.** Befunge's specification leaves several behaviors
unspecified; LeanFunge makes the following choices, all documented in
`ARCHITECTURE.md`:

- **Toroidal playfield**: coordinates are reduced modulo the playfield size on
  every access, so the playfield is a torus.
- **Stack underflow**: popping an empty stack yields `0`.
- **`p`/`g` argument order**: coordinates are popped as `y` then `x`, then the
  value, matching the Funge-98 convention.
- **Input**: `~` consumes from an explicit input stream (pushing `0` at EOF);
  `&` parses a decimal integer from the stream (skipping leading spaces and
  handling an optional `-` sign), leaving the remaining input for later.
- **`?` (random)**: the executable interpreter fixes `?` to "keep the current
  direction", which is one of the possible outcomes of the nondeterministic
  instruction. The full nondeterminism is captured by the transition relation
  `stepRel`, and `Theory.Random` proves the interpreter is a sound refinement
  of it and that `?` may choose any of the four directions.

**Limitations.**

- The `DecimalOutput` program's round-trip (`decimal_roundtrip`) is verified
  for concrete inputs only — a generic statement would require a
  program-level correctness proof of its loops. The `.` output encoding's
  round-trip (`parseInt_formatInt`) is fully generic.
- Every verified example is deterministic; the nondeterminism of `?` is
  captured by the transition relation rather than the executable interpreter.

## Installation & Building

Make sure you have [elan](https://github.com/leanprover/elan) installed for
Lean 4 version management.

```bash
git clone https://github.com/bangyen/leanfunge.git
cd leanfunge
lake exe cache get  # Downloads the pre-compiled Mathlib libraries
lake build
```

Then run the verification:

```bash
lake test           # Builds the test suite
lake lint           # Runs the linter
./scripts/check_all.sh  # Runs the repository guard checks
```

## Contributing

This repo uses standard Mathlib naming conventions and the same guard scripts
as LeanSharp. If you are interested in extending the formalization — for
example, another verified example program — feel free to open a pull request.

## Citation

If you use this work in your research, please cite:

```bibtex
@misc{pham_leanfunge_2026,
  author = {Pham, Bangyen},
  title = {LeanFunge: Formal Verification of the Befunge Esolang in Lean 4},
  year = {2026},
  url = {https://github.com/bangyen/leanfunge}
}
```
