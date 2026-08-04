# LeanFunge

**Formal Verification of the Befunge Esolang in Lean 4.**

[![Lean 4 Version](https://img.shields.io/badge/Lean-4.28.0-blue.svg)](https://leanprover.github.io/)
[![Mathlib4](https://img.shields.io/badge/Mathlib-4-brightgreen.svg)](https://github.com/leanprover-community/mathlib4)
[![License: MIT](https://img.shields.io/badge/License-MIT-yellow.svg)](LICENSE)

LeanFunge constructs a fully machine-checked, executable formalization of the
[Befunge-93](https://en.wikipedia.org/wiki/Befunge) esolang in the
[Lean 4](https://leanprover.github.io/) interactive theorem prover, and proves
properties about the language: stack algebra, toroidal wrapping, the
self-modifying playfield, string mode, and the single-step semantics of the
instruction set.

## Motivation

Esolangs like Befunge are defined by loose, human-readable specifications that
leave many details ambiguous (stack underflow, `p`/`g` coordinate order,
wrapping behavior, input at end-of-file). LeanFunge pins down one precise,
total, deterministic formalization — every transition of the interpreter is a
pure Lean function — and then proves theorems about it.

## What is formalized

The formalization lives in `LeanFunge/Core` and `LeanFunge/Theory`.

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
  and symmetrically for rows.
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

## Roadmap

| Task | Priority | Justification |
| :--- | :--- | :--- |
| **Verified looping programs** (countdown, factorial) | ✅ Done | `Countdown` prints `321` and `Factorial` computes `3! = 6`, both via `|` loops with cells and verified by the kernel. |
| **Program-level equivalence** (nop invariance, `p`/`g` roundtrip) | ✅ Done | `Theory.Invariance` proves spaces are no-ops, only `p` modifies the playfield, and `p` stores the addressed cell. |
| **`?` as true nondeterminism** | ✅ Done | `stepRel` is a relational transition and `Theory.Random` proves the interpreter is a sound refinement, plus all four directions are reachable `?` outcomes. |
| **Faithful `&` integer input** | ✅ Done | `Core/Parser` implements a decimal parser (sign, spaces, multi-digit) and `Theory/Parser` proves the digits round-trip; `Input` verifies programs reading `5`, `12`, and `-3`. |
| **Self-modification showcase** | ✅ Done | `SelfMod` verifies programs that write their own `@` (halting by rewriting) and that write then execute a `1` instruction. |
| **Verified termination analysis** | ✅ Done | `Theory/Termination` proves strictly decreasing counters are bounded and hit zero, and that any decreasing-counter machine halts or reaches zero in finitely many steps, covering the loop examples. |
| **Run-level program equivalence** | ✅ Done | `Theory/Run` proves a grid-preserving program leaves the playfield unchanged across a whole run, and a nop-only run leaves the stack unchanged. |
| **Complete the instruction set** | ✅ Done | `Theory/StepOps` adds single-step theorems for `/`, `%`, the comparison, `:`, `\`, `$`, `~` (including EOF), and `&` using the existing patterns, completing single-step coverage. |
| **Verified decimal output routine** | ✅ Done | `DecimalOutput` reads `0`, `5`, `123`, and `12345` with `&` and prints each back as characters via a `div`/`mod` extraction loop and a reverse print loop; `decimal_roundtrip` shows the printed output re-parses to the original number — the first verified "library" program, the dual of the `&` parser. |
| **Program equivalence** | ✅ Done | `Theory/Program` defines strict, observational, and ordered stuttering equivalence; verified examples show that leading-space padding preserves the behavior of `@` and `23+.@`. |
| **Determinism for `?`** | ✅ Done | `Theory.Random` proves non-random states have a unique relational successor and `?` states have distinct reachable successors, completing the determinism boundary around the nondeterministic instruction. |
| **Multi-step relational semantics** | ✅ Done | `Theory/Run/Relational` lifts `stepRel` to finite runs, proves deterministic execution is a valid relational trace, identifies one-step runs with `stepRel`, and propagates relational halting. |
| **Compositional program blocks** | ✅ Done | `run_append` and `runRel_append` compose deterministic and relational executions across continuations, providing the sequencing foundation for block equivalence. |
| **State simulation relations** | ✅ Done | `Theory/Program` defines dimension-independent bisimulations that preserve observations, halting, and successor states, then lifts them to whole deterministic runs. |
| **Verified spacing transformations** | ✅ Done | `Grid.prependSpace`, `prependSpaceState`, and the arithmetic bisimulation verify a width-changing leading-space rewrite under explicit no-wrap conditions. |
| **Verified program transformations** | ✅ Done | Spacing rewrites are verified; rotation commutes with the full non-branching instruction set but is unsound in general (`rotateCounter` shows `_` changes behavior), so full rotation is documented as a limitation. |
| **Rotation-safe rewrites** | Medium | Verify clockwise rotation under a `rotationSafe` predicate restricting programs to the sound instruction set (no `_`, `|`, `?`, `p`, `g`). |
| **I/O behavior contracts** | Medium | Define input-consumption and output-production contracts and use them to compose the verified parser and decimal-output routines. |
| **Verified optimization rewrites** | Medium | Verify local stack-neutral rewrites such as no-op elimination and simple constant folding. |
| **Generic ranking-function termination API** | Medium | Generalize the decreasing-counter proofs into reusable ranking-function infrastructure for verified loops. |
| **Restricted self-interpreter** | Medium | Verify an interpreter for a small instruction subset as a staged simulation milestone, without committing to the full self-interpreter. |
| **Befunge-93 self-interpreter** | Low | A Befunge program that interprets Befunge-93, verified against the interpreter itself — the ultimate in-scope showcase, but a large lift. |

## Design decisions

Befunge's specification leaves several behaviors unspecified; LeanFunge makes
the following choices, all documented in `ARCHITECTURE.md`:

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
example, a verified Befunge-98 fingerprint, a termination analysis, or a
self-interpreter — feel free to open a pull request.

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
