# LeanFunge

**Formal Verification of the Befunge Esolang in Lean 4.**

[![CI](https://github.com/bangyen/leanfunge/actions/workflows/lean_action_ci.yml/badge.svg)](https://github.com/bangyen/leanfunge/actions/workflows/lean_action_ci.yml)
[![Lean 4 Version](https://img.shields.io/badge/Lean-4.28.0-blue.svg)](https://leanprover.github.io/)
[![Mathlib4](https://img.shields.io/badge/Mathlib-4-brightgreen.svg)](https://github.com/leanprover-community/mathlib4)
[![License: MIT](https://img.shields.io/badge/License-MIT-yellow.svg)](LICENSE)

LeanFunge constructs a fully machine-checked, executable formalization of the
[Befunge-93](https://en.wikipedia.org/wiki/Befunge) esolang in the
[Lean 4](https://leanprover.github.io/) interactive theorem prover, and proves
properties about the language. Esolangs like Befunge are defined by loose,
human-readable specifications that leave many details ambiguous (stack
underflow, `p`/`g` coordinate order, wrapping behavior, input at end-of-file).
LeanFunge pins down one precise, total, deterministic formalization — every
transition of the interpreter is a pure Lean function — and then proves
theorems about it.

## Architecture

For a detailed overview of the project's design and the full list of verified
theorems and example programs, see [ARCHITECTURE.md](ARCHITECTURE.md).

The implementation is organized into `Core` (definitions), `Theory`
(verified theorems), `Examples` (verified example programs), and `Tests`
(kernel re-assertions of the theorems and examples).

## Results

- **Total, deterministic interpreter** (`Core.Semantics`): `step`/`run` execute
  any Befunge-93 playfield as a pure Lean function, with `@` the sole halting
  instruction.
- **Stack algebra** (`Theory.Stack`): push/pop round-trip, swap involution,
  duplication, and binary-op consumption.
- **Playfield algebra** (`Theory.Grid`): the toroidal playfield, `get`/`put`
  round-trips, and the `p`/`g` write-then-read round-trip at wrapped
  coordinates.
- **Toroidal wrapping** (`Theory.Direction`): single-step and iterated wrapping
  in all four directions.
- **Complete single-step semantics** (`Theory.Step`, `Theory.StepOps`): a
  theorem for every instruction, including `#` skipping across the wrap.
- **Nondeterminism** (`Theory.Random`): `?` as a transition relation, with the
  deterministic interpreter a sound refinement.
- **I/O semantics** (`Theory.Parser`, `Theory.Output`): `&` parses a signed
  decimal integer and `.` prints through a redefinable encoding that round-trips
  with the parser.
- **Invariance, termination, divergence** (`Theory.Invariance`, `Theory.Run`,
  `Theory.Termination`): only `p` writes the playfield, ranked machines
  terminate, and all-space runs never halt.
- **Turing-completeness groundwork** (`Theory.Completeness`): a formalized
  two-counter Minsky machine, the `2^c1 * 3^c2` counter-pair encoding with
  its stack arithmetic (increment is `*2`/`*3`, decrement is `/2`/`/3`, and
  the zero tests are `% 2`/`% 3`), run-level straight-line routing lemmas
  (`run_spaces`, `run_spaces_v`) for the corridor geometry, and a concrete
  playfield that simulates a small two-counter machine step-for-step with the
  counters carried in the single encoded stack value. A generic simulation is
  proven for the branch-free fragment: any program of `inc` instructions
  followed by a `halt` is compiled to a single playfield row, and the
  interpreter run is proved to match the two-counter machine step for step.
  The `decz` block snippets are proven generically: running the test cells
  `: 2 % |` or `: 3 % |` leaves the encoded pair on the stack and branches
  down on the even/divisible case, up on the odd/non-divisible case, and the
  decrement cells `2 /`/`3 /` divide it. A concrete program with a genuine
  backward jump (a loop that moves counter 1 into counter 2) is verified by
  kernel computation, and its backward-jump corridor is also proved
  symbolically: the general `run_spaces_turn` routing lemma composes the
  `^`-up, `<`-left, and `v`-down turns that carry the pointer back into
  instruction 0's block. The counter-2 analogue (moving counter 2 into
  counter 1, testing with `% 3` and dividing by `3 /`) is verified the same
  way, exercising the counter-2 branch of the `decz` snippet.
  The generic simulation's layout foundation is in place: a `playfieldOf`
  generator lays each instruction's block at a chained entry column and block
  row (the `decz` branch one column left of the next entry, so drop columns
  stay clean of `|` cells), with the entry columns and block rows proven
  strictly increasing, and one header corridor row per block so every jump
  edge has a dedicated route. The generated playfield's fall-through is
  verified: from a block's exit the pointer drops down the entry column
  through the gap to the next block's `>`, both for an `inc` exit and for the
  `decz` branch jog, proved symbolically with the routing lemmas. The
  generated playfields of the transfer program and of a looping program (a
  genuine backward jump) fully simulate their two-counter machines by kernel
  computation, with the forward and backward corridors verified. The generic
  cell lookup is proven: any cell within a block's row range reads back
  exactly the block's body cell (`playfield_block_get`), and generic block
  execution is proven for every instruction — an arbitrary `inc` block
  multiplies the stack top by its counter digit and exits down its
  fall-through column, a `decz` block tests the remainder at the branch cell
  and either divides the value and falls through (counter positive) or sends
  the pointer up its corridor column (counter zero), a `jump` block sends the
  pointer up its corridor column, and `halt` stops the machine. The generic
  fall-through drop is proven: one step down from a block's bottom row lands
  the pointer on the next block's entry.
- **Verified example programs** (`LeanFunge.Examples`): kernel-checked
  `HelloWorld`, `Arithmetic`, `Trampoline`, `PutGet`, `Countdown`, `Factorial`,
  `Input`, `DecimalOutput`, `SelfMod`, `Quine`, `Echo`, and `Wrap`.

## Roadmap

The generic simulation of arbitrary two-counter machines on the generated
playfield is in progress. The cell-correctness foundation and the `inc`,
`jump`, and `halt` block executions are proven generically; the remaining
steps are:

| Task | Priority | Status |
| :--- | :--- | :--- |
| **Generic `decz` block execution** | High | Proven: the test cells and both branches (decrement down, jump up) on the playfield. |
| **Generic routing** | High | The fall-through drop is proven; remaining: the corridor up-turn-drop for arbitrary jump targets, including running through `v` cells. |
| **Simulation induction** | High | Assembling the block and routing lemmas into a step-for-step simulation of `CMInstr.run` for arbitrary programs. |
| **Universality statement** | High | Every two-counter machine has a simulating playfield; hence Befunge-93 is computationally universal. |

The following items have all been attempted and are confirmed roadblocks, not
untried work.

| Task | Priority | Status |
| :--- | :--- | :--- |
| **Generic 2CM simulation** | High | The branch-free fragment is proven and a concrete program with a backward jump is verified; needs the generic branch (`decz`) routing for arbitrary jump targets. |
| **String-mode block semantics** | Medium | Needs a grid-suffix run lemma relating a sub-block run to a narrow-grid induction. |
| **Run-level output monotonicity** | Medium | Single-step cases are proven; the remaining ~23 instructions are a mechanical case analysis. |
| **Nop-run pointer movement** | Low | Needs run-level lemmas on top of the `stepPos` threading. |
| **Input consumption is prefix-only** | Medium | Suffix helpers are proven; `parseInt_suffix` needs a match-reduction lemma. |
| **String-mode block output round-trip** | Medium | Shares the block roadblock, plus the `,` composition. |
| **Halting characterization** | Medium | Needs a `decodeChar` match lemma for a generic cell. |
| **I/O separation** | Medium | The 27-instruction case analysis. |

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
- The completeness development (`Theory.Completeness`) has verified the
  two-counter machine semantics, the pair encoding, the generic cell lookup
  and generic `inc`/`jump`/`halt` block execution on the generated playfield,
  and concrete simulated programs end-to-end. The fully generic theorem —
  that *every* two-counter machine has a playfield that simulates it — is in
  progress (see the Roadmap); it needs the generic `decz` block execution and
  the geometric routing lemmas. It does not require changing the fixed-grid
  semantics: unbounded memory comes from the unbounded stack, and the finite
  playfield supplies only finite control.

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
