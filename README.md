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
- **Turing completeness** (`Theory.Completeness`): a fully verified
  construction showing Befunge-93 computes what every two-counter machine
  computes. The two-counter Minsky machine semantics (`TwoCounter`), the
  `2^c1 * 3^c2` counter-pair encoding with its stack arithmetic
  (`PairEncoding`), and a `playfieldOf` generator that lays each instruction
  as a block at a chained entry column and block row, with one header corridor
  row per block so every jump edge has a dedicated route, are formalized. The
  layout is proved well formed (strictly increasing entries and rows), and the
  generated playfield is verified generically:
  - **Cell lookup** (`LayoutCells`): any cell in a block's row range reads
    back the block's body (`playfield_block_get`), the header rows hold only a
    block's corridor turn and drop, and a block's branch column is pure space
    above it.
  - **Block execution** (`LayoutBlock`): an `inc` block multiplies the stack top by its counter
    digit and exits down its fall-through column; a `decz` block tests the
    remainder at the branch cell and either divides the value and falls
    through (counter positive) or sends the pointer up its corridor column
    (counter zero); a `jump` block sends the pointer up its corridor column;
    `halt` stops the machine. The block theorems accept any arrival direction,
    since the entry `>` forces right.
  - **Routing** (`LayoutRouting`, `LayoutCorridor`): the fall-through drop
    lands the pointer on the next block's entry, and the jump corridor's
    up-turn-drop is proved generically (`corridor_run`), with the drop column
    passing only spaces and exit `v`s.
  - **Simulation** (`LayoutSimulation`): `sim_run` proves a step-for-step
    simulation — for a well-placed program (well-formed targets, `halt` last)
    the playfield run reaches the successor block with the encoding of the
    successor machine state, or stops when the machine stops.
  - **Universality** (`LayoutSimulationNormalize`):
    every two-counter machine is equivalent to a well-placed program (clamp
    the targets, append a `halt`), so `universal_simulation` provides a
    simulating playfield for every machine: its run matches the machine's
    encoded run and it halts whenever the machine does.
  The earlier concrete verifications — the transfer program, a looping program
  with a backward jump, and the branch-free single-row fragment — were the
  stepping stones for this generic development and are now subsumed by it;
  the modern `Tests/Completeness/LayoutSimulation.lean` re-verifies a concrete
  run by computation.
  A readable walkthrough of the whole construction — the machine, the
  encoding, the compilation scheme, the five proof layers, and the capstone
  theorem — is in [`COMPLETENESS.md`](COMPLETENESS.md).
- **Verified example programs** (`LeanFunge.Examples`): kernel-checked
  `HelloWorld`, `Arithmetic`, `Trampoline`, `PutGet`, `Countdown`, `Factorial`,
  `Input`, `DecimalOutput`, `SelfMod`, `Quine`, `Echo`, and `Wrap`.

## Roadmap

The generic simulation of arbitrary two-counter machines on the generated
playfield is complete. The construction — the layout, the cell lookups, the
block executions, the corridor routing, the step-for-step simulation, and the
universality statement — is verified for every program (via normalization):

| Task | Priority | Status |
| :--- | :--- | :--- |
| **Generic `decz` block execution** | High | Proven: the test cells and both branches (decrement down, jump up) on the playfield. |
| **Generic routing** | High | The corridor routing is proven: the up-turn, along-drop, and down segments compose into a single run for arbitrary well-formed jump targets. |
| **Simulation induction** | High | The step-for-step simulation of `CMInstr.run` is proven: each machine step is a playfield run to the successor block with the encoded state, for arbitrary well-placed programs. |
| **Universality statement** | Done | `universal_simulation` provides, for every two-counter machine, a well-placed program whose playfield matches the machine's encoded run and halts whenever the machine does. |

The following items have all been attempted and are confirmed roadblocks, not
untried work.

| Task | Priority | Status |
| :--- | :--- | :--- |
| **String-mode block semantics** | Done | `run_string_block` proves the opening quote, string run, and closing quote push the block's codes and leave string mode (`LeanFunge.Theory.Run.String`). |
| **Run-level output monotonicity** | Done | `run_output_prefix` shows a run only appends to the output; the single-step `step_output_prefix` covers the full instruction set (`LeanFunge.Theory.Run.IO`). |
| **Nop-run pointer movement** | Done | `run_spaces` moves the pointer through a run of spaces via `runPos`, preserving the rest of the state (`LeanFunge.Theory.Completeness.Routing`). |
| **Input consumption is prefix-only** | Done | `parseInt_suffix` shows parsing leaves a suffix; `run_input_prefix` lifts it to a whole run (`LeanFunge.Theory.Parser`, `LeanFunge.Theory.Run.IO`). |
| **String-mode block output round-trip** | Done | `run_print` pops printed codes back into characters, and `run_string_block_print` composes the string block with the print run (`LeanFunge.Theory.Run.String`). |
| **Halting characterization** | Done | `halts_iff_at` characterizes halting as reaching the `@` cell outside string mode, via `step_none_iff_halt` and `decodeChar_halt_iff` (`LeanFunge.Theory.Run.Halt`). |
| **I/O separation** | Done | `step_input_prefix`/`step_output_prefix` separate reading from printing over the 27-instruction case analysis; the run-level versions are `run_input_prefix`/`run_output_prefix` (`LeanFunge.Theory.Run.IO`). |

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
