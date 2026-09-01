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
  `Theory.Termination`): only `p` writes the playfield, the playfield at any
  step is the initial playfield plus the run's accumulated `p` writes (so a
  cell never written keeps its value), ranked machines terminate, and
  all-space runs never halt.
- **Memory model of the examples** (`Theory.Memory`): a program whose
  playfield holds no `p` cannot modify itself at any number of steps — proved
  for the quine — and the self-modifying programs' playfields are pinned down
  in full as the initial playfield plus their single write.
- **Turing completeness** (`Theory.Completeness`): a verified construction
  compiling an arbitrary two-counter machine into a Befunge playfield that
  simulates it step for step. The Minsky machine semantics, the `2^c1 * 3^c2`
  counter-pair encoding, and a `playfieldOf` generator laying each instruction
  as a block with its own jump corridor are formalized and proved well formed;
  `universal_simulation` then gives *every* machine a playfield whose run
  matches the machine's encoded run and which halts exactly when it does. The
  construction, its five proof layers, and the capstone theorem are walked
  through in [`COMPLETENESS.md`](COMPLETENESS.md).
- **Undecidability** (`Theory.Completeness.Undecidable`): Befunge-93 halting is
  undecidable, conditional on the classical undecidability of two-counter
  halting — `befunge_undecidable_of_twoCounter`. The statement is phrased over
  program *text*, since `Grid` holds a function and so no state-based domain is
  `Primcodable`, and the reduction runs through a `Computable` compiler. The
  one external input is 2CM universality itself, which mathlib does not
  contain; see [`UNDECIDABILITY.md`](UNDECIDABILITY.md).
- **Verified example programs** (`LeanFunge.Examples`): kernel-checked
  `HelloWorld`, `Arithmetic`, `Trampoline`, `PutGet`, `Countdown`, `Factorial`,
  `Input`, `DecimalOutput`, `SelfMod`, `Quine`, `Echo`, `Wrap`, and the
  nondeterministic `Random`.

## Scope & Limitations

**Scope.** LeanFunge has two halves.

The first is the language itself: Befunge-93's semantics and properties of
them — stack algebra, toroidal wrapping, the self-modifying playfield, string
mode, and the single-step semantics of the instruction set — together with
verified example programs.

The second is a *construction* rather than a property, and is now the larger
half by volume: `Theory.Completeness` compiles an arbitrary two-counter
machine into a Befunge playfield that simulates it step for step
(`universal_simulation`), and on top of that reduces two-counter halting to
Befunge halting (`befunge_undecidable_of_twoCounter`). This reaches outside
Befunge — the counter machines, their encoding, and the computability
plumbing are not facts about the language — but it is what makes the
Turing-completeness and undecidability claims machine-checked rather than
asserted. See [`COMPLETENESS.md`](COMPLETENESS.md) and
[`UNDECIDABILITY.md`](UNDECIDABILITY.md).

Out of scope: verified program transformations or optimizations (spacing,
rotation, dead no-op elimination, constant folding); the program-equivalence
framework that supported them was removed. A Befunge-98 fingerprint and
self-interpreters (programs that interpret Befunge, verified to match direct
execution) are also out, as their correctness proofs are program-equivalence
reasoning rather than properties of the language. The classical universality
of two-counter machines stays external too — it belongs upstream in mathlib,
not here.

**Design choices.** Befunge's specification leaves several behaviors
unspecified; LeanFunge makes the following choices, all documented in
`ARCHITECTURE.md`:

- **Toroidal playfield**: coordinates are reduced modulo the playfield size on
  every access, so the playfield is a torus. The pointer is likewise reduced on
  every move, so it never leaves the grid.
- **Stack underflow**: popping an empty stack yields `0`, and a binary
  operation on a short stack fills its missing operands with `0`.
- **Division by zero**: `/` by zero pushes `0`, while `%` by zero pushes the
  dividend unchanged, inheriting Lean's `Int` conventions.
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
- Every verified example *except* `Random` is deterministic; the
  nondeterminism of `?` is captured by the transition relation rather than the
  executable interpreter. `Random` is verified against that relation, halting
  along every direction the `?` may choose and, conversely, along every
  relational run there is (`coin_halts_only`). The direction-independent
  run-level laws are lifted to the relation in `Theory.Run.Nondeterminism`;
  the write trace and the straight-line divergence are direction- or
  path-dependent and hold for `run` only.
- The completeness development (`Theory.Completeness`) is complete for
  Befunge-93's side: `universal_simulation` gives *every* two-counter machine
  a playfield that simulates it. What it does not claim is the classical
  result that two-counter machines are themselves Turing complete, which
  mathlib does not contain; that last step is a library of classical
  computability theory rather than a gap in this development. The
  construction does not require changing the fixed-grid semantics: unbounded
  memory comes from the unbounded stack, and the finite playfield supplies
  only finite control.

## Installation & Building

Make sure you have [elan](https://github.com/leanprover/elan) installed for
Lean 4 version management.

```bash
git clone --recurse-submodules https://github.com/bangyen/leanfunge.git
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

This repo uses standard Mathlib naming conventions and the shared guard scripts
from [lean-guards](https://github.com/bangyen/lean-guards), vendored as a
submodule at `scripts/`. If you are interested in extending the formalization —
for example, another verified example program — feel free to open a pull
request.

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
