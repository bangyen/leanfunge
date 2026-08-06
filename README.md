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
  the zero tests are `% 2`/`% 3`), and a concrete playfield that simulates a
  small two-counter machine step-for-step with the counters carried in the
  single encoded stack value — the seed of a full universality proof that
  stays within the fixed-grid Befunge-93 semantics.
- **Verified example programs** (`LeanFunge.Examples`): kernel-checked
  `HelloWorld`, `Arithmetic`, `Trampoline`, `PutGet`, `Countdown`, `Factorial`,
  `Input`, `DecimalOutput`, `SelfMod`, `Quine`, `Echo`, and `Wrap`.

## Roadmap

All items below have been attempted and are confirmed roadblocks, not untried
work.

| Task | Priority | Status |
| :--- | :--- | :--- |
| **Generic 2CM simulation** | High | Needs a geometric routing lemma carrying the instruction pointer between instruction blocks for arbitrary jump targets in a fixed toroidal playfield. |
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
  two-counter machine semantics, the pair encoding, and one concrete simulated
  program end-to-end. The fully generic theorem — that *every* two-counter
  machine has a playfield that simulates it — is not yet proven; it needs the
  geometric routing lemma listed in the Roadmap. It does not require changing
  the fixed-grid semantics: unbounded memory comes from the unbounded stack,
  and the finite playfield supplies only finite control.

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
