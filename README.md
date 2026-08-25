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
    encoded run and it halts exactly when the machine does.
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
  `Input`, `DecimalOutput`, `SelfMod`, `Quine`, `Echo`, `Wrap`, and the
  nondeterministic `Random`.

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
| **Universality statement** | Done | `universal_simulation` provides, for every two-counter machine, a well-placed program whose playfield matches the machine's encoded run and halts *exactly when* the machine does. |

The remaining language tracks are complete: the string-mode block semantics
(`run_string_block`), the run-level output monotonicity (`run_output_prefix`),
the nop-run pointer movement (`run_spaces`), the prefix-only input consumption
(`parseInt_suffix`, `run_input_prefix`), the string-mode output round-trip
(`run_print`, `run_string_block_print`), the halting characterization
(`halts_iff_at`), the output determinism (`halt_unique`), the run-level memory
model (`run_grid_writes`), the string-mode precedence (`step_string_mode`), the
straight-line divergence (`not_halts_safe_line`), the quote balance
(`run_stringMode_parity`), and the I/O separation
(`step_input_prefix`/`step_output_prefix`,
`run_input_prefix`/`run_output_prefix`) are all proven.

### Open work

The language-property program is complete — every row in the table that
follows this one is proven, as is the halting equivalence that closes the
completeness capstone and the lift of the run-level laws to the
nondeterministic semantics. What remains is one external blocker.

| Task | Priority | Status |
| :--- | :--- | :--- |
| **Halting problem undecidability** | High | Blocked on one missing bridge, not a missing foundation. Mathlib *does* have a formal notion of decidability and the undecidability of the halting problem (`ComputablePred`, `ComputablePred.halting_problem` in `Mathlib.Computability.Halting`); what it lacks is any counter-machine model, so the gap is a reduction from a mathlib computability model (partrec or TM2) to two-counter machines, plus `Primcodable` encodings and a `Computable` proof for the machine-to-playfield compiler. The correspondence itself is no longer the gap — `simulation_halts_iff` proves the playfield halts *exactly when* the machine does. |

### Completed language properties

Properties of the language proven since the completeness construction landed,
ranked by value and feasibility.

| Task | Priority | Status |
| :--- | :--- | :--- |
| **Relational lifts of the run-level laws** | Medium | Done, for the laws that lift. `Theory.Run.Nondeterminism` carries string-mode precedence, quote parity, and the I/O prefixes to `runRel` off `stepRel_fields` (a `?` redirect changes only the direction and the pointer). Two laws do *not* lift and the module says why: the write trace of `run_grid_writes` is path-dependent, and `not_halts_safe_line` is a statement about travel in a fixed direction, which a `?` on the line breaks. |
| **`decodeChar` nop characterization** | Low | Done. `decodeChar_nop_iff` shows a character decodes to `nop` exactly when it is outside `instrChars`, the 37-character instruction table. |
| **Pointer-in-range invariant** | Low | Done. Every pointer update goes through `stepPos`, which reduces modulo the playfield size (`stepPos_lt`), so no step leaves the pointer out of range (`step_pc_lt`, `run_pc_lt`). An out-of-range pointer would be harmless anyway, since `Grid.get` wraps its coordinates (`get_eq_get_mod`). |
| **Halting converse for the simulation** | High | Done. `simulation_halts_converse` proves the generated playfield halts only if the machine does, so `simulation_halts_iff` makes the pair an equivalence and `universal_simulation` now states it. The converse needed `sim_step` to expose that each simulated step takes at least one playfield step, and `sim_run` to carry the resulting growth bound; the positivity was already implicit in the block step counts. |
| **Run-level `p`/`g` memory model** | High | Done. `run_grid_writes` shows the playfield at any step is the initial playfield with the run's accumulated `p` writes applied in order, and `run_cell_invariant` shows a cell never written keeps its value. `Theory.Memory` lifts the examples: `quine_grid_invariant` proves the quine never modifies itself at *any* number of steps, and `selfmod_grid`/`exec_grid` pin the whole playfield of the self-modifying programs. |
| **Output determinism** | Medium | Done. `halt_unique` shows a run reaches at most one halting configuration, at one step count; `halts_unique_final` packages it as a unique final state and `halt_output_unique` as a unique output, so for a fixed program and input the output is determined. |
| **`#` trampoline wrapping in all four directions** | Medium | Done. `step_trampoline_left_from_first`, `step_trampoline_down_from_last`, and `step_trampoline_up_from_first` join `step_trampoline_right_from_last`, covering the skip across the wrap at all four edges. |
| **Straight-line divergence without `@`** | Medium | Done. `not_halts_safe_line` proves any run along a line of safe cells diverges, in all four directions, generalizing `run_space_some` off all-space playfields. A safe cell also excludes `p` (a write could place an `@` further along the line) and `"` (it would leave the instruction set behind). |
| **Stack underflow semantics** | Low | Done. `pop_nil`, `top_nil`, `drop_nil`, `dup_nil`, `swap_nil`, `swap_singleton`, `applyBinary_nil`, and `applyBinary_singleton` pin down every accessor on an empty or one-element stack. On a singleton the missing operand is the *second-popped* one, so `-` on `[5]` computes `0 - 5 = -5`. |
| **Division and modulo by zero** | Low | Done, and the conventions are *not* symmetric: `step_div_zero` shows `/` by zero pushes `0`, but `step_mod_zero` shows `%` by zero pushes the dividend unchanged (Lean's `Int` has `b % 0 = b`). Befunge-93 leaves both undefined. |
| **String-mode precedence** | Medium | Done. `step_string_mode` shows a string-mode step never halts, writes the grid, consumes input, produces output, or turns; `run_string_mode` lifts it to any run that stays in string mode. The "string mode is data, not code" property. |
| **Quote balance** | Medium | Done. `run_stringMode_parity` shows string mode after a run is the initial mode toggled once per executed `"`, and `run_stringMode_even` gives the even-count form. The count is over cells the pointer *executes*, not cells it crosses: `#` skips a cell without executing it, so a quote skipped that way is correctly never counted. |

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
  along every direction the `?` may choose. The direction-independent
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
