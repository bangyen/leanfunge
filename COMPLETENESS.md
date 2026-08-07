# Turing-Completeness of Befunge-93 — a Machine-Checked Construction

This document explains, end to end, the result verified in
`LeanFunge.Theory.Completeness`: **every two-counter machine can be compiled to
a Befunge-93 playfield that simulates it step for step.** Everything described
here is checked by the Lean 4 kernel; there are no axioms beyond the standard
ones and no `sorry`s.

The proof is a generic construction. Instead of verifying one program at a
time, it shows that a certain *compilation scheme* works for an arbitrary
program: given any list of two-counter machine instructions, the scheme emits a
playfield, and a family of theorems establishes that running the interpreter on
that playfield reproduces the machine's run — for every input and every
instruction.

## 1. The machine

`TwoCounter.lean` formalizes a Minsky two-counter machine. A program is a list
of instructions

- `inc c` — increment counter `c` (0 or 1) and advance,
- `decz c k` — jump to instruction `k` when counter `c` is zero, otherwise
  decrement it and advance,
- `jump k` — unconditional jump to `k`,
- `halt` — stop.

A state `CMState` is the program counter and the two counters; `step` is a
total function `CMState → Option CMState` (`none` when the machine halts), and
`run` threads `Option`s for `n` steps. `CMInstr.halts prog s₀` means the run
reaches `none` after finitely many steps. This is the standard 2CM formalism
that is known to be universal; that *classical* link is the one piece not
reproven here (see §7).

## 2. The encoding

`PairEncoding.lean` proves the arithmetic that lets one stack value carry both
counters. The value

    encodeState s = 2^c1 · 3^c2

supports exactly the operations the machine needs:

- increment counter 1 / 2: multiply by `2` / `3`,
- decrement counter 1 / 2: divide by `2` / `3`,
- counter 1 is zero iff the value is odd; counter 2 is zero iff the value is
  not divisible by `3`.

Both the `ℕ`-level identities and their `Int`-level counterparts are proven, so
the arithmetic composes cleanly with the interpreter's integer stack.

## 3. The compilation scheme

`Layout.lean` defines the geometry. A program of `n` instructions becomes a
grid made of three parts:

- **Header rows** — one row per instruction block. On row `i`, under the jump
  corridor columns, sit the turn and drop cells (`<`, `v`) that route a jump
  to and from block `i`.
- **Block bodies** — instruction `i`'s cells occupy row range `i` of the body.
  Every block sits in its own rows, so blocks never collide. An `inc c` block
  multiplies the stack top by `c`'s digit and falls through; a `decz c k` block
  tests the remainder at a branch cell and either divides (positive) or turns
  up its corridor (zero); a `jump k` block turns up its corridor; a `halt`
  block stops.
- **Corridors** — for each jump target `k` a dedicated column runs from
  block `i`'s branch cell up to the header, along to `k`'s column, and down
  into block `k`'s entry. Each column is dedicated to one edge, so a jump back
  to block 0 cannot collide with the header's other cells.

`playfieldOf prog` produces the full grid. The entry columns and block rows
strictly increase, which is what makes every cell lookup well-defined.

## 4. The proof, in five layers

**1. Cell lookup (`LayoutCells`).** The playfield readback equals a lookup
over the placed cells; each block's body cells sit in its own row range and its
corridor on its header row. Therefore `playfield_block_get` shows that any cell
within a block's row range reads back exactly that block's body cell — for
arbitrary programs, not just checked ones.

**2. Block execution (`LayoutBlock`, `LayoutDecz`, `LayoutJumpBlock`).** With
the cells in place, each block's run is verified generically:

- an `inc` block multiplies the stack top by its counter digit and exits down
  its fall-through column;
- a `decz` block tests the remainder at the branch cell, divides and falls
  through when the counter is positive, and sends the pointer up its corridor
  column when it is zero;
- a `jump` block sends the pointer up its corridor column;
- a `halt` block stops the run.

**3. Routing (`LayoutRouting`, `LayoutCorridor*`).** The pointer must *get*
from one block to the next. The fall-through case: the bottom-right corner of a
block's body is a space and one step down lands on the next block's entry. The
jump case is the corridor: `run_spaces` (a run of spaces moves the pointer
without touching stack, grid, direction, string mode, output, or input) is
composed by `run_spaces_turn` into the general corridor pattern. The corridor
composition theorem `corridor_run` assembles the up segment, the along row, and
the down segment into a single run from the source block's branch cell to the
target block's entry, for any well-formed jump target. Because the header has
one row per block, every jump edge has a dedicated route.

**4. Simulation (`LayoutSimulation*`).** `wellPlaced` packages the two
properties the construction needs — every jump target is in range, and the last
instruction is a `halt` (so the machine never falls off the end of its own
program). Then `sim_run` is the core induction: for a well-placed program, the
playfield run reaches the successor block carrying the encoding of the
successor machine state, for every machine step:

    sim_run prog hwellPlaced s₀ hs₀ n :
      ∃ m, run m (playfieldStart prog s₀)
         = (CMInstr.run prog n s₀).map (fun s' => afterState prog ... s')

The lemmas `sim_inc`, `sim_decz_zero`, `sim_decz_nonzero`, `sim_jump`, and the
halt case each prove one instruction; the induction composes them with
`run_append`. The corollaries `simulation_map` (the playfield stack after `m`
steps is the encoded machine state after `n`) and `simulation_halts` (if the
machine halts, the playfield halts) make the statement usable.

**5. Universality (`LayoutSimulationNormalize*`, `LayoutSimulationUniversal`).**
`sim_run` requires a *well-placed* program, but an arbitrary program may jump
out of range or lack a trailing `halt`. Normalization fixes both: clamp every
jump target into range and append a `halt`. The normalization theorems show
this changes nothing — `normalize_run_encode` proves the normalized run agrees
with the original run on the encoding, and `normalize_halts_iff` proves it
halts exactly when the original does. Composing normalization with `sim_run`
yields the capstone:

    universal_simulation prog s₀ (hs₀ : s₀.pc < prog.length) :
      ∃ prog',
        wellPlaced prog' ∧
        (CMInstr.halts prog s₀ → halts (playfieldStart prog' s₀)) ∧
        ∀ n : ℕ, ∃ m : ℕ,
          (run m (playfieldStart prog' s₀)).map (fun s => s.stack)
            = (CMInstr.run prog n s₀).map (fun s => [encodeState s])

Read aloud: for every two-counter machine, there is a well-placed Befunge-93
playfield that halts whenever the machine halts, and whose stack after `m`
steps is exactly the encoding of the machine's state after `n` steps — the
playfield *is* the machine.

## 5. Why the geometry works

The subtle parts of Befunge-93 are the toroidal wrap and the self-modifying
grid. The construction sidesteps both by design:

- **No wrapping is ever relied on.** Every corridor route stays inside its
  dedicated rows and columns; `run_spaces` moves the pointer through spaces and
  stops at the next non-space.
- **Nothing is self-modified.** The compiled playfield is written once and only
  read; the block and corridor runs never execute a `p` or `g`.
- **Direction is threaded explicitly.** Every routing lemma carries the
  pointer's direction forward, and the block-entry `>` forces the run to
  proceed rightward, so the corridor composition always meets the next block
  facing the right way.

## 6. Navigating the code

| Module | Content |
| :--- | :--- |
| `TwoCounter` | the machine: instructions, `step`, `run`, `halts` |
| `PairEncoding` | the `2^c1 · 3^c2` counter arithmetic |
| `Routing` | `run_spaces`, `run_spaces_turn`: corridor primitives |
| `Layout` | block geometry, `playfieldOf` |
| `LayoutCells`, `LayoutCellRange`, `LayoutCellMain` | playfield readback = placed-cell lookup |
| `LayoutBlock`, `LayoutDecz`, `LayoutDeczBranch`, `LayoutJumpBlock` | generic block executions |
| `LayoutRouting`, `LayoutRowAt`, `LayoutHeader(Row)`, `LayoutCorridor*`, `LayoutCorridorRoute` | fall-through and jump routing |
| `LayoutSimulation` | state encoding, `wellFormed`, `wellPlaced`, `playfieldStart` |
| `LayoutSimulationBlock`, `LayoutSimulationStep`, `LayoutSimulationStepRun`, `LayoutSimulationDecz`, `LayoutSimulationRun` | `sim_step`, `sim_run`, `simulation_map`, `simulation_halts` |
| `LayoutSimulationNormalize*`, `LayoutSimulationUniversal` | normalization and `universal_simulation` |

`Tests/Completeness/LayoutCorridorRoute.lean` and
`Tests/Completeness/LayoutSimulation.lean` pin the construction down with
concrete examples, including a `decide`-verified transfer-program run.

## 7. Scope

What is *not* claimed:

- **The classical universality of two-counter machines.** That 2CMs can
  simulate Turing machines is a classical result not present in mathlib. This
  development stops at the (machine-checked) simulation of 2CMs on Befunge-93
  playfields; the last step to full Turing-completeness is a library of
  classical computability theory, not a Lean gap here.
- **The surrounding language tracks.** String-mode block semantics, output
  monotonicity, and input consumption are separate ongoing efforts (see the
  README roadmap); the completeness construction uses none of them.

Everything the construction claims — the cell lookups, the block executions,
the corridor routing, the step-for-step simulation, and the universality
statement — is verified by the Lean kernel for arbitrary programs.
