# Undecidability of Befunge-93 Halting

The last open row in the [README](README.md) roadmap was **halting problem
undecidability**. It was recorded as blocked on an external result; in fact only
a small part of it was, and that part is now isolated behind a single named
hypothesis.

**What is proven** (`Theory.Completeness.Undecidable`, `sorry`-free, standard
axioms only):

```lean
theorem befunge_undecidable_of_twoCounter
    (h2cm : ¬ ComputablePred
      (fun prog : CMProgram => CMInstr.halts prog (CMInstr.startCM 0 0))) :
    ¬ ComputablePred (fun p : ℕ × ℕ × List (List Char) =>
        halts (State.init (Grid.ofRows p.1 p.2.1 p.2.2)))
```

**What stays external:** `h2cm` itself — the classical undecidability of
two-counter machine halting. Mathlib has no counter-machine model at all, so
this is not a citation but a project: a reduction from `Turing.ToPartrec.Code`
to 2CMs, which is Minsky's theorem (§2.E).

This document records the plan that got there, and why each piece took the shape
it did.

## 1. The obstacle that shapes everything: `Grid` is a function

`ComputablePred p` requires `p`'s domain to be `Primcodable` — encodable as a
natural number. So "Befunge halting is undecidable" has to be stated over
something encodable, and the current state type is not:

```lean
structure Grid (w h : ℕ) where
  cells : ℕ → ℕ → Char        -- LeanFunge/Core/Grid.lean:26
```

`Grid` is a **function type**, and `State w h` contains one. No `Primcodable`
instance can exist for `Σ w h, State w h` as it stands — this is not a matter
of nobody having written the instance, it is not encodable. So the obvious
statement form is dead on arrival, and the choice of target statement is
decision #1, before any other work.

### The viable form: state it over the source text

State undecidability over the *program text*, where `String`/`List (List Char)`
is already `Primcodable`:

```lean
theorem befunge_halting_undecidable :
    ¬ ComputablePred (fun p : List (List Char) × List Char =>
        halts (State.init (Grid.ofRows (width p.1) (height p.1) p.1)
                 |>.withInput p.2))
```

This is also the more natural language-level theorem — "the halting of
Befunge-93 programs, given as text, is undecidable" — and it dodges the
dependent-type encoding entirely.

**What makes this workable:** `playfieldOf` is already built from a *finite*
cell list, not an arbitrary function:

```lean
def playfieldOf (prog : CMProgram) : Grid ... :=
  ((List.range prog.length).foldl
    (fun g i => (blockCellList prog i).foldl
      (fun g cell => Grid.put g cell.1.1 cell.1.2 cell.2) g))
    (Grid.space ...)                          -- Layout.lean:202
```

Every cell it ever writes comes from `blockCellList` (`Layout.lean:189`), a
plain `List ((ℕ × ℕ) × Char)`. So a rows-based twin `playfieldRowsOf : CMProgram
→ List (List Char)` is straightforwardly definable, and

    Grid.ofRows w h (playfieldRowsOf prog) = playfieldOf prog

is a provable bridge lemma. That lemma is the linchpin of the whole plan: it
carries the existing `universal_simulation` result over to the encodable
statement form without redoing any of the simulation proof.

## 2. Work breakdown

| # | Piece | Blocker | Size |
| :-- | :--- | :--- | :--- |
| A | `Primcodable` for `CMInstr`, `CMProgram`, `CMState` | none | **done** |
| A′ | `Primcodable Char` | none | **done** |
| B | `playfieldRowsOf` + the `ofRows` bridge lemma | none | **done** |
| B′ | Bootstrap from `State.init` to the block-0 entry | none | **done** |
| C | `Computable` proof for the compiler | none | **done** |
| D | Conditional undecidability theorem | none | **done** |
| E | 2CM universality | **external** | separate project |

### A. `Primcodable` instances — small, mechanical

`CMInstr` is a 4-constructor inductive over `Fin 2` and `ℕ`; `CMProgram` is a
`List`; `CMState` is a 3-field `ℕ` structure. There is no `deriving` handler for
`Primcodable`, so each needs an explicit `Equiv` fed through
`Primcodable.ofEquiv` — for instance
`CMInstr ≃ Fin 2 ⊕ (Fin 2 × ℕ) ⊕ ℕ ⊕ Unit` and `CMState ≃ ℕ × ℕ × ℕ`. The
`ofEquiv`/`prod`/`sum`/`fin`/`option` instances in
`Mathlib/Computability/Primrec/Basic.lean` cover all of it, and `CMProgram` then
comes free from the `List` instance. No research content.

**Status: done.** `Theory/Completeness/Encodable.lean` carries
`CMInstr.equivSum`, `CMState.equivProd`, and the two `ofEquiv` instances;
`Primcodable CMProgram` follows from the `List` instance. The `h2cm` hypothesis
shape of §2.B′ typechecks against them.

**`Char` (piece A′): done.** Mathlib has no `Primcodable` — nor even
`Encodable` — instance for `Char`, and `Primcodable.ofEquiv` is the only builder,
requiring a genuine `Equiv`. The obvious `Char.toNat`/`Char.ofNat` pairing does
*not* give one: `ofNat` clamps invalid code points to `'\0'`, so it is not
injective on `ℕ`.

The route that works goes through the subtype, and turned out to be short:

```lean
def charEquivSubtype : Char ≃ { n : ℕ // n.isValidChar } where
  toFun c := ⟨c.toNat, c.valid⟩
  invFun n := Char.ofNatAux n.1 n.2
  left_inv _ := Char.ext rfl
  right_inv _ := Subtype.ext rfl
```

`Char.ofNatAux` is the un-clamped constructor, taking the validity proof the
subtype already carries, which is what makes both inverse directions `rfl`.
The predicate side is easier than the `UInt32` framing suggested: `isValidChar`
unfolds to `n < 0xd800 ∨ (0xdfff < n ∧ n < 0x110000)`, so `PrimrecPred.or`,
`PrimrecPred.and`, and `Primrec.nat_lt` discharge it directly — no `UInt32`
reasoning at all. Note `Primcodable.subtype` is a `def`, not an instance, so it
must be supplied with `letI`.

With this, `Primcodable (List (List Char))` and the full
`ℕ × ℕ × List (List Char)` statement domain both resolve.

**Encoding choice affects C.** Pick the `Equiv` so encode/decode stay easy to
prove `Primrec`. A nested-sum `ofEquiv` is the natural first cut, but a flat
`Nat.pair`-based encoding is sometimes easier to drive through the `Primrec`
lemmas. Not worth over-engineering up front — but if C stalls, this is the first
thing to revisit.

### B. Rows-based playfield — done

`Theory/Completeness/LayoutRows.lean` defines `playfieldRowsOf` and proves

```lean
theorem ofRows_playfieldRowsOf (prog : CMProgram) (hne : prog ≠ []) :
    Grid.ofRows (playfieldWidth prog) (playfieldHeight prog) (playfieldRowsOf prog)
      = playfieldOf prog
```

Three things worth recording about how it landed:

**Aim for grid equality, not `get`-agreement.** `Grid` is a one-field structure,
so this is provable by `funext` on `cells`, and the simulation theorems then
transport by plain `rw`. Settling for `∀ x y, get = get` would have required
run-level congruence lemmas — a bisimulation layer that would dwarf B itself.
Verified: the bridge rewrites a `halts (State.init (Grid.ofRows ...))` statement
into `halts (playfieldStart ...)` in two lines.

**The nonemptiness hypothesis is load-bearing.** `Grid.get` reduces coordinates
modulo the size, but `Grid.ofRows` indexes `cells` at *raw* coordinates, so the
two agree only when the rows list covers the full extent — and for `w = 0` or
`h = 0`, `n % 0 = n` breaks the guard comparison. It cannot bite in practice
(an empty program places no cells), but rather than case-split on it the lemma
takes `prog ≠ []` and derives `playfieldWidth_pos` / `playfieldHeight_pos` from
the existing `entryColumn_strict_mono` and `blockRow_ge_length`.

**A `cells`-level twin of `foldl_put_get` was needed.** The existing
`LayoutCells` machinery characterizes `.get`; the `funext` works on `.cells` at
raw coordinates. `foldl_put_cells` and `foldl_put_cells_out` supply the in-range
and out-of-range halves, and `playfieldOf_cells` / `playfieldOf_cells_out` lift
them to the playfield.

**Statement-domain decision (affects C and D).** `playfieldRowsOf` supplies the
rows, but the width and height are *separate* outputs of the construction, and
`Grid.ofRows` takes them as explicit arguments. Rather than have D re-derive
dimensions from the rows list (with its ragged-row and empty-list edge cases),
the predicate domain should be the triple `ℕ × ℕ × List (List Char)`:

```lean
fun p : ℕ × ℕ × List (List Char) => halts (State.init (Grid.ofRows p.1 p.2.1 p.2.2))
```

This is `Primcodable` given A′, needs no dimension derivation, and the compiler
of C emits the triple directly. `playfieldRowsOf_length` and
`playfieldRowsOf_row_length` pin the dimensions for anyone who does want them.
**C's compiler target and D's statement must name this same domain.**

### B′. The bootstrap — done

`boot_run` (`Theory/Completeness/LayoutBoot.lean`) closes the gap between
`State.init` and `playfieldStart`:

```lean
theorem boot_run (prog : CMProgram) (hne : prog ≠ []) (hwp : wellPlaced prog) :
    run (prog.length + 1) (State.init (playfieldOf prog))
      = some (playfieldStart prog (CMInstr.startCM 0 0))

theorem boot_halts_iff (prog : CMProgram) (hne : prog ≠ []) (hwp : wellPlaced prog) :
    halts (State.init (playfieldOf prog))
      ↔ CMInstr.halts prog (CMInstr.startCM 0 0)
```

`State.init` begins at the origin, facing right, with an **empty stack**;
`playfieldStart` begins at a block entry, facing down, carrying the encoded
state. Nothing connected them, so a decider for the former said nothing about
the proven results.

**A wrapper grid does not work.** The tempting move — define the boot playfield
as `(playfieldOf prog).put ...` and leave the layout alone — is a dead end.
`sim_run` and `simulation_halts_iff` hard-code `playfieldOf prog` as their grid,
and no read-framing lemma exists to transport them. So the prelude had to become
part of the layout.

**The design.** `entryColumn` is re-based so block 0 sits at column 1, leaving
column 0 free across every row. The prelude is two cells on row 0: `1` at
`(0,0)` (push one, move right) and `v` at `(1,0)` (turn down). The pointer then
descends column 1 — the same shared descent every corridor into block 0 already
uses — arriving at `(1, prog.length)` facing down with stack `[1]`, which *is*
`playfieldStart prog (startCM 0 0)` since `encodeState (startCM 0 0) = 1`. The
run takes `prog.length + 1` steps.

**The re-base cost almost nothing.** The simulation tower is coordinate-generic
and rebuilt untouched; only concrete coordinate pins moved, all by the same
uniform shift, since `blockRow` is unchanged and only `entryColumn`-derived
x-coordinates shift. This corrects the earlier sizing here, which called B′
"larger than C" — that was wrong on the evidence.

**The cell layer was where the real work was.** Three things:

1. `playfieldCells` carries the prelude as a prefix, so block-row lookups peel
   it off (`lastCellAt_skip_boot`) — sound because the prelude is on row 0 and
   every block row is at or below `prog.length`.
2. `playfield_header_get` characterized *every* column of every header row, which
   the prelude falsifies at columns 0 and 1. It gains a `y = 0 → 2 ≤ x` guard.
   The guard has to be exactly that shape: a column-wide exclusion would break
   `corridorDown_cell` for `k = 0`, which legitimately reads column 1 at every
   row `≥ 1` during the descent.
3. Callers that legitimately touch the excluded positions go through two new
   lemmas instead. `playfield_boot_turn` is unconditional — any corridor drop
   landing on the turn's position is also a `v`, so the reading holds whichever
   write wins.

**`playfield_boot_push` needs `wellPlaced`, not `wellFormed`.** A block's exit
`v` deliberately sits in its *successor's* entry column. For the last block that
column equals `playfieldWidth`, and `Grid.put` reduces coordinates modulo the
width — so on a program without a trailing `halt` the exit cell wraps onto
column 0 and clobbers the push. `wellPlaced`'s trailing-halt requirement is
exactly what rules this out, and `wellPlaced_normalize` supplies it downstream.

**Gate checks that made this tractable** (all run before writing the geometry):
`corridorDown_cell` already proved the descent column reads `' '` *or* `'v'`, so
shared descents were handled; only one proof depended on `entryColumn prog 0 = 0`
by `rfl`; and `halts_iff_of_run` (`Theory/Run/Halt.lean`) supplies the
`run k s = some s' → (halts s ↔ halts s')` transport that turns the boot run into
the iff.

### C. `Computable` for the compiler — done

`Theory/Completeness/PrimrecLayout.lean` proves everything at the `Primrec`
level and converts once at the end with `Primrec.to_comp`; the `Primrec`
combinator library is far richer than the `Computable` one.

The layers, bottom-up:

- **Instruction accessors.** `blockCellList` matches on the instruction and uses
  its payload. Splitting the match into `Bool` tests (`isInc`, `isDecz`,
  `isJump`) and total accessors (`target`, `counter`) lets the proof dispatch
  with `ite` and hand each branch its payload. Functions *out of* `CMInstr`
  transport along `CMInstr.equivSum` — that is how the `Primcodable` instance is
  built — and `Primrec.sumCasesOn` handles the constructors.
- **Geometry.** Through the `entryColumn_foldl` / `blockRow_foldl` closed forms,
  since a `Primrec` argument cannot follow the index recursion. `list_foldl` and
  `list_range` exist; `list_take` and `list_sum` do not, which is why the closed
  forms are folds rather than sums over prefixes.
- **Cell lists.** Each branch a literal list of positioned characters; the
  `decz` branch's nine cells plus its corridor are the tedious spot.
- **`lastCellAt`.** Already a `foldl` with a positional `ite` on ℕ mod-equalities
   — a direct fit. No `Char` reasoning in the condition; characters appear only
  as constants, which A′ covers.
- **Assembly.** `playfieldCells` (append then flatMap over a range), then
  `playfieldRowsOf` (nested map over the row and column ranges).
- **Normalization.** `clampInstr` rebuilds instructions, so the constructors go
  through the equiv's *inverse* (`Primrec.of_equiv_symm`).

**The one mechanical lesson:** state every fact uncurried over its product, with
`list_foldl`'s implicit types given explicitly. The curried `Primrec₂` form
leaves the accumulator type a metavariable and instance resolution gets stuck
with `Primcodable ?m` — which is the error you get, not a hint about the real
problem.

### D. The conditional theorem — done

```lean
theorem befunge_undecidable_of_twoCounter
    (h2cm : ¬ ComputablePred
      (fun prog : CMProgram => CMInstr.halts prog (CMInstr.startCM 0 0))) :
    ¬ ComputablePred (fun p : ℕ × ℕ × List (List Char) =>
        halts (State.init (Grid.ofRows p.1 p.2.1 p.2.2)))
```

in `Theory/Completeness/Undecidable.lean`. A decider for Befunge halting,
composed with the compiler, would decide two-counter halting.

`compile_halts_iff` carries the content and chains the three bridges:
`ofRows_playfieldRowsOf` (B) moves from text to the generated playfield,
`boot_halts_iff` (B′) starts the run from `State.init`, and
`normalize_halts_iff` drops the well-placedness. Normalizing *inside* the
compiler makes it total, and since `normalize` always appends a `halt` its
result is never empty — so `hne` and `wellPlaced` both discharge by
construction and the hypothesis ranges over **all** programs, with no
empty-program carve-out.

The whole development is `sorry`-free and uses only the three standard axioms.

### E. 2CM universality — genuinely external

This is the only real gap, and it is Minsky's theorem. Mathlib has **no**
counter-machine model at all (confirmed: nothing matching counter/Minsky/register
machine anywhere in `Mathlib/Computability/`), so this cannot be a citation — it
has to be built.

**The narrowest formulation of the gap** is not "partrec or TM2" but a reduction
from `Turing.ToPartrec.Code`:

```lean
inductive Code
  | zero' | succ | tail
  | cons : Code → Code → Code
  | comp : Code → Code → Code
  | case : Code → Code → Code
  | fix  : Code → Code           -- Mathlib/Computability/TMConfig.lean:76
```

Note this lives in `TMConfig.lean`, not `TMToPartrec.lean`. It is a 7-constructor
list machine with `fix` — far closer to a counter machine than raw partrec codes
or TM2 tapes — and `exists_code` (`TMConfig.lean:266`) gives every partrec
function such a code. So `ToPartrec.Code → 2CM` is the tightest statement of
what is missing.

Sizing it honestly: simulating a list machine in two counters means a Gödel-style
exponent encoding of the stack plus a correctness proof for every constructor
including `fix`. That is a mathlib-contribution-scale project, plausibly
thousands of lines. It belongs in the roadmap as its own project, not as a task
row inside this one.

## 3. Where this leaves the row

A–D are done. The roadmap row moves from "blocked on an external result" to
"the reduction is proven; the sole remaining input is `h2cm`, classical Minsky,
external to this development."

That boundary is now precise and machine-checked rather than prose in a README —
the same shape mathlib itself uses for results whose last ingredient is
unformalized. If E ever arrives, here or upstream, discharging `h2cm` turns the
conditional theorem into the unconditional one with no further work.

**Two sizing calls in the original plan were wrong**, both recorded above where
they bit: B′ was called "larger than C" on the assumption that re-basing the
layout would force the `LayoutCells` tower to re-verify — the tower is
coordinate-generic and rebuilt untouched, and the real work turned out to be the
cell layer's row-0 collisions. And `Primcodable Char` was twice called small
before the `UInt32` framing turned out to be a red herring.
