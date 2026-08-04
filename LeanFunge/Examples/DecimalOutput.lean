/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanFunge.Core.Semantics

/-!
# Decimal Output

A "library" program that reads a non-negative decimal integer with `&` and
prints its digits back as characters with `,` — the dual of the `&` parser.
An extraction loop divides by 10 (`55+/`) and stores the remainders in cells
of column 0, and a print loop fetches them in reverse order, adding 48 to
print each digit. The printed output, when re-parsed by `&` (`parseInt`),
reconstructs the original number, so the routine round-trips with the parser.

The playfield is 48 wide and 10 tall. `(0, 0)` holds the running value and
`(1, 0)` the digit count; digits are stored at `(0, 2), (0, 3), ...`:
- Row 0: init (`& 00p 010p`), the extraction check `|` at `(8, 0)`, and the
  extraction re-entry `<` at `(46, 0)`.
- Row 1: the extraction body, which stores a digit, stores the quotient, and
  increments the count. Its `v` at `(44, 1)` routes to row 2.
- Row 2: `@` at `(12, 2)` (print halt) and the extraction routing `>`, `^`.
- Row 3: the print check `|` at `(12, 3)` and its re-entry `<` at `(40, 3)`.
- Row 4: the print body; `(8, 4)` and `(12, 4)` are `>` redirects.
- Rows 5-9: the print routing `^` and the print setup `1 0 g 1 +` stored
  upward in column 8.

The extraction loop continues while the quotient is non-zero; when it reaches
zero the check `|` exits up to the print setup, which pushes `i + 1` (the
first print row) and flows right into the print body.

## Main definitions

* `spaces`: A helper producing `n` spaces for padding rows to the width.
* `decimalRows`, `decimalGrid`, `decimalState`: The program and its initial
  state reading `123`.
* `decimal5State`: The same program reading `12345`.
* `singleState`: The same program reading `5`.
* `zeroState`: The same program reading `0`.

## Theorems

* `decimal_output`: Reading `123` prints `123`.
* `decimal_halts`: The `123` run halts after 439 steps.
* `decimal5_output`: Reading `12345` prints `12345`.
* `decimal5_halts`: The `12345` run halts after 719 steps.
* `single_output`: Reading `5` prints `5`.
* `single_halts`: The `5` run halts after 159 steps.
* `zero_output`: Reading `0` prints `0`.
* `zero_halts`: The `0` run halts after 159 steps.
* `decimal_roundtrip`: Re-parsing each printed output with `parseInt`
  reconstructs the original number.
-/

namespace LeanFunge.Examples

/-- A helper producing `n` spaces, used to pad rows to the playfield width. -/
def spaces (n : Nat) : String := String.ofList (List.replicate n ' ')

/-- The ten rows of the decimal output program, each 48 cells wide. -/
def decimalRows : List (List Char) :=
  [String.toList ("&00p010p|" ++ spaces 37 ++ "< "),
   String.toList (spaces 8 ++ ">00g:55+%10g2+0\\p55+/00p10g1+10p00g!v" ++ spaces 3),
   String.toList (spaces 12 ++ "@" ++ spaces 31 ++ "> ^ "),
   String.toList (spaces 12 ++ "|" ++ spaces 27 ++ "<" ++ spaces 7),
   String.toList (spaces 8 ++ ">" ++ spaces 3 ++ ">:0\\g58*8++,1-:1-!v" ++ spaces 17),
   String.toList (spaces 8 ++ "+" ++ spaces 21 ++ ">" ++ spaces 9 ++ "^" ++ spaces 7),
   String.toList (spaces 8 ++ "1" ++ spaces 39),
   String.toList (spaces 8 ++ "g" ++ spaces 39),
   String.toList (spaces 8 ++ "0" ++ spaces 39),
   String.toList (spaces 8 ++ "1" ++ spaces 39)]

/-- The playfield of the decimal output program. -/
def decimalGrid : Grid 48 10 := Grid.ofRows 48 10 decimalRows

/-- The initial state, reading `123`. -/
def decimalState : State 48 10 := { (State.init decimalGrid) with input := String.toList "123" }

/-- The initial state, reading `12345`. -/
def decimal5State : State 48 10 := { (State.init decimalGrid) with input := String.toList "12345" }

/-- The initial state, reading a single digit `5`. -/
def singleState : State 48 10 := { (State.init decimalGrid) with input := String.toList "5" }

/-- The initial state, reading `0`. -/
def zeroState : State 48 10 := { (State.init decimalGrid) with input := String.toList "0" }

/-- Reading `123` prints `123`. -/
theorem decimal_output :
    (run 400 decimalState).map (fun s => s.output) = some "123" := by
  decide

/-- The `123` run halts after 439 steps. -/
theorem decimal_halts : run 439 decimalState = none := by
  decide

/-- Reading `12345` prints `12345`. -/
theorem decimal5_output :
    (run 700 decimal5State).map (fun s => s.output) = some "12345" := by
  decide

/-- The `12345` run halts after 719 steps. -/
theorem decimal5_halts : run 719 decimal5State = none := by
  decide

/-- Reading `5` prints `5`. -/
theorem single_output :
    (run 150 singleState).map (fun s => s.output) = some "5" := by
  decide

/-- The `5` run halts after 159 steps. -/
theorem single_halts : run 159 singleState = none := by
  decide

/-- Reading `0` prints `0`. -/
theorem zero_output :
    (run 150 zeroState).map (fun s => s.output) = some "0" := by
  decide

/-- The `0` run halts after 159 steps. -/
theorem zero_halts : run 159 zeroState = none := by
  decide

/-- Re-parsing the printed output with `&` reconstructs the original number:
    the output routine round-trips with the `&` parser. -/
theorem decimal_roundtrip :
    (run 400 decimalState).map (fun s => parseInt s.output.toList) = some ([], 123) ∧
    (run 700 decimal5State).map (fun s => parseInt s.output.toList) = some ([], 12345) ∧
    (run 150 singleState).map (fun s => parseInt s.output.toList) = some ([], 5) ∧
    (run 150 zeroState).map (fun s => parseInt s.output.toList) = some ([], 0) := by
  decide

end LeanFunge.Examples
