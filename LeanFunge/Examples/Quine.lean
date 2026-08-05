/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanFunge.Core.Semantics

/-!
# Quine

A Befunge-93 quine: a program that prints its own source code. The classic
`01->1# +# :# 0# g# ,# :# 5# 8# *# 4# +# -# _@` walks rightward through the
playfield, reading each cell with `g` and printing it with `,`, before the
`_` branch finally exits right onto the terminal `@`.

## Main definitions

* `quineRow`, `quineStr`, `quineGrid`, `quineState`: The program, its source,
  its playfield, and its initial state.

## Theorems

* `quine_output`: After 2407 steps the output is the program's own source.
* `quine_halts`: The program halts after 2408 steps.
-/

namespace LeanFunge.Examples

/-- The single row of the quine program. -/
def quineRow : List Char :=
  String.toList "01->1# +# :# 0# g# ,# :# 5# 8# *# 4# +# -# _@"

/-- The source string that the program prints. -/
def quineStr : String :=
  String.ofList quineRow

/-- The playfield of the quine program. -/
def quineGrid : Grid 45 1 :=
  Grid.ofRows 45 1 [quineRow]

/-- The initial state of the quine program. -/
def quineState : State 45 1 :=
  State.init quineGrid

/-- After 2407 steps the output is the program's own source. -/
theorem quine_output :
    (run 2407 quineState).map (fun s => s.output) = some quineStr := by
  decide

/-- The program halts after 2408 steps. -/
theorem quine_halts : run 2408 quineState = none := by
  decide

end LeanFunge.Examples
