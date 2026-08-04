/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanFunge.Examples.DecimalOutput

/-!
# Decimal Output Tests
-/

namespace LeanFunge.Tests

open LeanFunge
open LeanFunge.Examples

example :
    (run 400 decimalState).map (fun s => s.output) = some "123" :=
  decimal_output

example : run 439 decimalState = none :=
  decimal_halts

example :
    (run 700 decimal5State).map (fun s => s.output) = some "12345" :=
  decimal5_output

example : run 719 decimal5State = none :=
  decimal5_halts

example :
    (run 150 singleState).map (fun s => s.output) = some "5" :=
  single_output

example : run 159 singleState = none :=
  single_halts

example :
    (run 150 zeroState).map (fun s => s.output) = some "0" :=
  zero_output

example : run 159 zeroState = none :=
  zero_halts

example :
    (run 400 decimalState).map (fun s => parseInt s.output.toList) = some ([], 123) ∧
    (run 700 decimal5State).map (fun s => parseInt s.output.toList) = some ([], 12345) ∧
    (run 150 singleState).map (fun s => parseInt s.output.toList) = some ([], 5) ∧
    (run 150 zeroState).map (fun s => parseInt s.output.toList) = some ([], 0) :=
  decimal_roundtrip

end LeanFunge.Tests
