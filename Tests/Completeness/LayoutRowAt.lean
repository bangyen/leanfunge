/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanFunge.Theory.Completeness.LayoutRowAt

/-!
# Block Lookup at Any Column Tests
-/

namespace LeanFunge.Tests

open LeanFunge
open LeanFunge.Completeness

/-- A cell beyond the first block's body is a space. -/
example : (playfieldOf layoutProgram).get 6 4 = ' ' :=
  playfield_row_at layoutProgram 0 (by decide) 6 0 (by decide) (by decide)

end LeanFunge.Tests
