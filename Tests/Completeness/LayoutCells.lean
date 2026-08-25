/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanFunge.Theory.Completeness.LayoutCells

/-!
# Generated Playfield Cell Lookup Tests
-/

namespace LeanFunge.Tests

open LeanFunge.Completeness

example :
    (playfieldOf layoutProgram).get 1 4 = blockBodyAt (layoutProgram.getD 0 .halt) 0 0 :=
  playfield_block_get layoutProgram 0 (by decide) 0 0 (by decide) (by decide)

example :
    (playfieldOf layoutProgram).get 8 6 = blockBodyAt (layoutProgram.getD 1 .halt) 4 0 :=
  playfield_block_get layoutProgram 1 (by decide) 4 0 (by decide) (by decide)

example :
    (playfieldOf layoutProgram).get 9 9 = blockBodyAt (layoutProgram.getD 1 .halt) 5 3 :=
  playfield_block_get layoutProgram 1 (by decide) 5 3 (by decide) (by decide)

example :
    (playfieldOf layoutProgram).get 9 11 = blockBodyAt (layoutProgram.getD 2 .halt) 0 0 :=
  playfield_block_get layoutProgram 2 (by decide) 0 0 (by decide) (by decide)

end LeanFunge.Tests
