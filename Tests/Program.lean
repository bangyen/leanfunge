/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanFunge.Theory.Program

/-!
# Program Equivalence Tests
-/

namespace LeanFunge.Tests

open LeanFunge

example (p : Program w h) : Program.equiv p p :=
  Program.equiv_refl p

example {p q : Program w h} (h : Program.equiv p q) : Program.equiv q p :=
  Program.equiv_symm h

example {p q r : Program w h} (hpq : Program.equiv p q) (hqr : Program.equiv q r) :
    Program.equiv p r :=
  Program.equiv_trans hpq hqr

end LeanFunge.Tests
