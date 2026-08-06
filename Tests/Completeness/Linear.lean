/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanFunge.Theory.Completeness.LinearMain

/-!
# Branch-Free Simulation Tests
-/

namespace LeanFunge.Tests

open LeanFunge.Completeness

example (c : Fin 2) : (linearCells (.inc c)).length = 2 :=
  linearCells_length_inc c

example (prog : CMProgram) (j : ℕ)
    (hinc : ∀ i, i < j → prog.getD i .halt = .inc 0 ∨ prog.getD i .halt = .inc 1) :
    (linearRowAux prog).drop (2 * j) = linearRowAux (prog.drop j) :=
  linearRowAux_drop prog j hinc

example (prog : CMProgram) (j : ℕ)
    (hinc : ∀ i, i < j → prog.getD i .halt = .inc 0 ∨ prog.getD i .halt = .inc 1)
    (hjinc : prog.getD j .halt = .inc 0 ∨ prog.getD j .halt = .inc 1) :
    (linearRow prog).getD (1 + 2 * j) ' ' = (linearCells (prog.getD j .halt)).getD 0 ' ' :=
  linearRow_get_first prog j hinc hjinc

example (prog : CMProgram) (j : ℕ)
    (hinc : ∀ i, i < j → prog.getD i .halt = .inc 0 ∨ prog.getD i .halt = .inc 1) :
    1 + 2 * j < (linearRow prog).length :=
  linearRow_length prog j hinc

example (prog : CMProgram) (j : ℕ) (c : Fin 2) (s : CMState)
    (h : prog.getD j .halt = .inc c) :
    foldIncs prog (j + 1) s = CMInstr.incCounter c (foldIncs prog j s) :=
  foldIncs_succ_inc prog j c s h

example (prog : CMProgram) (c1 c2 : ℕ) {j : ℕ}
    (h : prog.getD j .halt = .inc 0) :
    (Int.ofNat (encode (foldIncs prog j (CMInstr.startCM c1 c2)).c1
                       (foldIncs prog j (CMInstr.startCM c1 c2)).c2)) * 2
      = Int.ofNat (encode (foldIncs prog (j + 1) (CMInstr.startCM c1 c2)).c1
                          (foldIncs prog (j + 1) (CMInstr.startCM c1 c2)).c2) :=
  enc_update_inc_zero prog c1 c2 h

example (prog : CMProgram) (c1 c2 : ℕ) (j : ℕ)
    (hinc : ∀ i, i < j → prog.getD i .halt = .inc 0 ∨ prog.getD i .halt = .inc 1)
    (hw : 1 + 2 * j < (linearRow prog).length) :
    run (1 + 2 * j) (linearStart prog c1 c2) =
      some { linearStart prog c1 c2 with
        stack := [Int.ofNat (encode (foldIncs prog j (CMInstr.startCM c1 c2)).c1
                                     (foldIncs prog j (CMInstr.startCM c1 c2)).c2)],
        pc := (1 + 2 * j, 0) } :=
  linear_prefix prog c1 c2 j hinc hw

example (prog : CMProgram) (c1 c2 : ℕ) (hpos : 0 < prog.length)
    (hinc : ∀ i, i + 1 < prog.length → prog.getD i .halt = .inc 0 ∨ prog.getD i .halt = .inc 1) :
    (run (1 + 2 * (prog.length - 1)) (linearStart prog c1 c2)).map (fun s => s.stack)
      = some [Int.ofNat (encode (foldIncs prog (prog.length - 1) (CMInstr.startCM c1 c2)).c1
                                 (foldIncs prog (prog.length - 1) (CMInstr.startCM c1 c2)).c2)] :=
  linear_stack prog c1 c2 hpos hinc

example (prog : CMProgram) (c1 c2 : ℕ) (hpos : 0 < prog.length)
    (hinc : ∀ i, i + 1 < prog.length → prog.getD i .halt = .inc 0 ∨ prog.getD i .halt = .inc 1) :
    (run (1 + 2 * (prog.length - 1)) (linearStart prog c1 c2)).map (fun s => s.stack)
      = (CMInstr.run prog (prog.length - 1) (CMInstr.startCM c1 c2)).map
          (fun s => [Int.ofNat (encode s.c1 s.c2)]) :=
  linear_simulation prog c1 c2 hpos hinc

end LeanFunge.Tests
