/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanFunge.Theory.Completeness.Block
import LeanFunge.Theory.Completeness.BlockC2
import LeanFunge.Theory.Completeness.Layout
import LeanFunge.Theory.Completeness.LayoutBlock
import LeanFunge.Theory.Completeness.LayoutCellMain
import LeanFunge.Theory.Completeness.LayoutCellRange
import LeanFunge.Theory.Completeness.LayoutCells
import LeanFunge.Theory.Completeness.LayoutCorridor
import LeanFunge.Theory.Completeness.LayoutDecz
import LeanFunge.Theory.Completeness.LayoutDeczBranch
import LeanFunge.Theory.Completeness.LayoutFallthrough
import LeanFunge.Theory.Completeness.LayoutHeader
import LeanFunge.Theory.Completeness.LayoutJump
import LeanFunge.Theory.Completeness.LayoutJumpBlock
import LeanFunge.Theory.Completeness.LayoutRouting
import LeanFunge.Theory.Completeness.LayoutRowAt
import LeanFunge.Theory.Completeness.Linear
import LeanFunge.Theory.Completeness.LinearMain
import LeanFunge.Theory.Completeness.LinearRow
import LeanFunge.Theory.Completeness.LinearSimulation
import LeanFunge.Theory.Completeness.Loop
import LeanFunge.Theory.Completeness.LoopC2
import LeanFunge.Theory.Completeness.LoopCorridor
import LeanFunge.Theory.Completeness.PairEncoding
import LeanFunge.Theory.Completeness.Routing
import LeanFunge.Theory.Completeness.Simulation
import LeanFunge.Theory.Completeness.TwoCounter

/-!
# Turing Completeness Aggregator

This module aggregates the Turing-completeness development behind a single
import. The plan is to show that every two-counter machine can be simulated by
a LeanFunge playfield with the counters encoded as a single stack value
`2^c1 * 3^c2`, from which universality of LeanFunge follows from the classical
universality of two-counter machines.
-/
