/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import Tests.Completeness.Block
import Tests.Completeness.Layout
import Tests.Completeness.LayoutBlock
import Tests.Completeness.LayoutCellMain
import Tests.Completeness.LayoutCellRange
import Tests.Completeness.LayoutCells
import Tests.Completeness.LayoutCorridor
import Tests.Completeness.LayoutCorridorRoute
import Tests.Completeness.LayoutDecz
import Tests.Completeness.LayoutDeczBranch
import Tests.Completeness.LayoutFallthrough
import Tests.Completeness.LayoutHeader
import Tests.Completeness.LayoutJump
import Tests.Completeness.LayoutJumpBlock
import Tests.Completeness.LayoutRouting
import Tests.Completeness.LayoutRowAt
import Tests.Completeness.Linear
import Tests.Completeness.Loop
import Tests.Completeness.LoopC2
import Tests.Completeness.LoopCorridor
import Tests.Completeness.PairEncoding
import Tests.Completeness.Routing
import Tests.Completeness.Simulation
import Tests.Completeness.TwoCounter

/-!
# Turing Completeness Tests Aggregator

This module aggregates the Turing-completeness test modules behind a single
import.
-/
