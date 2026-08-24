/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import Tests.Completeness
import Tests.DecimalOutput
import Tests.Direction
import Tests.Examples
import Tests.Grid
import Tests.Invariance
import Tests.Memory
import Tests.Output
import Tests.Parser
import Tests.Random
import Tests.Run
import Tests.Stack
import Tests.Step
import Tests.StepOps
import Tests.Termination

/-!
# Test Suite Aggregator

This root test module gathers all LeanFunge test modules under one import
target, making CI and local verification commands simpler.
-/
