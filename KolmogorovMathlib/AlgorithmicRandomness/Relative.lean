/-
Copyright (c) 2026 Emma Dinowitz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emma Dinowitz
-/
import KolmogorovMathlib.AlgorithmicRandomness.Relative.Defs
import KolmogorovMathlib.AlgorithmicRandomness.Relative.Basic

/-!
# Martin-Löf randomness on Cantor space relative to an oracle

The Cantor-space notions of effective openness, computable measure, Martin-Löf test and
Martin-Löf randomness, relativized to an oracle `A : Set ℕ` (blueprint
`docs/BLUEPRINT.md`, nodes `vl:seq-oracle` to `vl:ae-random`).

* `Defs` — `seqOracle`, `IsUniformlyEffectiveOpenIn`, `IsComputableCantorMeasureIn`,
  `IsMartinLofTestIn`, `IsMartinLofRandomIn`.
* `Basic` — monotonicity in the oracle, the bridge to unrelativized randomness at the empty
  oracle, almost every sequence is random, finiteness of relatively computable measures.
-/
