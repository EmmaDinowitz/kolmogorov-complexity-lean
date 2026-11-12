/-
Copyright (c) 2026 Emma Dinowitz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emma Dinowitz
-/
import KolmogorovMathlib.AlgorithmicRandomness.VanLambalgen.Metric.Defs
import KolmogorovMathlib.AlgorithmicRandomness.Relative.Basic

/-!
# Transfer of randomness along the itinerary map

For an almost decidable basis `B` relative to `A` for `μ`, the itinerary map `φ = itinerary B`
sends a point to the sequence of bits `x ∈ B k`. This module proves that `φ` is measurable, that
it preserves randomness in both directions, relative to every oracle above `A`
(`IsAlmostDecidableBasisIn.mem_randomPoints_iff`), and that the image measure is computable on
Cantor space relative to `A` when `μ` is
(`IsAlmostDecidableBasisIn.isComputableCantorMeasureIn_map`).

## Conventions

Randomness on the presented space is `randomPoints P A μ`; on Cantor space it is
`IsMartinLofRandomIn A`. Measures are in `ℝ≥0∞`. A test on Cantor space pulls back along `φ` to a
union of finite intersections of the members `B k` and the exteriors `D k`, which differs from the
exact preimage by the boundary sets `(B k ∪ D k)ᶜ`; a random point avoids these.

## Main declarations

* `IsAlmostDecidableBasisIn.measurable_itinerary` (blueprint node `vlm:itinerary`).
* `IsAlmostDecidableBasisIn.mem_randomPoints_iff` (blueprint node `vlm:transfer`).
* `IsAlmostDecidableBasisIn.isComputableCantorMeasureIn_map` (blueprint node
  `vlm:itinerary-measure`).

Used by `AlgorithmicRandomness/VanLambalgen/Metric/MainResults.lean`.
-/

namespace Kolmogorov.PointToSet

open MeasureTheory
open scoped Computability

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] {P : Presentation X} {A : Set ℕ}
  {μ : Measure X} {B : ℕ → Set X}

/-- The itinerary map of an almost decidable basis is measurable: each bit is the indicator of an
open set. Blueprint node `vlm:itinerary`. -/
theorem IsAlmostDecidableBasisIn.measurable_itinerary [OpensMeasurableSpace X]
    (hB : IsAlmostDecidableBasisIn P A μ B) : Measurable (itinerary B) := by
  sorry -- blueprint node vlm:itinerary

/-- **Transfer of randomness.** For an almost decidable basis `B` relative to `A` for `μ` and every
oracle `A'` above `A`, a point is `μ`-random relative to `A'` exactly when its itinerary is random
relative to `A'` for the image of `μ` under the itinerary map. No computability of `μ` is used.
Blueprint node `vlm:transfer`. -/
theorem IsAlmostDecidableBasisIn.mem_randomPoints_iff [OpensMeasurableSpace X]
    (hB : IsAlmostDecidableBasisIn P A μ B) {A' : Set ℕ} (hAA' : charOracle A ≤ᵀ charOracle A')
    {x : X} :
    x ∈ randomPoints P A' μ ↔ IsMartinLofRandomIn A' (μ.map (itinerary B)) (itinerary B x) := by
  sorry -- blueprint node vlm:transfer

/-- For a finite measure `μ` computable relative to `A` with total mass computable relative to `A`,
the image of `μ` under the itinerary map of an almost decidable basis is computable relative to
`A` on Cantor space. Blueprint node `vlm:itinerary-measure`. -/
theorem IsAlmostDecidableBasisIn.isComputableCantorMeasureIn_map [BorelSpace X]
    [IsFiniteMeasure μ] (hB : IsAlmostDecidableBasisIn P A μ B) (hμ : IsComputableMeasureIn P A μ)
    (hmass : IsComputableRealFamilyIn A fun _ : Unit => (μ Set.univ).toReal) :
    IsComputableCantorMeasureIn A (μ.map (itinerary B)) := by
  sorry -- blueprint node vlm:itinerary-measure

end Kolmogorov.PointToSet
