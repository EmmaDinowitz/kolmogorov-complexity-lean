/-
Copyright (c) 2026 Emma Dinowitz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emma Dinowitz
-/
import KolmogorovMathlib.AlgorithmicRandomness.VanLambalgen.Metric.Defs

/-!
# Products of presented spaces and of almost decidable bases

The product presentation `P.prod Q` of `X × Y` (sup metric) is separable, so `X × Y` is second
countable and its product σ-algebra is Borel. For almost decidable bases `B` of `μ` and `C` of `ν`,
the interleaved family `prodBasis B C` is an almost decidable basis of `μ.prod ν`
(`IsAlmostDecidableBasisIn.prod`); its itinerary at `(x, y)` is the interleaving of the
itineraries (`itinerary_prodBasis`), so it carries `μ.prod ν` to `joinMeasure` of the two image
measures (`map_prod_itinerary_prodBasis`).

## Conventions

A sup-metric ball in `X × Y` is the product of the balls of the same radius. The boundary cover of
`B k × Y` is `W × Y` for a boundary cover `W` of `B k`, at a level shifted by a constant bounding
`ν(Y)`.

## Main declarations

* `Presentation.secondCountableTopology` (blueprint node `vlm:prod-presentation`).
* `itinerary_prodBasis`, `map_prod_itinerary_prodBasis` (blueprint node `vlm:prod-basis`).
* `IsAlmostDecidableBasisIn.prod` (blueprint node `vlm:prod-basis`).

Used by `AlgorithmicRandomness/VanLambalgen/Metric/MainResults.lean`.
-/

namespace Kolmogorov.PointToSet

open MeasureTheory

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]

/-- A presented space is second countable: the ideal points are dense.
Blueprint node `vlm:prod-presentation`. -/
theorem Presentation.secondCountableTopology (P : Presentation X) :
    SecondCountableTopology X := by
  have := P.dense.separableSpace'
  exact UniformSpace.secondCountable_of_separable X

omit [MetricSpace X] [MetricSpace Y] in
/-- The itinerary of a pair in the interleaved product family is the interleaving of the
itineraries. Blueprint node `vlm:prod-basis`. -/
theorem itinerary_prodBasis (B : ℕ → Set X) (C : ℕ → Set Y) (x : X) (y : Y) :
    itinerary (prodBasis B C) (x, y) = cantorJoin (itinerary B x) (itinerary C y) := by
  funext n
  unfold itinerary prodBasis cantorJoin
  split_ifs with h <;> simp [h]

variable [MeasurableSpace X] [MeasurableSpace Y]

/-- The image of a product measure under the itinerary of the interleaved product family is the
joined product of the image measures. Blueprint node `vlm:prod-basis`. -/
theorem map_prod_itinerary_prodBasis {B : ℕ → Set X} {C : ℕ → Set Y} (μ : Measure X)
    (ν : Measure Y) [SFinite ν] (hB : Measurable (itinerary B)) (hC : Measurable (itinerary C)) :
    (μ.prod ν).map (itinerary (prodBasis B C)) =
      joinMeasure (μ.map (itinerary B)) (ν.map (itinerary C)) := by
  sorry -- blueprint node vlm:prod-basis

/-- The interleaved product of almost decidable bases for `μ` and `ν` is an almost decidable basis
for `μ.prod ν` in the product presentation. Blueprint node `vlm:prod-basis`. -/
theorem IsAlmostDecidableBasisIn.prod [OpensMeasurableSpace X] [OpensMeasurableSpace Y]
    {P : Presentation X} {Q : Presentation Y} {A : Set ℕ} {μ : Measure X} {ν : Measure Y}
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] {B : ℕ → Set X} {C : ℕ → Set Y}
    (hP : ComputablePresentationIn P A) (hQ : ComputablePresentationIn Q A)
    (hB : IsAlmostDecidableBasisIn P A μ B) (hC : IsAlmostDecidableBasisIn Q A ν C) :
    IsAlmostDecidableBasisIn (P.prod Q) A (μ.prod ν) (prodBasis B C) := by
  sorry -- blueprint node vlm:prod-basis

end Kolmogorov.PointToSet
