/-
Copyright (c) 2026 Emma Dinowitz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emma Dinowitz
-/
import KolmogorovMathlib.AlgorithmicRandomness.VanLambalgen.Metric.Countable.Basic
import KolmogorovMathlib.AlgorithmicRandomness.VanLambalgen.Countable.Split

/-!
# The product of an almost decidable basis over the coordinates

For an almost decidable basis `B` of the mixture `∑ᵢ 2^{-(i+1)} μ i`, the product basis
`piBasis B` (the sets `{x | x j ∈ B k}` at the index `pair j k`) is an almost decidable basis of
`Measure.infinitePi μ` in the presentation `Presentation.pi P` (`IsAlmostDecidableBasisIn.pi`).
The itinerary of a sequence in the product basis is the infinite join of the itineraries of its
coordinates (`itinerary_piBasis`), so the itinerary map carries the product measure to
`piJoinMeasure` (`map_infinitePi_itinerary_piBasis`).

## Conventions

The metric on `ℕ → X` is the local instance `PiCountable.metricSpace`. The boundary cover of
`piBasis B` at `pair j k` is the cover of `B k` at a level shifted by `j + 1`, pulled back to
coordinate `j`, since `μ j ≤ 2^{j+1} • mixMeasure μ` (`le_two_pow_smul_mixMeasure`).

## Main declarations

* `itinerary_piBasis`, `IsAlmostDecidableBasisIn.pi`, `map_infinitePi_itinerary_piBasis`
  (blueprint node `vlm:pi-basis`).

Used by `Metric/Countable/MainResults.lean`.
-/

namespace Kolmogorov.PointToSet

open MeasureTheory
open scoped Computability ENNReal

attribute [local instance] PiCountable.metricSpace

variable {X : Type*} [MetricSpace X] {P : Presentation X} {A : Set ℕ}

omit [MetricSpace X] in
/-- The itinerary of a sequence in the product basis is the infinite join of the itineraries of
its coordinates. Blueprint node `vlm:pi-basis`. -/
theorem itinerary_piBasis (B : ℕ → Set X) (x : ℕ → X) :
    itinerary (piBasis B) x = cantorPiJoin fun j => itinerary B (x j) := by
  funext n
  unfold itinerary piBasis cantorPiJoin
  exact decide_eq_decide.2 Iff.rfl

variable [MeasurableSpace X] {μ : ℕ → Measure X} {B : ℕ → Set X}

/-- The product over the coordinates of an almost decidable basis of the mixture is an almost
decidable basis of the product measure. Blueprint node `vlm:pi-basis`. -/
theorem IsAlmostDecidableBasisIn.pi [OpensMeasurableSpace X] [∀ i, IsProbabilityMeasure (μ i)]
    (hP : ComputablePresentationIn P A) (hB : IsAlmostDecidableBasisIn P A (mixMeasure μ) B) :
    IsAlmostDecidableBasisIn P.pi A (Measure.infinitePi μ) (piBasis B) := by
  sorry -- blueprint node vlm:pi-basis

/-- The itinerary map of the product basis carries the product measure to the countable product
of the image measures. Blueprint node `vlm:pi-basis`. -/
theorem map_infinitePi_itinerary_piBasis [∀ i, IsProbabilityMeasure (μ i)]
    (hB : Measurable (itinerary B)) :
    (Measure.infinitePi μ).map (itinerary (piBasis B)) =
      piJoinMeasure fun j => (μ j).map (itinerary B) := by
  sorry -- blueprint node vlm:pi-basis

end Kolmogorov.PointToSet
