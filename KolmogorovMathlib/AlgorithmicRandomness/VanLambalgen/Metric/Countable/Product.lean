/-
Copyright (c) 2026 Emma Dinowitz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emma Dinowitz
-/
import KolmogorovMathlib.AlgorithmicRandomness.VanLambalgen.Metric.Countable.Defs
import KolmogorovMathlib.PointToSet.Measure.Computable

/-!
# Countable products of presented spaces and of almost decidable bases

The presentation `Presentation.pi P` of `ℕ → X` has a metric table computable relative to `A` when
`P` has (`Presentation.computablePresentationIn_pi`). A sequence of probability measures that is
computable relative to `A` uniformly in the index has a mixture `∑ᵢ 2^{-(i+1)} μ i` that is a
probability measure computable relative to `A`; an almost decidable basis of the mixture is one of
every `μ i` (`IsAlmostDecidableBasisIn.of_mixMeasure`), and its product over the coordinates is an
almost decidable basis of `Measure.infinitePi μ` (`IsAlmostDecidableBasisIn.pi`). The itinerary of
a sequence in the product basis is the infinite join of the itineraries of its coordinates
(`itinerary_piBasis`), so the itinerary map carries `Measure.infinitePi μ` to `piJoinMeasure`
(`map_infinitePi_itinerary_piBasis`). Finally a name of a sequence computes a name of its
truncation to the first `i` coordinates (`exists_isCauchyName_pi_below`).

## Conventions

The metric on `ℕ → X` is the local instance `PiCountable.metricSpace`, as in
`Metric/Countable/Defs.lean`. The boundary cover of the product basis at the index `pair j k` is
the cover of `B k` at a level shifted by `j + 1`, since `μ j ≤ 2^{j+1} · mixMeasure μ`.

## Main declarations

* `Presentation.computablePresentationIn_pi` (blueprint node `vlm:pi-presentation`).
* `IsComputableMeasureFamilyIn.isComputableMeasureIn` (blueprint node `vlm:measure-family`).
* `isProbabilityMeasure_mixMeasure`, `IsComputableMeasureFamilyIn.isComputableMeasureIn_mix`,
  `IsAlmostDecidableBasisIn.of_mixMeasure` (blueprint node `vlm:mix`).
* `isComputableRealFamilyIn_measure_univ` (blueprint node `vlm:measure-family`): the total mass of
  a probability measure is computable.
* `itinerary_piBasis`, `map_infinitePi_itinerary_piBasis`, `IsAlmostDecidableBasisIn.pi`
  (blueprint node `vlm:pi-basis`).
* `exists_isCauchyName_pi_below` (blueprint node `vlm:pi-below`).

Used by `AlgorithmicRandomness/VanLambalgen/Metric/Countable/MainResults.lean`.
-/

namespace Kolmogorov.PointToSet

open MeasureTheory
open scoped Computability

attribute [local instance] PiCountable.metricSpace

variable {X : Type*} [MetricSpace X] {P : Presentation X} {A : Set ℕ}

/-- The presentation of `ℕ → X` has a metric table computable relative to `A` when `P` has: the
distance of two ideal sequences is a finite sum, their coordinates agreeing beyond the longer
list. Blueprint node `vlm:pi-presentation`. -/
theorem Presentation.computablePresentationIn_pi (hP : ComputablePresentationIn P A) :
    ComputablePresentationIn P.pi A := by
  sorry -- blueprint node vlm:pi-presentation

omit [MetricSpace X] in
/-- The itinerary of a sequence in the product basis is the infinite join of the itineraries of
its coordinates. Blueprint node `vlm:pi-basis`. -/
theorem itinerary_piBasis (B : ℕ → Set X) (x : ℕ → X) :
    itinerary (piBasis B) x = cantorPiJoin fun j => itinerary B (x j) := by
  funext n
  unfold itinerary piBasis cantorPiJoin
  exact decide_eq_decide.2 Iff.rfl

/-- A Cauchy name of a sequence `y` computes, relative to `A`, a Cauchy name of its truncation
`j ↦ if j < i then y j else P.ι 0`: keep the first `i` entries of each listed ideal sequence.
Blueprint node `vlm:pi-below`. -/
theorem exists_isCauchyName_pi_below {y : ℕ → X} {a : ℕ → ℕ} (ha : IsCauchyName P.pi y a)
    (i : ℕ) :
    ∃ b, IsCauchyName P.pi (fun j => if j < i then y j else P.ι 0) b ∧
      charOracle (oracleJoin A (nameOracle b)) ≤ᵀ charOracle (oracleJoin A (nameOracle a)) := by
  sorry -- blueprint node vlm:pi-below

variable [MeasurableSpace X] {μ : ℕ → Measure X} {B : ℕ → Set X}

/-- A member of a uniformly computable sequence of measures is computable.
Blueprint node `vlm:measure-family`. -/
theorem IsComputableMeasureFamilyIn.isComputableMeasureIn (hμ : IsComputableMeasureFamilyIn P A μ)
    (i : ℕ) : IsComputableMeasureIn P A (μ i) := by
  sorry -- blueprint node vlm:measure-family

/-- The total mass of a probability measure is computable relative to every oracle.
Blueprint node `vlm:measure-family`. -/
theorem isComputableRealFamilyIn_measure_univ (ν : Measure X) [IsProbabilityMeasure ν] :
    IsComputableRealFamilyIn A fun _ : Unit => (ν Set.univ).toReal := by
  sorry -- blueprint node vlm:measure-family

/-- The mixture of probability measures is a probability measure. Blueprint node `vlm:mix`. -/
instance isProbabilityMeasure_mixMeasure [∀ i, IsProbabilityMeasure (μ i)] :
    IsProbabilityMeasure (mixMeasure μ) := by
  sorry -- blueprint node vlm:mix

/-- The mixture of a uniformly computable sequence of probability measures is computable.
Blueprint node `vlm:mix`. -/
theorem IsComputableMeasureFamilyIn.isComputableMeasureIn_mix [∀ i, IsProbabilityMeasure (μ i)]
    (hμ : IsComputableMeasureFamilyIn P A μ) : IsComputableMeasureIn P A (mixMeasure μ) := by
  sorry -- blueprint node vlm:mix

/-- An almost decidable basis of the mixture is an almost decidable basis of every member, with
the boundary covers shifted by `i + 1` levels. Blueprint node `vlm:mix`. -/
theorem IsAlmostDecidableBasisIn.of_mixMeasure (hB : IsAlmostDecidableBasisIn P A (mixMeasure μ) B)
    (i : ℕ) : IsAlmostDecidableBasisIn P A (μ i) B := by
  sorry -- blueprint node vlm:mix

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
