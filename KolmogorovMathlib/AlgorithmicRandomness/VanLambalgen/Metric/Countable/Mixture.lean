/-
Copyright (c) 2026 Emma Dinowitz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emma Dinowitz
-/
import KolmogorovMathlib.AlgorithmicRandomness.VanLambalgen.Metric.Countable.Basic
import KolmogorovMathlib.PointToSet.Measure.Computable

/-!
# Uniformly computable sequences of measures and their mixture

A member of a uniformly computable sequence of measures is computable
(`IsComputableMeasureFamilyIn.isComputableMeasureIn`), and a probability measure has computable
total mass (`isComputableRealFamilyIn_measure_univ`). The mixture `∑ᵢ 2^{-(i+1)} μ i` of
probability measures is a probability measure (`isProbabilityMeasure_mixMeasure`), computable when
the sequence is uniformly computable (`IsComputableMeasureFamilyIn.isComputableMeasureIn_mix`),
and an almost decidable basis of the mixture is one of every member, with the boundary covers
shifted by `i + 1` levels (`IsAlmostDecidableBasisIn.of_mixMeasure`).

## Main declarations

* `IsComputableMeasureFamilyIn.isComputableMeasureIn`, `isComputableRealFamilyIn_measure_univ`
  (blueprint node `vlm:measure-family`).
* `isProbabilityMeasure_mixMeasure`, `IsComputableMeasureFamilyIn.isComputableMeasureIn_mix`,
  `IsAlmostDecidableBasisIn.of_mixMeasure` (blueprint node `vlm:mix`).

Used by `Metric/Countable/MainResults.lean`.
-/

namespace Kolmogorov.PointToSet

open MeasureTheory
open scoped Computability ENNReal

attribute [local instance] PiCountable.metricSpace

variable {X : Type*} [MetricSpace X] {P : Presentation X} {A : Set ℕ}
  [MeasurableSpace X] {μ : ℕ → Measure X} {B : ℕ → Set X}

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

end Kolmogorov.PointToSet
