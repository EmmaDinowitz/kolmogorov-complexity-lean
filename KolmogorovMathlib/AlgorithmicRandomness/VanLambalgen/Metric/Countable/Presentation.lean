/-
Copyright (c) 2026 Emma Dinowitz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emma Dinowitz
-/
import KolmogorovMathlib.AlgorithmicRandomness.VanLambalgen.Metric.Countable.Defs

/-!
# The presentation of `ℕ → X`

The metric table of `Presentation.pi P` is computable relative to `A` when that of `P` is
(`Presentation.computablePresentationIn_pi`): the distance of two ideal sequences is a finite
sum up to a tail, since their coordinates agree beyond the longer list. A name of a sequence
computes a name of its truncation to the first `i` coordinates (`exists_isCauchyName_pi_below`).

## Conventions

The metric on `ℕ → X` is the local instance `PiCountable.metricSpace`, as in
`Metric/Countable/Defs.lean`.

## Main declarations

* `Presentation.computablePresentationIn_pi` (blueprint node `vlm:pi-presentation`).
* `exists_isCauchyName_pi_below` (blueprint node `vlm:pi-below`).

Used by `Metric/Countable/MainResults.lean`.
-/

namespace Kolmogorov.PointToSet

open MeasureTheory
open scoped Computability ENNReal

attribute [local instance] PiCountable.metricSpace

variable {X : Type*} [MetricSpace X] {P : Presentation X} {A : Set ℕ}

/-- The presentation of `ℕ → X` has a metric table computable relative to `A` when `P` has: the
distance of two ideal sequences is a finite sum, their coordinates agreeing beyond the longer
list. Blueprint node `vlm:pi-presentation`. -/
theorem Presentation.computablePresentationIn_pi (hP : ComputablePresentationIn P A) :
    ComputablePresentationIn P.pi A := by
  sorry -- blueprint node vlm:pi-presentation

/-- A Cauchy name of a sequence `y` computes, relative to `A`, a Cauchy name of its truncation
`j ↦ if j < i then y j else P.ι 0`: keep the first `i` entries of each listed ideal sequence.
Blueprint node `vlm:pi-below`. -/
theorem exists_isCauchyName_pi_below {y : ℕ → X} {a : ℕ → ℕ} (ha : IsCauchyName P.pi y a)
    (i : ℕ) :
    ∃ b, IsCauchyName P.pi (fun j => if j < i then y j else P.ι 0) b ∧
      charOracle (oracleJoin A (nameOracle b)) ≤ᵀ charOracle (oracleJoin A (nameOracle a)) := by
  sorry -- blueprint node vlm:pi-below

end Kolmogorov.PointToSet
