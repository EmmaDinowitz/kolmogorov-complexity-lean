/-
Copyright (c) 2026 Emma Dinowitz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emma Dinowitz
-/
import KolmogorovMathlib.AlgorithmicRandomness.VanLambalgen.Metric.Defs
import KolmogorovMathlib.Oracle.Joins

/-!
# The itinerary as an oracle for a point

For an almost decidable basis `B` relative to `A`, the itinerary of a point and its Cauchy names
compute each other relative to `A`:

* the itinerary computes a name, for every point (`exists_isCauchyName_le_itinerary`): search for
  a small basic ball written as a finite intersection of members containing the point;
* every name computes the itinerary at a random point (`itinerary_le_of_mem_randomPoints`): a
  random point lies in no boundary set `(B k ∪ D k)ᶜ`, so bit `k` is found by searching for a
  certificate of `x ∈ B k` or of `x ∈ D k`.

So at a random point, `A ⊕ itinerary` is the least of the degrees `A ⊕ a` over the names `a`.

## Conventions

Names are encoded by their graphs (`nameOracle`); oracles are joined with
`PointToSet.oracleJoin`.

## Main declarations

* `IsAlmostDecidableBasisIn.exists_isCauchyName_le_itinerary`,
  `IsAlmostDecidableBasisIn.itinerary_le_of_mem_randomPoints` (blueprint node `vlm:oracle`).

Used by `AlgorithmicRandomness/VanLambalgen/Metric/MainResults.lean`.
-/

namespace Kolmogorov.PointToSet

open MeasureTheory
open scoped Computability

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] {P : Presentation X} {A : Set ℕ}
  {μ : Measure X} {B : ℕ → Set X}

/-- The itinerary of a point in an almost decidable basis computes, relative to `A`, a Cauchy name
of the point. Blueprint node `vlm:oracle`. -/
theorem IsAlmostDecidableBasisIn.exists_isCauchyName_le_itinerary
    (hB : IsAlmostDecidableBasisIn P A μ B) (x : X) :
    ∃ a, IsCauchyName P x a ∧
      charOracle (oracleJoin A (nameOracle a)) ≤ᵀ
        charOracle (oracleJoin A (seqOracle (itinerary B x))) := by
  sorry -- blueprint node vlm:oracle

/-- At a point that is `μ`-random relative to `A`, every Cauchy name computes the itinerary
relative to `A`, provided the presentation has a metric table computable relative to `A`.
Blueprint node `vlm:oracle`. -/
theorem IsAlmostDecidableBasisIn.itinerary_le_of_mem_randomPoints
    (hB : IsAlmostDecidableBasisIn P A μ B) (hP : ComputablePresentationIn P A) {x : X}
    (hx : x ∈ randomPoints P A μ) {a : ℕ → ℕ} (ha : IsCauchyName P x a) :
    charOracle (oracleJoin A (seqOracle (itinerary B x))) ≤ᵀ
      charOracle (oracleJoin A (nameOracle a)) := by
  sorry -- blueprint node vlm:oracle

end Kolmogorov.PointToSet
