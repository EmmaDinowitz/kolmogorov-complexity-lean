/-
Copyright (c) 2026 Emma Dinowitz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emma Dinowitz
-/
import KolmogorovMathlib.AlgorithmicRandomness.VanLambalgen.Metric.Defs

/-!
# Existence of almost decidable bases (Hoyrup–Rojas)

A finite measure `μ` on a presented space, computable relative to `A` with total mass computable
relative to `A`, has an almost decidable basis relative to `A` (`exists_isAlmostDecidableBasisIn`).
The basis consists of the balls `B(ι i, r)` with radii `r` computable relative to `A`, dense in
every rational interval, whose spheres are `μ`-null.

The radius is found by a nested-interval search: of `m` disjoint closed annuli about `ι i` with
radii in a rational interval, one has measure at most `μ(X)/m`; closed annuli have upper
semicomputable measure (total mass minus the measure of an open set), so such an annulus is found
by a search relative to `A`, and the nested intervals shrink to a radius computable relative to
`A` whose sphere has measure below every `2^{-n}`. The exterior of `B(ι i, r)` is `{d(·, ι i) > r}`,
and the boundary set, the sphere, is covered by the open annuli about it, whose measures are
upper semicomputable and tend to `0`.

## Conventions

Radii are real numbers computable relative to `A`, as `IsComputableRealFamilyIn`. The total mass
is computable relative to `A` in the form `IsComputableRealFamilyIn A fun _ : Unit ↦ μ(X)`.

## Main declarations

* `exists_isAlmostDecidableBasisIn` (blueprint node `vlm:ad-basis-exists`).

Used by `AlgorithmicRandomness/VanLambalgen/Metric/MainResults.lean`.
-/

namespace Kolmogorov.PointToSet

open MeasureTheory

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] {P : Presentation X} {A : Set ℕ}
  {μ : Measure X}

/-- **Hoyrup–Rojas.** A finite Borel measure computable relative to `A`, with total mass computable
relative to `A`, on a presentation whose metric table is computable relative to `A`, has an
almost decidable basis relative to `A`. Blueprint node `vlm:ad-basis-exists`. -/
theorem exists_isAlmostDecidableBasisIn [BorelSpace X] [IsFiniteMeasure μ]
    (hP : ComputablePresentationIn P A) (hμ : IsComputableMeasureIn P A μ)
    (hmass : IsComputableRealFamilyIn A fun _ : Unit => (μ Set.univ).toReal) :
    ∃ B, IsAlmostDecidableBasisIn P A μ B := by
  sorry -- blueprint node vlm:ad-basis-exists

end Kolmogorov.PointToSet
