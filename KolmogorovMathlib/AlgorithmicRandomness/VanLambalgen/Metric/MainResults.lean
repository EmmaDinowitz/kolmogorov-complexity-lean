/-
Copyright (c) 2026 Emma Dinowitz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emma Dinowitz
-/
import KolmogorovMathlib.AlgorithmicRandomness.VanLambalgen.MainResults
import KolmogorovMathlib.AlgorithmicRandomness.VanLambalgen.Metric.Transfer
import KolmogorovMathlib.AlgorithmicRandomness.VanLambalgen.Metric.Oracle
import KolmogorovMathlib.AlgorithmicRandomness.VanLambalgen.Metric.Basis
import KolmogorovMathlib.AlgorithmicRandomness.VanLambalgen.Metric.Product

/-!
# The van Lambalgen theorem on presented metric spaces

Let `X`, `Y` be presented metric spaces whose metric tables are computable relative to `A`, and
`μ`, `ν` finite Borel measures on them, computable relative to `A` with total masses computable
relative to `A`. A pair `(x, y)` is `μ ⊗ ν`-random relative to `A` (in the product presentation,
sup metric) exactly when `x` is `μ`-random relative to `A` and `y` is `ν`-random relative to
`A ⊕ a` for some Cauchy name `a` of `x` (`mem_randomPoints_prod_iff`, blueprint node `vlm:main`).

The proof transfers the Cantor-space theorem (`isMartinLofRandomIn_cantorJoin_iff`, node
`vl:main`) along the itinerary maps of almost decidable bases (Hoyrup–Rojas, node
`vlm:ad-basis-exists`), which preserve randomness relative to every oracle above `A` (node
`vlm:transfer`); at a random point the itinerary is the least degree of a name (node `vlm:oracle`).

## Conventions

"Some name" cannot be strengthened to "every name": a point has names of arbitrarily high degree,
and a name can encode `y` itself. Both measures must be computable relative to `A` here, while the
Cantor-space theorem lets the first be arbitrary finite: the itinerary of the first factor needs
`μ`-null boundaries found effectively. The blind version on presented spaces and the countable
form are not formalized (see `docs/BLUEPRINT.md`).

## Main statements

* `IsAlmostDecidableBasisIn.mem_randomPoints_iff` (node `vlm:transfer`) and
  `exists_isAlmostDecidableBasisIn` (node `vlm:ad-basis-exists`) are restated here as
  `mem_randomPoints_iff_itinerary`.
* `mem_randomPoints_prod_iff` (blueprint node `vlm:main`).
-/

namespace Kolmogorov.PointToSet

open MeasureTheory
open scoped Computability

variable {X Y : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y]
  {P : Presentation X} {Q : Presentation Y} {A : Set ℕ} {μ : Measure X} {ν : Measure Y}

/-- **Randomness through itineraries.** For a finite measure computable relative to `A`, with
total mass computable relative to `A`, there is a family `B` of open sets such that, relative to
every oracle `A'` above `A`, a point is random exactly when its itinerary in `B` is random for the
image measure, and that image measure is computable relative to `A` on Cantor space.
Blueprint nodes `vlm:ad-basis-exists`, `vlm:transfer`, `vlm:itinerary-measure`. -/
theorem mem_randomPoints_iff_itinerary [IsFiniteMeasure μ] (hP : ComputablePresentationIn P A)
    (hμ : IsComputableMeasureIn P A μ)
    (hmass : IsComputableRealFamilyIn A fun _ : Unit => (μ Set.univ).toReal) :
    ∃ B : ℕ → Set X, IsComputableCantorMeasureIn A (μ.map (itinerary B)) ∧
      ∀ A' : Set ℕ, charOracle A ≤ᵀ charOracle A' → ∀ x : X,
        (x ∈ randomPoints P A' μ ↔
          IsMartinLofRandomIn A' (μ.map (itinerary B)) (itinerary B x)) := by
  obtain ⟨B, hB⟩ := exists_isAlmostDecidableBasisIn hP hμ hmass
  exact ⟨B, hB.isComputableCantorMeasureIn_map hμ hmass,
    fun _ hAA' _ => hB.mem_randomPoints_iff hAA'⟩

/-- **van Lambalgen's theorem on presented metric spaces.** For presentations with metric tables
computable relative to `A` and finite Borel measures `μ`, `ν` computable relative to `A` with total
masses computable relative to `A`: the pair `(x, y)` is `μ ⊗ ν`-random relative to `A` exactly
when `x` is `μ`-random relative to `A` and `y` is `ν`-random relative to `A ⊕ a` for some Cauchy
name `a` of `x`. Blueprint node `vlm:main`. -/
theorem mem_randomPoints_prod_iff [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hP : ComputablePresentationIn P A) (hQ : ComputablePresentationIn Q A)
    (hμ : IsComputableMeasureIn P A μ)
    (hμm : IsComputableRealFamilyIn A fun _ : Unit => (μ Set.univ).toReal)
    (hν : IsComputableMeasureIn Q A ν)
    (hνm : IsComputableRealFamilyIn A fun _ : Unit => (ν Set.univ).toReal) {x : X} {y : Y} :
    (x, y) ∈ randomPoints (P.prod Q) A (μ.prod ν) ↔
      x ∈ randomPoints P A μ ∧
        ∃ a, IsCauchyName P x a ∧ y ∈ randomPoints Q (oracleJoin A (nameOracle a)) ν := by
  have := P.secondCountableTopology
  obtain ⟨B, hB⟩ := exists_isAlmostDecidableBasisIn hP hμ hμm
  obtain ⟨C, hC⟩ := exists_isAlmostDecidableBasisIn hQ hν hνm
  have hBC := hB.prod hP hQ hC
  have hνC := hC.isComputableCantorMeasureIn_map hν hνm
  rw [hBC.mem_randomPoints_iff (TuringReducible.refl _),
    map_prod_itinerary_prodBasis μ ν hB.measurable_itinerary hC.measurable_itinerary,
    itinerary_prodBasis, isMartinLofRandomIn_cantorJoin_iff hνC,
    ← hB.mem_randomPoints_iff (TuringReducible.refl _),
    ← hC.mem_randomPoints_iff (oracle_joins A (seqOracle (itinerary B x)))]
  refine and_congr_right fun hx => ⟨fun hy => ?_, fun ⟨a, ha, hy⟩ => ?_⟩
  · obtain ⟨a, ha, hle⟩ := hB.exists_isCauchyName_le_itinerary x
    exact ⟨a, ha, randomPoints_anti_oracle Q ν hle hy⟩
  · exact randomPoints_anti_oracle Q ν (hB.itinerary_le_of_mem_randomPoints hP hx ha) hy

end Kolmogorov.PointToSet
