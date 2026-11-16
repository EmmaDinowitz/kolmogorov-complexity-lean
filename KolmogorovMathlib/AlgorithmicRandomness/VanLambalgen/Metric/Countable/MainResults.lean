/-
Copyright (c) 2026 Emma Dinowitz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emma Dinowitz
-/
import KolmogorovMathlib.AlgorithmicRandomness.VanLambalgen.Metric.MainResults
import KolmogorovMathlib.AlgorithmicRandomness.VanLambalgen.Metric.Countable.Presentation
import KolmogorovMathlib.AlgorithmicRandomness.VanLambalgen.Metric.Countable.Mixture
import KolmogorovMathlib.AlgorithmicRandomness.VanLambalgen.Metric.Countable.Basis

/-!
# The countable van Lambalgen theorem on a presented metric space

Let `X` be a presented space whose metric table is computable relative to `A`, and `μ i` a
sequence of Borel probability measures on `X`, computable relative to `A` uniformly in `i`. If a
sequence `x : ℕ → X` is random relative to `A` for the product measure `Measure.infinitePi μ`
(presentation `Presentation.pi P`), then each coordinate `x i` is `μ i`-random relative to `A ⊕ a`
for some Cauchy name `a` of the other coordinates (`mem_randomPoints_coordinate_of_pi`, blueprint
node `vlm:countable`), and likewise of the earlier coordinates
(`mem_randomPoints_coordinate_of_pi_below`, node `vlm:countable-below`). Random sequences exist
(`exists_mem_randomPoints_pi`, node `vlm:countable-nonvacuous`).

The proof transfers the Cantor-space countable theorem (`vl:countable`) along the itinerary of the
product basis of one almost decidable basis of the mixture `∑ᵢ 2^{-(i+1)} μ i`.

## Conventions

The metric on `ℕ → X` is Mathlib's `PiCountable.metricSpace`, a local instance in this file (its
topology is the product topology). The other coordinates are the sequence `j ↦ x (skipIndex i j)`;
the earlier ones are the sequence `j ↦ if j < i then x j else P.ι 0`. As on Cantor space, only the
direction from the product to its coordinates is stated; the converse is false.

## Main statements

* `mem_randomPoints_coordinate_of_pi` (blueprint node `vlm:countable`).
* `mem_randomPoints_coordinate_of_pi_below` (blueprint node `vlm:countable-below`).
* `exists_mem_randomPoints_pi` (blueprint node `vlm:countable-nonvacuous`).
-/

namespace Kolmogorov.PointToSet

open MeasureTheory
open scoped Computability

attribute [local instance] PiCountable.metricSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] {P : Presentation X}
  {A : Set ℕ} {μ : ℕ → Measure X} [∀ i, IsProbabilityMeasure (μ i)]

/-- **Countable van Lambalgen on a presented space.** For a presentation with metric table
computable relative to `A` and probability measures `μ i` computable relative to `A` uniformly in
`i`: if `x` is random relative to `A` for the product measure, then `x i` is `μ i`-random relative
to `A ⊕ a` for some Cauchy name `a` of the other coordinates `j ↦ x (skipIndex i j)`.
Blueprint node `vlm:countable`. -/
theorem mem_randomPoints_coordinate_of_pi (hP : ComputablePresentationIn P A)
    (hμ : IsComputableMeasureFamilyIn P A μ) {x : ℕ → X}
    (hx : x ∈ randomPoints P.pi A (Measure.infinitePi μ)) (i : ℕ) :
    ∃ a, IsCauchyName P.pi (fun j => x (skipIndex i j)) a ∧
      x i ∈ randomPoints P (oracleJoin A (nameOracle a)) (μ i) := by
  have := P.secondCountableTopology
  obtain ⟨B, hB⟩ := exists_isAlmostDecidableBasisIn hP hμ.isComputableMeasureIn_mix
    (isComputableRealFamilyIn_measure_univ _)
  have hBi := hB.of_mixMeasure i
  have hφ := hB.measurable_itinerary
  have hBpi := hB.pi hP
  rw [hBpi.mem_randomPoints_iff (P.computablePresentationIn_pi hP) (TuringReducible.refl _),
    map_infinitePi_itinerary_piBasis hφ, itinerary_piBasis] at hx
  have hci := hBi.isComputableCantorMeasureIn_map (hμ.isComputableMeasureIn i)
    (isComputableRealFamilyIn_measure_univ _)
  have h1 : IsMartinLofRandomIn
      (oracleJoin A (seqOracle (cantorPiJoinSkip (fun j => itinerary B (x j)) i)))
      ((μ i).map (itinerary B)) (itinerary B (x i)) :=
    (isMartinLofRandomIn_oracleJoin_cantorPiJoinSkip_iff i).2
      (hx.coordinate_of_cantorPiJoin (μ := fun j => (μ j).map (itinerary B)) hci)
  have hy : itinerary (piBasis B) (fun j => x (skipIndex i j)) =
      cantorPiJoinSkip (fun j => itinerary B (x j)) i := by
    rw [itinerary_piBasis]
    rfl
  rw [← hy, ← hBi.mem_randomPoints_iff hP (oracle_joins A _)] at h1
  obtain ⟨a, ha, hle⟩ := hBpi.exists_isCauchyName_le_itinerary fun j => x (skipIndex i j)
  exact ⟨a, ha, randomPoints_anti_oracle P (μ i) hle h1⟩

/-- **Countable van Lambalgen, earlier coordinates.** Under the hypotheses of
`mem_randomPoints_coordinate_of_pi`, `x i` is `μ i`-random relative to `A ⊕ a` for some Cauchy
name `a` of the earlier coordinates `j ↦ if j < i then x j else P.ι 0`.
Blueprint node `vlm:countable-below`. -/
theorem mem_randomPoints_coordinate_of_pi_below (hP : ComputablePresentationIn P A)
    (hμ : IsComputableMeasureFamilyIn P A μ) {x : ℕ → X}
    (hx : x ∈ randomPoints P.pi A (Measure.infinitePi μ)) (i : ℕ) :
    ∃ a, IsCauchyName P.pi (fun j => if j < i then x j else P.ι 0) a ∧
      x i ∈ randomPoints P (oracleJoin A (nameOracle a)) (μ i) := by
  obtain ⟨a, ha, hxi⟩ := mem_randomPoints_coordinate_of_pi hP hμ hx i
  obtain ⟨b, hb, hle⟩ := exists_isCauchyName_pi_below (A := A) ha i
  have heq : (fun j => if j < i then x (skipIndex i j) else P.ι 0) =
      fun j => if j < i then x j else P.ι 0 := by
    funext j
    split_ifs with h
    · simp [skipIndex, h]
    · rfl
  rw [heq] at hb
  exact ⟨b, hb, randomPoints_anti_oracle P (μ i) hle hxi⟩

/-- Some sequence is random relative to `A` for the product of probability measures.
Blueprint node `vlm:countable-nonvacuous`. -/
theorem exists_mem_randomPoints_pi (P : Presentation X) (A : Set ℕ) :
    ∃ x : ℕ → X, x ∈ randomPoints P.pi A (Measure.infinitePi μ) := by
  have := P.secondCountableTopology
  obtain ⟨x, -, hx⟩ :=
    exists_mem_randomPoints_of_measure_pos P.pi A (Measure.infinitePi μ) (Z := Set.univ)
      (by simp)
  exact ⟨x, hx⟩

end Kolmogorov.PointToSet
