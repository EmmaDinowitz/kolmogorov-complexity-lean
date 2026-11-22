/-
Copyright (c) 2026 Emma Dinowitz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emma Dinowitz
-/
import KolmogorovMathlib.Trusted.StatementsShift
import KolmogorovMathlib.Trusted.Bridge
import KolmogorovMathlib.PointToSet.Measure.Ergodic.CantorInstances
import KolmogorovMathlib.PointToSet.Measure.Ergodic.ShiftKSEntropy
import KolmogorovMathlib.PointToSet.Measure.Ergodic.OrbitUpper
import KolmogorovMathlib.PointToSet.Measure.Ergodic.OrbitLower
import KolmogorovMathlib.PointToSet.Measure.ExampleFiveFive

/-!
# Bridge: the trusted shift statements follow from the library

Proofs of the statements of `KolmogorovMathlib.Trusted.StatementsShift`:

* `proposition7_10_i`, `proposition7_10_ii` (from `upperOrbitComplexity_le_shiftEntropy`,
  `orbitComplexities_eq_shiftEntropy`);
* `proposition7_10_i_cantor`, `proposition7_10_ii_cantor` (from
  `upperOrbitComplexity_le_shiftEntropy_cantor`, `orbitComplexities_eq_shiftEntropy_cantor`);
* `proposition7_10_i_ks`, `proposition7_10_ii_ks` (from
  `shiftKS_upperOrbitComplexity_le_ksEntropy`, `shiftKS_orbitComplexities_eq_ksEntropy`);
* `example5_5_1`, `example5_5_2` (from `exists_countable_atomic_random_upperLocalEntropy_eq_one`,
  `exists_random_lowerLocalEntropy_eq_zero`, with `ae_localEntropy_eq_zero_of_countable`,
  `localEntropy_eq_zero_of_measure_singleton_ne_zero` and `orbitComplexities_eq_localEntropy`
  for the derived conclusions);
* `theorem1_a`, `theorem1_b` (from `orbitComplexityAt_snd_le_ksEntropy`,
  `upperOrbitComplexity_le_ksEntropy`, `ksEntropy_le_lowerOrbitComplexity`).

Equivalences between the new plain definitions and the library's (the pilot bridge
`KolmogorovMathlib.Trusted.Bridge` supplies the others):

* `shift_eq`, `cylinder_eq`: `= shiftMap`, `= wordCylinder` (definitional);
* `isGeneric_iff`: `↔ IsGenericPoint`; `blockEntropy_eq`, `shiftEntropy_eq`: `= blockEntropy`,
  `= shiftEntropy` (definitional);
* `hasComputableSymbols_iff`: `↔` the library's hypothesis `hP` on the presentation;
* `cantorMetric_eq`: `= cantorMetricSpace`; `cantorIdeal_eq`: `= cantorPresentation.ι`
  (definitional); `hasComputableSymbols_cantorIdeal`: the standard ideal points have computable
  symbols relative to every oracle;
* `shiftEntropy_eq_ksEntropy`: for a shift-invariant probability measure, the plain
  `h_ν(σ) = inf_k H_ν(ξᵏ) / k` is the pilot's Kolmogorov–Sinai entropy `ksEntropy ν shift`.
-/

namespace Kolmogorov.Trusted

open MeasureTheory Filter Set
open scoped ENNReal Computability

universe u

/-! ### The shift -/

section Shift

variable {α : Type*}

/-- The plain shift is the library's `shiftMap`. -/
theorem shift_eq : (shift : (ℕ → α) → ℕ → α) = PointToSet.shiftMap :=
  rfl

/-- The plain cylinders are the library's `wordCylinder`. -/
theorem cylinder_eq {k : ℕ} (w : Fin k → α) : cylinder w = PointToSet.wordCylinder w :=
  rfl

/-- The plain symbol hypothesis is the library's hypothesis `hP` for the presentation given by
the ideal points. -/
theorem hasComputableSymbols_iff [Primcodable α] [MetricSpace (ℕ → α)] [CompleteSpace (ℕ → α)]
    (x : ℕ → ℕ → α) (hx : DenseRange x) (A : Set ℕ) :
    HasComputableSymbols x A ↔
      ComputableIn {charOracle A} fun q : ℕ × ℕ ↦ (toPresentation x hx).ι q.1 q.2 :=
  Iff.rfl

variable [MeasurableSpace (ℕ → α)]

/-- Plain generic points are the library's. -/
theorem isGeneric_iff (ν : Measure (ℕ → α)) (y : ℕ → α) :
    IsGeneric ν y ↔ PointToSet.IsGenericPoint ν y :=
  Iff.rfl

variable [Fintype α]

/-- The plain block entropy is the library's. -/
theorem blockEntropy_eq (ν : Measure (ℕ → α)) (k : ℕ) :
    blockEntropy ν k = PointToSet.blockEntropy ν k :=
  rfl

/-- The plain shift entropy `inf_{k ≥ 1} H_ν(ξᵏ) / k` is the library's. -/
theorem shiftEntropy_eq (ν : Measure (ℕ → α)) : shiftEntropy ν = PointToSet.shiftEntropy ν :=
  rfl

/-- For a shift-invariant probability measure on a shift with a first-difference metric, the
plain shift entropy is the pilot's Kolmogorov–Sinai entropy of the shift. -/
theorem shiftEntropy_eq_ksEntropy [MetricSpace (ℕ → α)] [BorelSpace (ℕ → α)] {β : ℝ}
    (hβ : 0 < β) (hβ₁ : β < 1)
    (hd : ∀ y z : ℕ → α, y ≠ z → dist y z = β ^ PiNat.firstDiff y z)
    (ν : Measure (ℕ → α)) [IsProbabilityMeasure ν] (hν : MeasurePreserving shift ν ν) :
    shiftEntropy ν = ksEntropy ν shift := by
  rw [ksEntropy_eq hν]
  exact PointToSet.shiftKS_shiftEntropy_eq_ksEntropy hβ hβ₁ hd ν hν

end Shift

/-! ### Cantor space -/

section Cantor

/-- The plain Cantor metric is the library's `cantorMetricSpace`. -/
theorem cantorMetric_eq : cantorMetric = PointToSet.cantorMetricSpace :=
  rfl

attribute [local instance] cantorMetric

/-- The plain standard ideal points of Cantor space are those of the library's
`cantorPresentation`. -/
theorem cantorIdeal_eq : cantorIdeal = PointToSet.cantorPresentation.ι :=
  rfl

/-- The standard ideal points of Cantor space have computable symbols, relative to every
oracle. -/
theorem hasComputableSymbols_cantorIdeal (A : Set ℕ) : HasComputableSymbols cantorIdeal A :=
  PointToSet.cantorPres_computableIn_symbols A

/-- The shift of Cantor space is continuous. -/
theorem continuous_shiftMap_cantorMetric :
    Continuous (PointToSet.shiftMap : (ℕ → Bool) → ℕ → Bool) :=
  PointToSet.continuous_shiftMap_cantor

end Cantor

/-! ### Proposition 7.10 -/

/-- [N, Proposition 7.10(i)], from `upperOrbitComplexity_le_shiftEntropy`. -/
theorem proposition7_10_i : Proposition7_10_i.{u} := by
  intro α _ _ _ _ _ β hβ hβ₁ hd x A hx hP ν _ hν y hy
  have : CompactSpace (ℕ → α) := PointToSet.vyuginGen_compactSpace hβ hβ₁ hd
  let P := toPresentation x hx
  have hT : Continuous (PointToSet.shiftMap : (ℕ → α) → ℕ → α) :=
    PointToSet.continuous_shiftMap hβ hβ₁ hd
  have e : upperOrbitComplexity x shift A y = _ := upperOrbitComplexity_eq P A hT y
  rw [e, shiftEntropy_eq]
  exact PointToSet.upperOrbitComplexity_le_shiftEntropy hβ hβ₁ hd P A hP ν hν hy

/-- [N, Proposition 7.10(ii)], from `orbitComplexities_eq_shiftEntropy`. -/
theorem proposition7_10_ii : Proposition7_10_ii.{u} := by
  intro α _ _ _ _ _ β hβ hβ₁ hd x ν _ hν A B hB hAB hP y hy
  have : CompactSpace (ℕ → α) := PointToSet.vyuginGen_compactSpace hβ hβ₁ hd
  let P := toPresentation x hB.presentation.1
  have hT : Continuous (PointToSet.shiftMap : (ℕ → α) → ℕ → α) :=
    PointToSet.continuous_shiftMap hβ hβ₁ hd
  have hB' : PointToSet.IsMeasureAdmissible P PointToSet.shiftMap ν B :=
    (isAdmissible_iff P _ ν).1 hB
  have hy' : y ∈ PointToSet.randomPoints P B ν := by
    rw [← mlRandom_eq]
    exact hy
  have h := PointToSet.orbitComplexities_eq_shiftEntropy hβ hβ₁ hd P ν hν hB' hy' hAB hP
  have e1 : lowerOrbitComplexity x shift A y = _ := lowerOrbitComplexity_eq P A hT y
  have e2 : upperOrbitComplexity x shift A y = _ := upperOrbitComplexity_eq P A hT y
  rw [e1, e2, h, shiftEntropy_eq]
  exact ⟨rfl, rfl⟩

/-- [N, Proposition 7.10(i)] in Kolmogorov–Sinai form, from
`shiftKS_upperOrbitComplexity_le_ksEntropy`. -/
theorem proposition7_10_i_ks : Proposition7_10_i_ks.{u} := by
  intro α _ _ _ _ _ β hβ hβ₁ hd x A hx hP ν _ hν y hy
  have : CompactSpace (ℕ → α) := PointToSet.vyuginGen_compactSpace hβ hβ₁ hd
  let P := toPresentation x hx
  have hT : Continuous (PointToSet.shiftMap : (ℕ → α) → ℕ → α) :=
    PointToSet.continuous_shiftMap hβ hβ₁ hd
  have e : upperOrbitComplexity x shift A y = _ := upperOrbitComplexity_eq P A hT y
  rw [e, ksEntropy_eq hν]
  exact PointToSet.shiftKS_upperOrbitComplexity_le_ksEntropy hβ hβ₁ hd P A hP ν hν hy

/-- [N, Proposition 7.10(ii)] in Kolmogorov–Sinai form, from
`shiftKS_orbitComplexities_eq_ksEntropy`. -/
theorem proposition7_10_ii_ks : Proposition7_10_ii_ks.{u} := by
  intro α _ _ _ _ _ β hβ hβ₁ hd x ν _ hν A B hB hAB hP y hy
  have : CompactSpace (ℕ → α) := PointToSet.vyuginGen_compactSpace hβ hβ₁ hd
  let P := toPresentation x hB.presentation.1
  have hT : Continuous (PointToSet.shiftMap : (ℕ → α) → ℕ → α) :=
    PointToSet.continuous_shiftMap hβ hβ₁ hd
  have hB' : PointToSet.IsMeasureAdmissible P PointToSet.shiftMap ν B :=
    (isAdmissible_iff P _ ν).1 hB
  have hy' : y ∈ PointToSet.randomPoints P B ν := by
    rw [← mlRandom_eq]
    exact hy
  have h := PointToSet.shiftKS_orbitComplexities_eq_ksEntropy hβ hβ₁ hd P ν hν hB' hy' hAB hP
  have e1 : lowerOrbitComplexity x shift A y = _ := lowerOrbitComplexity_eq P A hT y
  have e2 : upperOrbitComplexity x shift A y = _ := upperOrbitComplexity_eq P A hT y
  rw [e1, e2, h, ksEntropy_eq hν.toMeasurePreserving]
  exact ⟨rfl, rfl⟩

section Cantor

attribute [local instance] cantorMetric

/-- [N, Proposition 7.10(i)] on Cantor space, from
`upperOrbitComplexity_le_shiftEntropy_cantor`. -/
theorem proposition7_10_i_cantor : Proposition7_10_i_cantor := by
  intro A ν _ hν y hy
  have e : upperOrbitComplexity cantorIdeal shift A y = _ :=
    upperOrbitComplexity_eq PointToSet.cantorPresentation A continuous_shiftMap_cantorMetric y
  rw [e, shiftEntropy_eq]
  exact PointToSet.upperOrbitComplexity_le_shiftEntropy_cantor A ν hν hy

/-- [N, Proposition 7.10(ii)] on Cantor space, from `orbitComplexities_eq_shiftEntropy_cantor`. -/
theorem proposition7_10_ii_cantor : Proposition7_10_ii_cantor := by
  intro ν _ hν A B hB hAB y hy
  have hB' : PointToSet.IsMeasureAdmissible PointToSet.cantorPresentation PointToSet.shiftMap ν B :=
    (isAdmissible_iff PointToSet.cantorPresentation _ ν).1 hB
  have hy' : y ∈ PointToSet.randomPoints PointToSet.cantorPresentation B ν := by
    rw [← mlRandom_eq]
    exact hy
  have h := PointToSet.orbitComplexities_eq_shiftEntropy_cantor ν hν hB' hy' hAB
  have e1 : lowerOrbitComplexity cantorIdeal shift A y = _ :=
    lowerOrbitComplexity_eq PointToSet.cantorPresentation A continuous_shiftMap_cantorMetric y
  have e2 : upperOrbitComplexity cantorIdeal shift A y = _ :=
    upperOrbitComplexity_eq PointToSet.cantorPresentation A continuous_shiftMap_cantorMetric y
  rw [e1, e2, h, shiftEntropy_eq]
  exact ⟨rfl, rfl⟩

/-! ### Example 5.5 -/

/-- [N, Example 5.5(1)], from `exists_countable_atomic_random_upperLocalEntropy_eq_one`. -/
theorem example5_5_1 : Example5_5_1 := by
  obtain ⟨μ, hμ, hA, ⟨S, hS, hSμ⟩, z, hz, hz1⟩ :=
    PointToSet.exists_countable_atomic_random_upperLocalEntropy_eq_one
  have hA' : IsAdmissible cantorIdeal shift μ ∅ :=
    (isAdmissible_iff PointToSet.cantorPresentation _ μ).2 hA
  have hz' : z ∈ MLRandom cantorIdeal ∅ μ := by
    rw [show MLRandom cantorIdeal ∅ μ = _ from mlRandom_eq PointToSet.cantorPresentation μ]
    exact hz
  have hup : upperLocalEntropy μ shift z = 1 := by
    rw [upperLocalEntropy_eq]
    exact hz1
  refine ⟨μ, hμ, hA', ⟨S, hS, hSμ⟩, ?_, z, hz', ?_, hup, ?_⟩
  · filter_upwards [PointToSet.ae_localEntropy_eq_zero_of_countable μ PointToSet.shiftMap hS hSμ]
      with y hy
    rw [lowerLocalEntropy_eq, upperLocalEntropy_eq, shift_eq, hy]
    exact ⟨rfl, rfl⟩
  · by_contra h
    rw [upperLocalEntropy_eq, PointToSet.localEntropy_eq_zero_of_measure_singleton_ne_zero μ _ h]
      at hup
    exact zero_ne_one hup
  · have e : upperOrbitComplexity cantorIdeal shift ∅ z = _ :=
      upperOrbitComplexity_eq PointToSet.cantorPresentation ∅ continuous_shiftMap_cantorMetric z
    rw [e, PointToSet.orbitComplexities_eq_localEntropy PointToSet.cantorPresentation _
      continuous_shiftMap_cantorMetric ∅ μ hA hz]
    exact hz1

/-- [N, Example 5.5(2)], from `exists_random_lowerLocalEntropy_eq_zero`. -/
theorem example5_5_2 : Example5_5_2 := by
  obtain ⟨μ, hμ, hA, hae, z, hz, hz0⟩ := PointToSet.exists_random_lowerLocalEntropy_eq_zero
  have hA' : IsAdmissible cantorIdeal shift μ ∅ :=
    (isAdmissible_iff PointToSet.cantorPresentation _ μ).2 hA
  have hz' : z ∈ MLRandom cantorIdeal ∅ μ := by
    rw [show MLRandom cantorIdeal ∅ μ = _ from mlRandom_eq PointToSet.cantorPresentation μ]
    exact hz
  refine ⟨μ, hμ, hA', ?_, z, hz', ?_, ?_⟩
  · filter_upwards [hae] with y hy
    rw [lowerLocalEntropy_eq, upperLocalEntropy_eq, shift_eq, hy]
    exact ⟨rfl, rfl⟩
  · rw [lowerLocalEntropy_eq]
    exact hz0
  · have e : lowerOrbitComplexity cantorIdeal shift ∅ z = _ :=
      lowerOrbitComplexity_eq PointToSet.cantorPresentation ∅ continuous_shiftMap_cantorMetric z
    rw [e, PointToSet.orbitComplexities_eq_localEntropy PointToSet.cantorPresentation _
      continuous_shiftMap_cantorMetric ∅ μ hA hz]
    exact hz0

end Cantor

/-! ### The companion Theorem 1(a), (b) -/

/-- [C, Theorem 1(a)], from `orbitComplexityAt_snd_le_ksEntropy` and
`upperOrbitComplexity_le_ksEntropy`. -/
theorem theorem1_a : Theorem1_a.{u} := by
  intro X _ _ _ _ x T A μ _ hT hA herg y hy
  let P := toPresentation x hA.presentation.1
  have hA' : PointToSet.IsMeasureAdmissible P T μ A := (isAdmissible_iff P T μ).1 hA
  have hy' : y ∈ PointToSet.randomPoints P A μ := by
    rw [← mlRandom_eq]
    exact hy
  rw [ksEntropy_eq herg.toMeasurePreserving]
  refine ⟨fun ε hε ↦ ?_, ?_⟩
  · have e := congrArg Prod.snd (orbitComplexityAt_eq P A hT y hε)
    exact e.le.trans (PointToSet.orbitComplexityAt_snd_le_ksEntropy P T hT A μ hA' herg hy' hε)
  · have e : upperOrbitComplexity x T A y = _ := upperOrbitComplexity_eq P A hT y
    rw [e]
    exact PointToSet.upperOrbitComplexity_le_ksEntropy P T hT A μ hA' herg hy'

/-- [C, Theorem 1(b)], from `ksEntropy_le_lowerOrbitComplexity`. -/
theorem theorem1_b : Theorem1_b.{u} := by
  intro X _ _ _ _ x T A μ _ hT hA herg y hy
  let P := toPresentation x hA.presentation.1
  have hA' : PointToSet.IsMeasureAdmissible P T μ A := (isAdmissible_iff P T μ).1 hA
  have hy' : y ∈ PointToSet.randomPoints P A μ := by
    rw [← mlRandom_eq]
    exact hy
  have e : lowerOrbitComplexity x T A y = _ := lowerOrbitComplexity_eq P A hT y
  rw [ksEntropy_eq herg.toMeasurePreserving, e]
  exact PointToSet.ksEntropy_le_lowerOrbitComplexity P T hT A μ hA' herg hy'

end Kolmogorov.Trusted
