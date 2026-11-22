/-
Copyright (c) 2026 Emma Dinowitz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emma Dinowitz
-/
import KolmogorovMathlib.Trusted.StatementsDecomposition
import KolmogorovMathlib.Trusted.Bridge
import KolmogorovMathlib.PointToSet.Measure.Pointwise
import KolmogorovMathlib.PointToSet.Measure.IntegralAffinity
import KolmogorovMathlib.Ergodic.Jacobs

/-!
# Bridge: the decomposition statements follow from the library

Proofs of the statements of `KolmogorovMathlib.Trusted.StatementsDecomposition`:

* `theorem3_3_fixedScale` (from `PointToSet.orbitComplexityAt_le_localEntropyAt`),
* `theorem3_3_ae` (from `PointToSet.ae_orbitComplexities_eq_localEntropy`),
* `theorem7_3_a` (from `PointToSet.ae_compProd_localEntropy_le`),
* `theorem7_5_a` (from `PointToSet.ae_compProd_localEntropy_eq_of_absolutelyContinuous`),
* `theorem7_5_b` (from
  `PointToSet.ae_compProd_localEntropy_eq_ksEntropy_of_ergodicDecomposition`),
* `theorem7_5_b_fengHuang` (from
  `PointToSet.ae_compProd_localEntropy_eq_of_ergodicDecomposition`),
* `jacobsTheorem` (from `Ergodic.jacobs_ksEntropy_bind`),

through the equivalence lemmas of `KolmogorovMathlib.Trusted.Bridge` and the following ones:

* `lowerOrbitComplexityAt_eq`, `upperOrbitComplexityAt_eq`: the plain fixed-scale orbit
  complexities are `(orbitComplexityAt P T A y ε).1, .2`, for continuous `T` and `ε > 0`;
* `lowerLocalEntropyAt_eq`, `upperLocalEntropyAt_eq`: the plain fixed-scale local entropies are
  `(localEntropyAt μ T y ε).1, .2` (unconditionally);
* `lintegral_lowerLocalEntropy_eq`: `∫ h̲_ν(T, z) dν(z) = (measureEntropy ν T).1`;
* `measurePreserving_bind`: a mixture of a.e. invariant measures is invariant (used to apply
  the pilot's `ksEntropy_eq`, valid for invariant probability measures, to the mixture);
* `ae_compProd_of_ae_fst`: a property of `Q`-a.e. `ω` holds at `Q ⊗ κ`-a.e. `(ω, x)`;
* `aemeasurable_ksEntropy`: the plain `ω ↦ h_{κ ω}(T)` of Jacobs' theorem is a.e. measurable.
-/

namespace Kolmogorov.Trusted

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal

universe u v

/-! ### Fixed-scale notions -/

section FixedScale

variable {X : Type*} [MetricSpace X] (P : PointToSet.Presentation X) (A : Set ℕ)

/-- At a positive radius the plain `K̲^A(y, T, ε)` is the library's, for continuous `T`. -/
theorem lowerOrbitComplexityAt_eq {T : X → X} (hT : Continuous T) (y : X) {ε : ℝ}
    (hε : 0 < ε) :
    lowerOrbitComplexityAt P.ι T A y ε = (PointToSet.orbitComplexityAt P T A y ε).1 :=
  congrArg Prod.fst (orbitComplexityAt_eq P A hT y hε)

/-- At a positive radius the plain `K̄^A(y, T, ε)` is the library's, for continuous `T`. -/
theorem upperOrbitComplexityAt_eq {T : X → X} (hT : Continuous T) (y : X) {ε : ℝ}
    (hε : 0 < ε) :
    upperOrbitComplexityAt P.ι T A y ε = (PointToSet.orbitComplexityAt P T A y ε).2 :=
  congrArg Prod.snd (orbitComplexityAt_eq P A hT y hε)

variable [MeasurableSpace X]

/-- The plain `h̲_μ(T, y, ε)` is the library's. -/
theorem lowerLocalEntropyAt_eq (μ : Measure X) (T : X → X) (y : X) (ε : ℝ) :
    lowerLocalEntropyAt μ T y ε = (PointToSet.localEntropyAt μ T y ε).1 :=
  congrArg Prod.fst (localEntropyAt_eq μ T y ε)

/-- The plain `h̄_μ(T, y, ε)` is the library's. -/
theorem upperLocalEntropyAt_eq (μ : Measure X) (T : X → X) (y : X) (ε : ℝ) :
    upperLocalEntropyAt μ T y ε = (PointToSet.localEntropyAt μ T y ε).2 :=
  congrArg Prod.snd (localEntropyAt_eq μ T y ε)

/-- The mean lower local entropy is the first coordinate of the library's Feng–Huang entropy
`measureEntropy`. -/
theorem lintegral_lowerLocalEntropy_eq (ν : Measure X) (T : X → X) :
    ∫⁻ z, lowerLocalEntropy ν T z ∂ν = (PointToSet.measureEntropy ν T).1 := by
  simp only [lowerLocalEntropy_eq, PointToSet.measureEntropy]

end FixedScale

/-! ### Mixtures -/

section Mixture

variable {X : Type*} [MeasurableSpace X] {Ω : Type*} [MeasurableSpace Ω]

/-- A mixture `ρ.bind κ` of measures that are `T`-invariant for `ρ`-a.e. `ω` is `T`-invariant
(for `ρ ≠ 0`, which gives the measurability of `T`). -/
theorem measurePreserving_bind {ρ : Measure Ω} [NeZero ρ] {κ : Kernel Ω X} {T : X → X}
    (hinv : ∀ᵐ ω ∂ρ, MeasurePreserving T (κ ω) (κ ω)) :
    MeasurePreserving T (ρ.bind κ) (ρ.bind κ) := by
  obtain ⟨ω₀, hω₀⟩ := hinv.exists
  have hT := hω₀.measurable
  refine ⟨hT, ?_⟩
  ext s hs
  rw [Measure.map_apply hT hs, Measure.bind_apply (hT hs) κ.aemeasurable,
    Measure.bind_apply hs κ.aemeasurable]
  refine lintegral_congr_ae (hinv.mono fun ω hω ↦ ?_)
  change κ ω (T ⁻¹' s) = κ ω s
  rw [← Measure.map_apply hT hs, hω.map_eq]

/-- A property of `Q`-almost every `ω` holds at `Q ⊗ κ`-almost every `(ω, x)`. -/
theorem ae_compProd_of_ae_fst {Q : Measure Ω} [IsProbabilityMeasure Q] {κ : Kernel Ω X}
    [IsMarkovKernel κ] {r : Ω → Prop} (h : ∀ᵐ ω ∂Q, r ω) : ∀ᵐ p ∂(Q ⊗ₘ κ), r p.1 := by
  rw [← Measure.fst_compProd Q κ, Measure.fst] at h
  exact ae_of_ae_map measurable_fst.aemeasurable h

end Mixture

/-- On a compact metric space, the plain entropy `ω ↦ h_{κ ω}(T)` of a.e. invariant components
is almost everywhere measurable (from the library's `jacobs_aemeasurable_ksEntropy`). -/
theorem aemeasurable_ksEntropy {X : Type*} [MetricSpace X] [CompactSpace X] [MeasurableSpace X]
    [BorelSpace X] {Ω : Type*} [MeasurableSpace Ω] (ρ : Measure Ω) [IsProbabilityMeasure ρ]
    (κ : Kernel Ω X) [IsMarkovKernel κ] {T : X → X}
    (hinv : ∀ᵐ ω ∂ρ, MeasurePreserving T (κ ω) (κ ω)) :
    AEMeasurable (fun ω ↦ ksEntropy (κ ω) T) ρ :=
  (Ergodic.jacobs_aemeasurable_ksEntropy ρ κ hinv).congr
    (hinv.mono fun _ hω ↦ (ksEntropy_eq hω).symm)

/-! ### The statements -/

/-- [N, Theorem 3.3(i)] at a fixed scale, from `orbitComplexityAt_le_localEntropyAt`. -/
theorem theorem3_3_fixedScale : Theorem3_3_fixedScale.{u} := by
  intro X _ _ _ _ x T A μ hT hμ hA ε hε y
  have : IsFiniteMeasure μ := ⟨hμ.trans_lt ENNReal.one_lt_top⟩
  let P := toPresentation x hA.presentation.1
  have hA' : PointToSet.IsMeasureAdmissible P T μ A := (isAdmissible_iff P T μ).1 hA
  have h := PointToSet.orbitComplexityAt_le_localEntropyAt P T hT A μ hμ hA' ε hε y
  have h6 : (0 : ℝ) < 6 * (ε : ℝ) := by positivity
  have e1 : lowerOrbitComplexityAt x T A y (6 * ε) = _ := lowerOrbitComplexityAt_eq P A hT y h6
  have e2 : upperOrbitComplexityAt x T A y (6 * ε) = _ := upperOrbitComplexityAt_eq P A hT y h6
  rw [e1, e2, lowerLocalEntropyAt_eq, upperLocalEntropyAt_eq]
  exact h

/-- [N, Theorem 3.3], almost everywhere, from `ae_orbitComplexities_eq_localEntropy`. -/
theorem theorem3_3_ae : Theorem3_3_ae.{u} := by
  intro X _ _ _ _ x T A μ _ hT hA
  let P := toPresentation x hA.presentation.1
  have hA' : PointToSet.IsMeasureAdmissible P T μ A := (isAdmissible_iff P T μ).1 hA
  filter_upwards [PointToSet.ae_orbitComplexities_eq_localEntropy P T hT A μ hA'] with y hy
  have e1 : lowerOrbitComplexity x T A y = _ := lowerOrbitComplexity_eq P A hT y
  have e2 : upperOrbitComplexity x T A y = _ := upperOrbitComplexity_eq P A hT y
  rw [e1, e2, lowerLocalEntropy_eq, upperLocalEntropy_eq, hy]
  exact ⟨rfl, rfl⟩

/-- [N, Theorem 7.3(a)], from `ae_compProd_localEntropy_le`. -/
theorem theorem7_3_a : Theorem7_3_a.{u, v} := by
  intro X _ _ _ _ Ω _ T Q _ κ _ hT
  filter_upwards [PointToSet.ae_compProd_localEntropy_le hT Q κ] with p hp
  simp only [lowerLocalEntropy_eq, upperLocalEntropy_eq]
  exact hp

/-- [N, Theorem 7.5(a)], from `ae_compProd_localEntropy_eq_of_absolutelyContinuous`. -/
theorem theorem7_5_a : Theorem7_5_a.{u, v} := by
  intro X _ _ _ _ Ω _ T Q _ κ _ hT h
  filter_upwards [PointToSet.ae_compProd_localEntropy_eq_of_absolutelyContinuous hT Q κ h]
    with p hp
  simp only [lowerLocalEntropy_eq, upperLocalEntropy_eq]
  exact ⟨congrArg Prod.fst hp, congrArg Prod.snd hp⟩

/-- [N, Theorem 7.5(b)], from `ae_compProd_localEntropy_eq_ksEntropy_of_ergodicDecomposition`. -/
theorem theorem7_5_b : Theorem7_5_b.{u, v} := by
  intro X _ _ _ _ Ω _ T Q _ κ _ hT hinv herg
  filter_upwards [PointToSet.ae_compProd_localEntropy_eq_ksEntropy_of_ergodicDecomposition
    hT Q κ hinv herg, ae_compProd_of_ae_fst (κ := κ) herg] with p hp hpe
  simp only [lowerLocalEntropy_eq, upperLocalEntropy_eq, ksEntropy_eq hpe.toMeasurePreserving]
  rw [hp.2, hp.1]
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- [N, Theorem 7.5(b)] with the mean local entropy of the component, from
`ae_compProd_localEntropy_eq_of_ergodicDecomposition`. -/
theorem theorem7_5_b_fengHuang : Theorem7_5_b_fengHuang.{u, v} := by
  intro X _ _ _ _ Ω _ T Q _ κ _ hT hinv herg
  filter_upwards [PointToSet.ae_compProd_localEntropy_eq_of_ergodicDecomposition
    hT Q κ hinv herg] with p hp
  rw [lintegral_lowerLocalEntropy_eq]
  simp only [lowerLocalEntropy_eq, upperLocalEntropy_eq]
  rw [hp.2, hp.1]
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- Jacobs' theorem, from `Ergodic.jacobs_ksEntropy_bind`. -/
theorem jacobsTheorem : JacobsTheorem.{u, v} := by
  intro X _ _ _ _ Ω _ T ρ _ κ _ hinv
  have : IsProbabilityMeasure (ρ.bind κ) :=
    isProbabilityMeasure_bind κ.aemeasurable (Eventually.of_forall fun ω ↦ inferInstance)
  rw [ksEntropy_eq (measurePreserving_bind hinv),
    lintegral_congr_ae (hinv.mono fun ω hω ↦ ksEntropy_eq hω)]
  exact Ergodic.jacobs_ksEntropy_bind ρ κ hinv

end Kolmogorov.Trusted
