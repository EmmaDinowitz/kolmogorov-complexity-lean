/-
Copyright (c) 2026 Emma Dinowitz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emma Dinowitz
-/
import KolmogorovMathlib.PointToSet.Measure.Pointwise
import KolmogorovMathlib.PointToSet.Measure.Decomposition
import KolmogorovMathlib.PointToSet.BSDimension.Upper.PointToSetPrinciple
import Mathlib.MeasureTheory.Function.EssSup

/-!
# The universal map and statistics of the entropy law (§6)

The pair of orbit complexities `Ψ^A = orbitComplexities P T A` involves no measure, and the
entropy law of every measure that `A` computes is its pushforward under `Ψ^A` (E. Dinowitz,
*Entropy of non-invariant measures and orbit complexity of random points*, Proposition 6.2).
The Feng–Huang entropies and the essential bounds of the local entropies are statistics of the
entropy law (Corollary 6.5(a), (b)).

* `orbitComplexities_mono_oracle` (Proposition 6.2(i)): `Ψ^B ≤ Ψ^A` when `B ≥_T A`.
* `entropyLaw_eq_map_orbitComplexities` (Proposition 6.2(ii)): `Λ_μ = (Ψ^A)_* μ`.
* `localEntropy_le_orbitComplexities_of_mem_randomPoints` (Remark 3.5): if `A` does not
  compute `μ` the lower bound survives at the points random relative to a stronger admissible
  oracle.
* `measureEntropy_eq_lintegral_entropyLaw` (Corollary 6.5(a)): the Feng–Huang entropies are
  the means of the marginals of `Λ_μ`.
* `essSup_localEntropy_eq_essSup_entropyLaw`, `essSup_localEntropy_sum`,
  `essInf_localEntropy_sum` (Corollary 6.5(b)): the essential bounds are those of the
  marginals of `Λ_μ`, and on countable convex combinations they are suprema and infima.

Blueprint nodes `meas:universal-map`, `meas:statistics`.
-/

namespace Kolmogorov.PointToSet

open Filter Set MeasureTheory
open scoped Topology ENNReal Computability

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

omit [MeasurableSpace X] [BorelSpace X] in
/-- Proposition 6.2(i): the orbit complexities decrease when the oracle is strengthened.
Blueprint node `meas:universal-map`. -/
theorem orbitComplexities_mono_oracle (P : Presentation X) (T : X → X) {A B : Set ℕ}
    (hAB : charOracle A ≤ᵀ charOracle B) (x : X) :
    (orbitComplexities P T B x).1 ≤ (orbitComplexities P T A x).1 ∧
      (orbitComplexities P T B x).2 ≤ (orbitComplexities P T A x).2 := by
  have hu : UniformContinuous (fun _ : X ↦ (1 : ℝ)) := uniformContinuous_const
  have hpos : 0 < lowerBirkhoffAverage T (fun _ ↦ (1 : ℝ)) x := by
    have hev : (fun n : ℕ ↦ ((birkhoffSum T (fun _ ↦ (1 : ℝ)) n x / n : ℝ) : EReal)) =ᶠ[atTop]
        fun _ ↦ (1 : EReal) := by
      filter_upwards [eventually_ge_atTop 1] with n hn
      have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.one_le_iff_ne_zero.1 hn)
      simp [birkhoffSum, hn']
    rw [lowerBirkhoffAverage, liminf_congr hev, liminf_const]
    exact zero_lt_one
  exact ⟨bsPointToSet_mono_oracle P T _ hu A B hAB x hpos LimitSide.lower,
    bsPointToSet_mono_oracle P T _ hu A B hAB x hpos LimitSide.upper⟩

/-- Proposition 6.2(ii): the entropy law of a measure computed by `A` is its image under the
universal map `Ψ^A`. Blueprint node `meas:universal-map`. -/
theorem entropyLaw_eq_map_orbitComplexities (P : Presentation X) (T : X → X)
    (hT : Continuous T) (A : Set ℕ) (μ : Measure X) [IsProbabilityMeasure μ]
    (hA : IsMeasureAdmissible P T μ A) :
    entropyLaw μ T = Measure.map (orbitComplexities P T A) μ := by
  exact Measure.map_congr ((ae_orbitComplexities_eq_localEntropy P T hT A μ hA).mono
    fun _ hx ↦ hx.symm)

/-- Remark 3.5: if `B ≥_T A` is admissible for `(X, d, T, μ)`, then at every point random
relative to `B` the orbit complexities relative to `A` are at least the local entropies.
Blueprint node `meas:universal-map`. -/
theorem localEntropy_le_orbitComplexities_of_mem_randomPoints (P : Presentation X) (T : X → X)
    (hT : Continuous T) {A B : Set ℕ} (hAB : charOracle A ≤ᵀ charOracle B) (μ : Measure X)
    [IsProbabilityMeasure μ] (hB : IsMeasureAdmissible P T μ B) {x : X}
    (hx : x ∈ randomPoints P B μ) :
    (localEntropy μ T x).1 ≤ (orbitComplexities P T A x).1 ∧
      (localEntropy μ T x).2 ≤ (orbitComplexities P T A x).2 := by
  rw [← orbitComplexities_eq_localEntropy P T hT B μ hB hx]
  exact orbitComplexities_mono_oracle P T hAB x

section statistics

variable [SecondCountableTopology X]

omit [MetricSpace X] [BorelSpace X] in
/-- The essential infimum of `g` under a pushforward measure `f_* μ` is that of `g ∘ f`
under `μ`, for measurable `f` and `g`. -/
private lemma essInf_map_of_measurable {γ : Type*} [MeasurableSpace γ] {μ : Measure X}
    {f : X → γ} {g : γ → ℝ≥0∞} (hg : Measurable g) (hf : Measurable f) :
    essInf g (Measure.map f μ) = essInf (g ∘ f) μ := by
  simp only [essInf, liminf_eq]
  congr 1
  ext c
  exact ae_map_iff hf.aemeasurable (measurableSet_le measurable_const hg)

omit [MetricSpace X] [BorelSpace X] in
/-- A set is null for a countable combination `∑_j t_j μ_j` with all `t_j ≠ 0` iff it is
`μ_j`-null for every `j`: each `μ_j` is absolutely continuous with respect to the sum. -/
private lemma absolutelyContinuous_sum_smul {ι : Type*} (t : ι → ℝ≥0∞) (μs : ι → Measure X)
    (ht : ∀ j, t j ≠ 0) (j : ι) : μs j ≪ Measure.sum fun j ↦ t j • μs j :=
  (Measure.absolutelyContinuous_smul (ht j)).trans
    (Measure.absolutelyContinuous_of_le (Measure.le_sum (fun j ↦ t j • μs j) j))

omit [MetricSpace X] [BorelSpace X] in
/-- The essential supremum under `∑_j t_j μ_j` (all `t_j ≠ 0`) is the supremum over `j` of the
essential suprema under `μ_j`. -/
lemma essSup_sum_measure {ι : Type*} [Countable ι] (t : ι → ℝ≥0∞) (μs : ι → Measure X)
    (ht : ∀ j, t j ≠ 0) (f : X → ℝ≥0∞) :
    essSup f (Measure.sum fun j ↦ t j • μs j) = ⨆ j, essSup f (μs j) := by
  refine le_antisymm (essSup_le_of_ae_le _ ?_)
    (iSup_le fun j ↦ essSup_mono_measure (absolutelyContinuous_sum_smul t μs ht j))
  refine Measure.ae_sum_iff.2 fun j ↦ (Measure.ae_ennreal_smul_measure_iff (ht j)).2 ?_
  filter_upwards [ENNReal.ae_le_essSup (μ := μs j) f] with x hx
  exact hx.trans (le_iSup (fun j ↦ essSup f (μs j)) j)

omit [MetricSpace X] [BorelSpace X] in
/-- The essential infimum under `∑_j t_j μ_j` (all `t_j ≠ 0`) is the infimum over `j` of the
essential infima under `μ_j`. -/
lemma essInf_sum_measure {ι : Type*} [Countable ι] (t : ι → ℝ≥0∞) (μs : ι → Measure X)
    (ht : ∀ j, t j ≠ 0) (f : X → ℝ≥0∞) :
    essInf f (Measure.sum fun j ↦ t j • μs j) = ⨅ j, essInf f (μs j) := by
  refine le_antisymm
    (le_iInf fun j ↦ essInf_antitone_measure (absolutelyContinuous_sum_smul t μs ht j))
    (le_essInf_of_ae_le _ ?_)
  refine Measure.ae_sum_iff.2 fun j ↦ (Measure.ae_ennreal_smul_measure_iff (ht j)).2 ?_
  filter_upwards [ae_essInf_le (μ := μs j) (f := f)] with x hx
  exact (iInf_le (fun j ↦ essInf f (μs j)) j).trans hx

omit [SecondCountableTopology X] in
/-- Corollary 6.5(a): the Feng–Huang entropies are the means of the two marginals of the
entropy law. Blueprint node `meas:statistics`. -/
theorem measureEntropy_eq_lintegral_entropyLaw {T : X → X} (hT : Continuous T)
    (μ : Measure X) :
    (measureEntropy μ T).1 = ∫⁻ p, p.1 ∂entropyLaw μ T ∧
      (measureEntropy μ T).2 = ∫⁻ p, p.2 ∂entropyLaw μ T := by
  simp only [measureEntropy, entropyLaw]
  exact ⟨(lintegral_map measurable_fst (measurable_localEntropy μ hT)).symm,
    (lintegral_map measurable_snd (measurable_localEntropy μ hT)).symm⟩

omit [SecondCountableTopology X] in
/-- Corollary 6.5(b): the essential suprema and infima of the local entropies are those of the
coordinates under the entropy law. Blueprint node `meas:statistics`. -/
theorem essSup_localEntropy_eq_essSup_entropyLaw {T : X → X} (hT : Continuous T)
    (μ : Measure X) :
    (essSup (fun x ↦ (localEntropy μ T x).1) μ = essSup Prod.fst (entropyLaw μ T) ∧
        essSup (fun x ↦ (localEntropy μ T x).2) μ = essSup Prod.snd (entropyLaw μ T)) ∧
      essInf (fun x ↦ (localEntropy μ T x).1) μ = essInf Prod.fst (entropyLaw μ T) ∧
        essInf (fun x ↦ (localEntropy μ T x).2) μ = essInf Prod.snd (entropyLaw μ T) := by
  have hf := measurable_localEntropy μ hT
  exact ⟨⟨(essSup_map_measure_of_measurable measurable_fst hf.aemeasurable).symm,
    (essSup_map_measure_of_measurable measurable_snd hf.aemeasurable).symm⟩,
    (essInf_map_of_measurable measurable_fst hf).symm,
    (essInf_map_of_measurable measurable_snd hf).symm⟩

/-- Corollary 6.5(b): on a countable combination `μ = ∑_j t_j μ_j` with all `t_j > 0` the
essential suprema of the local entropies are the suprema over `j` of those of `μ_j`.
Blueprint node `meas:statistics`. -/
theorem essSup_localEntropy_sum {T : X → X} (hT : Continuous T) {ι : Type*} [Countable ι]
    (t : ι → ℝ≥0∞) (μs : ι → Measure X) [∀ j, IsFiniteMeasure (μs j)]
    [IsFiniteMeasure (Measure.sum fun j ↦ t j • μs j)] (ht : ∀ j, t j ≠ 0) :
    essSup (fun x ↦ (localEntropy (Measure.sum fun j ↦ t j • μs j) T x).1)
          (Measure.sum fun j ↦ t j • μs j) =
        ⨆ j, essSup (fun x ↦ (localEntropy (μs j) T x).1) (μs j) ∧
      essSup (fun x ↦ (localEntropy (Measure.sum fun j ↦ t j • μs j) T x).2)
          (Measure.sum fun j ↦ t j • μs j) =
        ⨆ j, essSup (fun x ↦ (localEntropy (μs j) T x).2) (μs j) := by
  refine ⟨?_, ?_⟩ <;> rw [essSup_sum_measure t μs ht] <;> refine iSup_congr fun j ↦ ?_ <;>
    refine essSup_congr_ae ?_ <;>
    filter_upwards [ae_localEntropy_eq_of_sum hT t μs ht j] with x hx <;> rw [hx]

/-- Corollary 6.5(b): on a countable combination `μ = ∑_j t_j μ_j` with all `t_j > 0` the
essential infima of the local entropies are the infima over `j` of those of
`μ_j`. Blueprint node `meas:statistics`. -/
theorem essInf_localEntropy_sum {T : X → X} (hT : Continuous T) {ι : Type*} [Countable ι]
    (t : ι → ℝ≥0∞) (μs : ι → Measure X) [∀ j, IsFiniteMeasure (μs j)]
    [IsFiniteMeasure (Measure.sum fun j ↦ t j • μs j)] (ht : ∀ j, t j ≠ 0) :
    essInf (fun x ↦ (localEntropy (Measure.sum fun j ↦ t j • μs j) T x).1)
          (Measure.sum fun j ↦ t j • μs j) =
        ⨅ j, essInf (fun x ↦ (localEntropy (μs j) T x).1) (μs j) ∧
      essInf (fun x ↦ (localEntropy (Measure.sum fun j ↦ t j • μs j) T x).2)
          (Measure.sum fun j ↦ t j • μs j) =
        ⨅ j, essInf (fun x ↦ (localEntropy (μs j) T x).2) (μs j) := by
  refine ⟨?_, ?_⟩ <;> rw [essInf_sum_measure t μs ht] <;> refine iInf_congr fun j ↦ ?_ <;>
    refine essInf_congr_ae ?_ <;>
    filter_upwards [ae_localEntropy_eq_of_sum hT t μs ht j] with x hx <;> rw [hx]

end statistics

end Kolmogorov.PointToSet
