/-
Copyright (c) 2026 Emma Dinowitz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emma Dinowitz
-/
import KolmogorovMathlib.Ergodic.Jacobs
import KolmogorovMathlib.PointToSet.Measure.Ergodic.BernoulliRandom
import KolmogorovMathlib.PointToSet.Measure.RemarksShift

/-!
# The Feng–Huang entropy of an invariant measure is its Kolmogorov–Sinai entropy

Consequences of Jacobs' theorem (`Kolmogorov.Ergodic.jacobs_ksEntropy_bind`) for the chapter
*Entropy of non-invariant measures and orbit complexity of random points*, on a compact metric
space with a continuous map `T`.

* `jacobs_measureEntropy_bind_eq_lintegral_ksEntropy`: along an ergodic decomposition
  `μ = ∫ κ ω dQ(ω)`, both Feng–Huang entropies of `μ` equal `∫ h_{κ ω}(T) dQ(ω)` (Theorem 7.5(b),
  `ae_compProd_localEntropy_eq_ksEntropy_of_ergodicDecomposition`, integrated).
* `jacobs_measureEntropy_eq_ksEntropy_of_measurePreserving` (Remark 6.7, the mean of `Λ_μ`): for
  every invariant Borel probability measure `μ`, `h̲_μ(T) = h̄_μ(T) = h_μ(T)`, the
  Kolmogorov–Sinai entropy. Proof: the previous item for the ergodic decomposition
  (`exists_ergodicDecomposition`) and Jacobs' theorem. This removes the tautological reading of
  "the mean of `Λ_μ` is `h_μ(T)`" in `RemarksShift`
  (`measureEntropy_fst_eq_snd_of_measurePreserving`).
* Remark 6.7 with the Kolmogorov–Sinai entropy: the mean of the entropy law
  (`jacobs_lintegral_entropyLaw_fst`, `_snd`), the ergodic case
  (`jacobs_entropyLaw_eq_dirac_ksEntropy_of_ergodic`), countable ergodic mixtures
  (`jacobs_entropyLaw_sum_ergodic_ksEntropy`) and ergodic decompositions
  (`jacobs_entropyLaw_eq_map_ksEntropy_of_ergodicDecomposition`).
* Example 5.3 (`jacobs_ksEntropy_bernoulliMixture`): `h_μ(σ) = (H(p) + H(q))/2` for the mixture
  `μ = ½ (ν_p + ν_q)` of two Bernoulli measures, from `measureEntropy_bernoulliMixture`.

Blueprint node `erg:jacobs`.
-/

namespace Kolmogorov.PointToSet

open Filter Set MeasureTheory ProbabilityTheory
open scoped Topology ENNReal NNReal

section General

variable {X : Type*} [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
  {Ω : Type*} [MeasurableSpace Ω]

/-- Along an ergodic decomposition `μ = ∫ κ ω dQ(ω)` (`κ ω` ergodic for `Q`-a.e. `ω`), both
Feng–Huang entropies of `μ` are the mean Kolmogorov–Sinai entropy of the components.
Blueprint node `erg:jacobs`. -/
theorem jacobs_measureEntropy_bind_eq_lintegral_ksEntropy {T : X → X} (hT : Continuous T)
    (Q : Measure Ω) [IsProbabilityMeasure Q] (κ : Kernel Ω X) [IsMarkovKernel κ]
    (hinv : MeasurePreserving T (Q.bind κ) (Q.bind κ)) (herg : ∀ᵐ ω ∂Q, Ergodic T (κ ω)) :
    measureEntropy (Q.bind κ) T =
      (∫⁻ ω, Ergodic.ksEntropy (κ ω) T ∂Q, ∫⁻ ω, Ergodic.ksEntropy (κ ω) T ∂Q) := by
  have h := Measure.ae_ae_of_ae_compProd
    (ae_compProd_localEntropy_eq_ksEntropy_of_ergodicDecomposition hT Q κ hinv herg)
  have hm := measurable_localEntropy (Q.bind κ) hT
  have key : ∀ f : ℝ≥0∞ × ℝ≥0∞ → ℝ≥0∞, Measurable f → (∀ c, f (c, c) = c) →
      ∫⁻ x, f (localEntropy (Q.bind κ) T x) ∂(Q.bind κ) =
        ∫⁻ ω, Ergodic.ksEntropy (κ ω) T ∂Q := by
    intro f hf hfc
    rw [Measure.lintegral_bind (f := fun x ↦ f (localEntropy (Q.bind κ) T x))
      κ.measurable.aemeasurable (hf.comp hm).aemeasurable]
    refine lintegral_congr_ae (h.mono fun ω hω ↦ ?_)
    change ∫⁻ x, f (localEntropy (Q.bind κ) T x) ∂κ ω = Ergodic.ksEntropy (κ ω) T
    rw [lintegral_congr_ae (g := fun _ ↦ Ergodic.ksEntropy (κ ω) T)
      (hω.mono fun x hx ↦ by simp only [hx.1, hfc]), lintegral_const, measure_univ, mul_one]
  exact Prod.ext (key Prod.fst measurable_fst fun _ ↦ rfl)
    (key Prod.snd measurable_snd fun _ ↦ rfl)

/-- Along an ergodic decomposition, both Feng–Huang entropies of the mixture equal its
Kolmogorov–Sinai entropy (Theorem 7.5(b) and Jacobs' theorem). Blueprint node `erg:jacobs`. -/
theorem jacobs_measureEntropy_bind_eq_ksEntropy {T : X → X} (hT : Continuous T)
    (Q : Measure Ω) [IsProbabilityMeasure Q] (κ : Kernel Ω X) [IsMarkovKernel κ]
    (hinv : MeasurePreserving T (Q.bind κ) (Q.bind κ)) (herg : ∀ᵐ ω ∂Q, Ergodic T (κ ω)) :
    measureEntropy (Q.bind κ) T =
      (Ergodic.ksEntropy (Q.bind κ) T, Ergodic.ksEntropy (Q.bind κ) T) := by
  rw [jacobs_measureEntropy_bind_eq_lintegral_ksEntropy hT Q κ hinv herg,
    Ergodic.jacobs_ksEntropy_bind Q κ (herg.mono fun _ h ↦ h.toMeasurePreserving)]

/-- Remark 6.7, the mean of the entropy law (audit, fix 3): for a continuous map of a compact
metric space and an invariant Borel probability measure `μ`, both Feng–Huang entropies equal the
Kolmogorov–Sinai entropy, `h̲_μ(T) = h̄_μ(T) = h_μ(T)`. No finiteness or ergodicity is assumed.
Proof: the ergodic decomposition, Theorem 7.5(b) and Jacobs' theorem.
Blueprint node `erg:jacobs`. -/
theorem jacobs_measureEntropy_eq_ksEntropy_of_measurePreserving {T : X → X}
    (hT : Continuous T) (μ : Measure X) [IsProbabilityMeasure μ]
    (hμ : MeasurePreserving T μ μ) :
    measureEntropy μ T = (Ergodic.ksEntropy μ T, Ergodic.ksEntropy μ T) := by
  obtain ⟨κ, hκ, hbind, herg⟩ := Ergodic.exists_ergodicDecomposition hT μ hμ
  have hinv : MeasurePreserving T (μ.bind κ) (μ.bind κ) := by rw [hbind]; exact hμ
  have h := jacobs_measureEntropy_bind_eq_ksEntropy hT μ κ hinv herg
  rwa [hbind] at h

/-- Remark 6.7: the mean of the first marginal of the entropy law `Λ_μ` of an invariant measure
is the Kolmogorov–Sinai entropy. Blueprint node `erg:jacobs`. -/
theorem jacobs_lintegral_entropyLaw_fst {T : X → X} (hT : Continuous T) (μ : Measure X)
    [IsProbabilityMeasure μ] (hμ : MeasurePreserving T μ μ) :
    ∫⁻ p, p.1 ∂entropyLaw μ T = Ergodic.ksEntropy μ T := by
  rw [entropyLaw, lintegral_map measurable_fst (measurable_localEntropy μ hT)]
  exact congrArg Prod.fst (jacobs_measureEntropy_eq_ksEntropy_of_measurePreserving hT μ hμ)

/-- Remark 6.7: the mean of the second marginal of the entropy law `Λ_μ` of an invariant measure
is the Kolmogorov–Sinai entropy. Blueprint node `erg:jacobs`. -/
theorem jacobs_lintegral_entropyLaw_snd {T : X → X} (hT : Continuous T) (μ : Measure X)
    [IsProbabilityMeasure μ] (hμ : MeasurePreserving T μ μ) :
    ∫⁻ p, p.2 ∂entropyLaw μ T = Ergodic.ksEntropy μ T := by
  rw [entropyLaw, lintegral_map measurable_snd (measurable_localEntropy μ hT)]
  exact congrArg Prod.snd (jacobs_measureEntropy_eq_ksEntropy_of_measurePreserving hT μ hμ)

/-- Remark 6.7 for an ergodic measure, with the Kolmogorov–Sinai entropy: the entropy law is the
point mass `δ_{(h_μ(T), h_μ(T))}`. Blueprint node `erg:jacobs`. -/
theorem jacobs_entropyLaw_eq_dirac_ksEntropy_of_ergodic {T : X → X} (hT : Continuous T)
    (μ : Measure X) [IsProbabilityMeasure μ] (hμ : Ergodic T μ) :
    entropyLaw μ T = Measure.dirac (Ergodic.ksEntropy μ T, Ergodic.ksEntropy μ T) := by
  rw [entropyLaw, Measure.map_congr (ae_localEntropy_eq_ksEntropy hT μ hμ),
    Measure.map_const, measure_univ, one_smul]

/-- Remark 6.7 for countably many ergodic components, with the Kolmogorov–Sinai entropy: if
`μ = ∑_j t_j μ_j` with all `t_j > 0` and every `μ_j` ergodic, then
`Λ_μ = ∑_j t_j δ_{(h_{μ_j}(T), h_{μ_j}(T))}`. Blueprint node `erg:jacobs`. -/
theorem jacobs_entropyLaw_sum_ergodic_ksEntropy {T : X → X} (hT : Continuous T) {ι : Type*}
    [Countable ι] (t : ι → ℝ≥0∞) (μs : ι → Measure X) [∀ j, IsProbabilityMeasure (μs j)]
    [IsFiniteMeasure (Measure.sum fun j ↦ t j • μs j)] (ht : ∀ j, t j ≠ 0)
    (herg : ∀ j, Ergodic T (μs j)) :
    entropyLaw (Measure.sum fun j ↦ t j • μs j) T =
      Measure.sum fun j ↦
        t j • Measure.dirac (Ergodic.ksEntropy (μs j) T, Ergodic.ksEntropy (μs j) T) := by
  rw [entropyLaw_sum_ergodic hT t μs ht herg]
  congr 1
  funext j
  rw [measureEntropy_eq_ksEntropy hT (μs j) (herg j)]

/-- Remark 6.7, last sentence, with the Kolmogorov–Sinai entropy: along an ergodic decomposition
`μ = ∫ κ ω dQ(ω)`, `Λ_μ` is the law of `(h_{κ ω}(T), h_{κ ω}(T))` under `M = Q ⊗ κ`.
(`ω ↦ h_{κ ω}(T)` is almost everywhere equal to a measurable function, so the image measure is
the expected one.) Blueprint node `erg:jacobs`. -/
theorem jacobs_entropyLaw_eq_map_ksEntropy_of_ergodicDecomposition {T : X → X}
    (hT : Continuous T) (Q : Measure Ω) [IsProbabilityMeasure Q] (κ : Kernel Ω X)
    [IsMarkovKernel κ] (hinv : MeasurePreserving T (Q.bind κ) (Q.bind κ))
    (herg : ∀ᵐ ω ∂Q, Ergodic T (κ ω)) :
    entropyLaw (Q.bind κ) T = Measure.map (fun p : Ω × X ↦
      (Ergodic.ksEntropy (κ p.1) T, Ergodic.ksEntropy (κ p.1) T)) (Q ⊗ₘ κ) := by
  have h := ae_compProd_localEntropy_eq_ksEntropy_of_ergodicDecomposition hT Q κ hinv herg
  refine Eq.trans ?_ (Measure.map_congr (h.mono fun p hp ↦ hp.1))
  rw [entropyLaw, ← Measure.snd_compProd Q κ, Measure.snd,
    Measure.map_map (measurable_localEntropy _ hT) measurable_snd]
  rfl

end General

/-! ### Example 5.3 -/

section Cantor

attribute [local instance] cantorMetricSpace

variable (p : ℝ≥0) (hp : p ≤ 1) (q : ℝ≥0) (hq : q ≤ 1)

/-- The mixture `½ (ν_p + ν_q)` of two Bernoulli measures is shift-invariant.
Blueprint node `erg:jacobs`. -/
theorem jacobs_bernoulliMixture_measurePreserving :
    MeasurePreserving shiftMap (bernoulliMixture p hp q hq) (bernoulliMixture p hp q hq) := by
  refine ⟨bernRand_measurable_shiftMap, ?_⟩
  rw [bernoulliMixture, Measure.map_smul, Measure.map_add _ _ bernRand_measurable_shiftMap,
    (bernRand_measurePreserving p hp).map_eq, (bernRand_measurePreserving q hq).map_eq]
  exact bernRand_measurable_shiftMap.aemeasurable

/-- Example 5.3 (audit, fix 4): the Kolmogorov–Sinai entropy of the mixture
`μ = ½ (ν_p + ν_q)` (`0 < p, q < 1`) is `(H(p) + H(q))/2`. Proof: it equals the Feng–Huang
entropy (`jacobs_measureEntropy_eq_ksEntropy_of_measurePreserving`), computed in
`measureEntropy_bernoulliMixture`. Blueprint node `erg:jacobs`. -/
theorem jacobs_ksEntropy_bernoulliMixture (hp0 : 0 < p) (hp1 : p < 1) (hq0 : 0 < q)
    (hq1 : q < 1) :
    Ergodic.ksEntropy (bernoulliMixture p hp q hq) shiftMap =
      (binEntropyBits p + binEntropyBits q) / 2 := by
  have h := jacobs_measureEntropy_eq_ksEntropy_of_measurePreserving continuous_shiftMap_cantor
    (bernoulliMixture p hp q hq) (jacobs_bernoulliMixture_measurePreserving p hp q hq)
  rw [measureEntropy_bernoulliMixture p hp q hq hp0 hp1 hq0 hq1] at h
  exact (congrArg Prod.fst h).symm

end Cantor

end Kolmogorov.PointToSet
