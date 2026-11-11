/-
Copyright (c) 2026 Emma Dinowitz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emma Dinowitz
-/
import KolmogorovMathlib.PointToSet.Measure.EssentialBounds
import KolmogorovMathlib.PointToSet.Measure.InformationRate

/-!
# Variational forms and the comparison chain (Corollaries 4.2 and 6.5(c), §4.4)

For a Borel probability measure `μ` with `μ(Z) = 1` the Feng–Huang entropies of `μ` are at
most the Bowen and packing entropies of `Z` (`measureEntropy_fst_le_lowerEntropy`,
`measureEntropy_snd_le_upperEntropy`); this half of the variational principle of Feng and
Huang follows from Theorem 4.3. The other half, for a compact subset `K` of a compact space,

`h̲(K, T) ≤ sup {h̲_μ(T) : μ(K) = 1}`, `h̄(K, T) ≤ sup {h̄_μ(T) : μ(K) = 1}`,

is the theorem of Feng and Huang (*Variational principles for topological entropies of
subsets*, J. Funct. Anal. 263 (2012)); it is not available here and is recorded as the tracked
`sorry`s `lowerEntropy_le_iSup_measureEntropy` and `upperEntropy_le_iSup_measureEntropy`.
The remaining statements are derived from these two.

* `lowerEntropy_eq_iSup_measureEntropy`, `upperEntropy_eq_iSup_measureEntropy`: the
  variational principles.
* `iInf_iSup_orbitComplexities_eq_iSup_lintegral` (Corollary 4.2): the variational form of the
  point-to-set principle on a compact set.
* `lowerEntropy_eq_iSup_essInf`, `lowerEntropy_eq_iSup_essSup` and the upper versions
  (Corollary 6.5(c)): any statistic between the essential infimum and the essential supremum
  gives the same supremum.
* `essInf_le_measureEntropy_fst`, `measureEntropy_snd_le_essSup`, `entropy_chain` (§4.4):
  `ess inf h̲_μ ≤ h̲_μ(T) ≤ H̲_μ(T) ≤ H̄_μ(T) ≤ h̄_μ(T) ≤ ess sup h̄_μ` on a compact space.

Blueprint nodes `meas:variational`, `meas:chain`.
-/

namespace Kolmogorov.PointToSet

open Filter Set MeasureTheory
open scoped Topology ENNReal Computability

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

omit [MetricSpace X] [BorelSpace X] in
/-- For a probability measure, the integral of a function is at most its essential
supremum. -/
private theorem lintegral_le_essSup_of_prob (μ : Measure X) [IsProbabilityMeasure μ]
    (f : X → ℝ≥0∞) : ∫⁻ x, f x ∂μ ≤ essSup f μ := by
  calc ∫⁻ x, f x ∂μ ≤ ∫⁻ _, essSup f μ ∂μ := lintegral_mono_ae (ENNReal.ae_le_essSup f)
    _ = essSup f μ := by simp

omit [MetricSpace X] [BorelSpace X] in
/-- For a probability measure, the essential infimum of a function is at most its
integral. -/
private theorem essInf_le_lintegral_of_prob (μ : Measure X) [IsProbabilityMeasure μ]
    (f : X → ℝ≥0∞) : essInf f μ ≤ ∫⁻ x, f x ∂μ := by
  calc essInf f μ = ∫⁻ _, essInf f μ ∂μ := by simp
    _ ≤ ∫⁻ x, f x ∂μ := lintegral_mono_ae ae_essInf_le

/-- The lower Feng–Huang entropy of a probability measure carried by `Z` is at most the Bowen
entropy of `Z`. Blueprint node `meas:variational`. -/
theorem measureEntropy_fst_le_lowerEntropy (P : Presentation X) (T : X → X)
    (hT : Continuous T) (μ : Measure X) [IsProbabilityMeasure μ] {Z : Set X} (hZ : μ Z = 1) :
    (measureEntropy μ T).1 ≤ lowerEntropy T Z := by
  calc (measureEntropy μ T).1 ≤ essSup (fun x ↦ (localEntropy μ T x).1) μ :=
        lintegral_le_essSup_of_prob μ _
    _ = ⨅ (Z : Set X) (_ : μ Z = 1), lowerEntropy T Z :=
        essSup_lowerLocalEntropy_eq_iInf_lowerEntropy P T hT μ
    _ ≤ lowerEntropy T Z := iInf₂_le Z hZ

/-- The upper Feng–Huang entropy of a probability measure carried by `Z` is at most the
packing entropy of `Z`. Blueprint node `meas:variational`. -/
theorem measureEntropy_snd_le_upperEntropy (P : Presentation X) (T : X → X)
    (hT : Continuous T) (μ : Measure X) [IsProbabilityMeasure μ] {Z : Set X} (hZ : μ Z = 1) :
    (measureEntropy μ T).2 ≤ upperEntropy P T Z := by
  calc (measureEntropy μ T).2 ≤ essSup (fun x ↦ (localEntropy μ T x).2) μ :=
        lintegral_le_essSup_of_prob μ _
    _ = ⨅ (Z : Set X) (_ : μ Z = 1), upperEntropy P T Z :=
        essSup_upperLocalEntropy_eq_iInf_upperEntropy P T hT μ
    _ ≤ upperEntropy P T Z := iInf₂_le Z hZ

/-- The Feng–Huang variational principle for the Bowen entropy of a compact set, hard half.
Outside input: D.-J. Feng and W. Huang, J. Funct. Anal. 263 (2012), Theorem 1.2.
Blueprint node `meas:variational`. -/
theorem lowerEntropy_le_iSup_measureEntropy [CompactSpace X] {T : X → X} (hT : Continuous T)
    {K : Set X} (hK : IsCompact K) (hne : K.Nonempty) :
    lowerEntropy T K ≤
      ⨆ (μ : Measure X) (_ : IsProbabilityMeasure μ) (_ : μ K = 1), (measureEntropy μ T).1 := by
  -- TODO(sorry): external input — the Feng–Huang variational principle (Bowen entropy)
  sorry

/-- The Feng–Huang variational principle for the packing entropy of a compact set, hard half.
Outside input: D.-J. Feng and W. Huang, J. Funct. Anal. 263 (2012), Theorem 1.3.
Blueprint node `meas:variational`. -/
theorem upperEntropy_le_iSup_measureEntropy [CompactSpace X] (P : Presentation X) {T : X → X}
    (hT : Continuous T) {K : Set X} (hK : IsCompact K) (hne : K.Nonempty) :
    upperEntropy P T K ≤
      ⨆ (μ : Measure X) (_ : IsProbabilityMeasure μ) (_ : μ K = 1), (measureEntropy μ T).2 := by
  -- TODO(sorry): external input — the Feng–Huang variational principle (packing entropy)
  sorry

/-- The variational principle of Feng and Huang for the Bowen entropy of a compact set.
Blueprint node `meas:variational`. -/
theorem lowerEntropy_eq_iSup_measureEntropy [CompactSpace X] (P : Presentation X) {T : X → X}
    (hT : Continuous T) {K : Set X} (hK : IsCompact K) (hne : K.Nonempty) :
    lowerEntropy T K =
      ⨆ (μ : Measure X) (_ : IsProbabilityMeasure μ) (_ : μ K = 1), (measureEntropy μ T).1 :=
  le_antisymm (lowerEntropy_le_iSup_measureEntropy hT hK hne) <|
    iSup_le fun μ ↦ iSup_le fun _ ↦ iSup_le fun hμK ↦
      measureEntropy_fst_le_lowerEntropy P T hT μ hμK

/-- The variational principle of Feng and Huang for the packing entropy of a compact set.
Blueprint node `meas:variational`. -/
theorem upperEntropy_eq_iSup_measureEntropy [CompactSpace X] (P : Presentation X) {T : X → X}
    (hT : Continuous T) {K : Set X} (hK : IsCompact K) (hne : K.Nonempty) :
    upperEntropy P T K =
      ⨆ (μ : Measure X) (_ : IsProbabilityMeasure μ) (_ : μ K = 1), (measureEntropy μ T).2 :=
  le_antisymm (upperEntropy_le_iSup_measureEntropy P hT hK hne) <|
    iSup_le fun μ ↦ iSup_le fun _ ↦ iSup_le fun hμK ↦
      measureEntropy_snd_le_upperEntropy P T hT μ hμK

/-- Corollary 4.2 (variational form): on a compact space, for a nonempty compact set `K`,
`min_A sup_{x ∈ K} K̲^A(x) = sup_{μ(K) = 1} ∫ K̲^{A_μ} dμ` and the same for the upper
quantities, where `A_μ` is any oracle admissible for `(X, d, T, μ)`.
Blueprint node `meas:variational`. -/
theorem iInf_iSup_orbitComplexities_eq_iSup_lintegral [CompactSpace X] (P : Presentation X)
    {T : X → X} (hT : Continuous T) {K : Set X} (hK : IsCompact K) (hne : K.Nonempty)
    (Aμ : Measure X → Set ℕ)
    (hAμ : ∀ μ : Measure X, IsProbabilityMeasure μ → IsMeasureAdmissible P T μ (Aμ μ)) :
    ⨅ A : Set ℕ, ⨆ x ∈ K, (orbitComplexities P T A x).1 =
        ⨆ (μ : Measure X) (_ : IsProbabilityMeasure μ) (_ : μ K = 1),
          ∫⁻ x, (orbitComplexities P T (Aμ μ) x).1 ∂μ ∧
      ⨅ A : Set ℕ, ⨆ x ∈ K, (orbitComplexities P T A x).2 =
        ⨆ (μ : Measure X) (_ : IsProbabilityMeasure μ) (_ : μ K = 1),
          ∫⁻ x, (orbitComplexities P T (Aμ μ) x).2 ∂μ := by
  constructor
  · rw [← entropy_effectiveCharacterization_allOracles_pointToSet P T hT K,
      lowerEntropy_eq_iSup_measureEntropy P hT hK hne]
    exact iSup_congr fun μ ↦ iSup_congr fun hμ ↦ iSup_congr fun _ ↦
      (measureEntropy_eq_lintegral_orbitComplexities P T hT (Aμ μ) μ (hAμ μ hμ)).1
  · rw [← upperEntropy_pointToSet P T hT K, upperEntropy_eq_iSup_measureEntropy P hT hK hne]
    exact iSup_congr fun μ ↦ iSup_congr fun hμ ↦ iSup_congr fun _ ↦
      (measureEntropy_eq_lintegral_orbitComplexities P T hT (Aμ μ) μ (hAμ μ hμ)).2

/-- The key step of Corollary 6.5(c) for essential infima: if `μ(K) = 1` then for every
measurable statistic `π` of the pair of local entropies, `∫ π ∘ Φ_μ dμ` is at most the
supremum of `ess inf π ∘ Φ_ν` over the probability measures `ν` with `ν(K) = 1`. For
`s < ∫ π ∘ Φ_μ dμ` the set `E = {s < π ∘ Φ_μ}` has positive mass, and the normalised
restriction `ν` of `μ` to `E` satisfies `π ∘ Φ_ν = π ∘ Φ_μ > s` `ν`-almost everywhere. -/
private theorem lintegral_le_iSup_essInf [CompactSpace X] {T : X → X} (hT : Continuous T)
    {K : Set X} (hK : IsCompact K) (π : ℝ≥0∞ × ℝ≥0∞ → ℝ≥0∞) (hπ : Measurable π)
    (μ : Measure X) [IsProbabilityMeasure μ] (hμK : μ K = 1) :
    ∫⁻ x, π (localEntropy μ T x) ∂μ ≤
      ⨆ (ν : Measure X) (_ : IsProbabilityMeasure ν) (_ : ν K = 1),
        essInf (fun x ↦ π (localEntropy ν T x)) ν := by
  refine le_of_forall_lt_imp_le_of_dense fun s hs ↦ ?_
  have hf : Measurable fun x ↦ π (localEntropy μ T x) := hπ.comp (measurable_localEntropy μ hT)
  set E := {x | s < π (localEntropy μ T x)} with hEdef
  have hE : MeasurableSet E := measurableSet_lt measurable_const hf
  have hE0 : μ E ≠ 0 := by
    intro h0
    have hle : ∀ᵐ x ∂μ, π (localEntropy μ T x) ≤ s := by
      filter_upwards [measure_eq_zero_iff_ae_notMem.1 h0] with x hx
      exact not_lt.1 hx
    have := lintegral_mono_ae hle
    simp only [lintegral_const, measure_univ, mul_one] at this
    exact absurd hs (not_lt.2 this)
  have hEt : μ E ≠ ⊤ := measure_ne_top μ E
  set ν : Measure X := (μ E)⁻¹ • μ.restrict E with hνdef
  have hν : IsProbabilityMeasure ν := ⟨by
    simp only [hνdef, Measure.smul_apply, Measure.restrict_apply_univ, smul_eq_mul]
    exact ENNReal.inv_mul_cancel hE0 hEt⟩
  have hνμ : ν ≪ μ :=
    (Measure.absolutelyContinuous_of_le Measure.restrict_le_self).smul_left _
  have hνK : ν K = 1 := by
    have hKc : μ Kᶜ = 0 := (prob_compl_eq_zero_iff hK.measurableSet).2 hμK
    simp only [hνdef, Measure.smul_apply, Measure.restrict_apply hK.measurableSet,
      smul_eq_mul]
    rw [inter_comm, measure_inter_conull hKc]
    exact ENNReal.inv_mul_cancel hE0 hEt
  have hae : ∀ᵐ x ∂ν, s ≤ π (localEntropy ν T x) := by
    have h1 : ∀ᵐ x ∂ν, x ∈ E := Measure.ae_smul_measure (ae_restrict_mem hE) _
    filter_upwards [ae_localEntropy_eq_of_absolutelyContinuous hT hνμ, h1] with x hx hxE
    rw [hx]
    exact hxE.le
  calc s ≤ essInf (fun x ↦ π (localEntropy ν T x)) ν := le_essInf_of_ae_le s hae
    _ ≤ _ := le_iSup₂_of_le (f := fun (ν : Measure X) (_ : IsProbabilityMeasure ν) ↦
          ⨆ (_ : ν K = 1), essInf (fun x ↦ π (localEntropy ν T x)) ν) ν hν
        (le_iSup_of_le hνK le_rfl)

/-- Corollary 6.5(c), essential infimum: `h̲(K, T) = sup_{μ(K) = 1} ess inf h̲_μ` and
`h̄(K, T) = sup_{μ(K) = 1} ess inf h̄_μ`. Blueprint node `meas:variational`. -/
theorem lowerEntropy_eq_iSup_essInf [CompactSpace X] (P : Presentation X) {T : X → X}
    (hT : Continuous T) {K : Set X} (hK : IsCompact K) (hne : K.Nonempty) :
    lowerEntropy T K =
        ⨆ (μ : Measure X) (_ : IsProbabilityMeasure μ) (_ : μ K = 1),
          essInf (fun x ↦ (localEntropy μ T x).1) μ ∧
      upperEntropy P T K =
        ⨆ (μ : Measure X) (_ : IsProbabilityMeasure μ) (_ : μ K = 1),
          essInf (fun x ↦ (localEntropy μ T x).2) μ := by
  constructor
  · refine le_antisymm ?_ (iSup_le fun μ ↦ iSup_le fun _ ↦ iSup_le fun hμK ↦
      (essInf_le_lintegral_of_prob μ _).trans (measureEntropy_fst_le_lowerEntropy P T hT μ hμK))
    rw [lowerEntropy_eq_iSup_measureEntropy P hT hK hne]
    exact iSup_le fun μ ↦ iSup_le fun _ ↦ iSup_le fun hμK ↦
      lintegral_le_iSup_essInf hT hK Prod.fst measurable_fst μ hμK
  · refine le_antisymm ?_ (iSup_le fun μ ↦ iSup_le fun _ ↦ iSup_le fun hμK ↦
      (essInf_le_lintegral_of_prob μ _).trans (measureEntropy_snd_le_upperEntropy P T hT μ hμK))
    rw [upperEntropy_eq_iSup_measureEntropy P hT hK hne]
    exact iSup_le fun μ ↦ iSup_le fun _ ↦ iSup_le fun hμK ↦
      lintegral_le_iSup_essInf hT hK Prod.snd measurable_snd μ hμK

/-- Corollary 6.5(c), essential supremum: `h̲(K, T) = sup_{μ(K) = 1} ess sup h̲_μ` and
`h̄(K, T) = sup_{μ(K) = 1} ess sup h̄_μ`. Blueprint node `meas:variational`. -/
theorem lowerEntropy_eq_iSup_essSup [CompactSpace X] (P : Presentation X) {T : X → X}
    (hT : Continuous T) {K : Set X} (hK : IsCompact K) (hne : K.Nonempty) :
    lowerEntropy T K =
        ⨆ (μ : Measure X) (_ : IsProbabilityMeasure μ) (_ : μ K = 1),
          essSup (fun x ↦ (localEntropy μ T x).1) μ ∧
      upperEntropy P T K =
        ⨆ (μ : Measure X) (_ : IsProbabilityMeasure μ) (_ : μ K = 1),
          essSup (fun x ↦ (localEntropy μ T x).2) μ := by
  constructor
  · refine le_antisymm ?_ (iSup_le fun μ ↦ iSup_le fun _ ↦ iSup_le fun hμK ↦
      (essSup_lowerLocalEntropy_eq_iInf_lowerEntropy P T hT μ).trans_le (iInf₂_le K hμK))
    rw [lowerEntropy_eq_iSup_measureEntropy P hT hK hne]
    exact iSup_mono fun μ ↦ iSup_mono fun _ ↦ iSup_mono fun _ ↦
      lintegral_le_essSup_of_prob μ _
  · refine le_antisymm ?_ (iSup_le fun μ ↦ iSup_le fun _ ↦ iSup_le fun hμK ↦
      (essSup_upperLocalEntropy_eq_iInf_upperEntropy P T hT μ).trans_le (iInf₂_le K hμK))
    rw [upperEntropy_eq_iSup_measureEntropy P hT hK hne]
    exact iSup_mono fun μ ↦ iSup_mono fun _ ↦ iSup_mono fun _ ↦
      lintegral_le_essSup_of_prob μ _

/-! ### The comparison chain (§4.4) -/

omit [BorelSpace X] in
/-- `ess inf h̲_μ ≤ h̲_μ(T)` for a probability measure. Blueprint node `meas:chain`. -/
theorem essInf_le_measureEntropy_fst {T : X → X} (_hT : Continuous T) (μ : Measure X)
    [IsProbabilityMeasure μ] :
    essInf (fun x ↦ (localEntropy μ T x).1) μ ≤ (measureEntropy μ T).1 :=
  essInf_le_lintegral_of_prob μ _

omit [BorelSpace X] in
/-- `h̄_μ(T) ≤ ess sup h̄_μ` for a probability measure. Blueprint node `meas:chain`. -/
theorem measureEntropy_snd_le_essSup {T : X → X} (_hT : Continuous T) (μ : Measure X)
    [IsProbabilityMeasure μ] :
    (measureEntropy μ T).2 ≤ essSup (fun x ↦ (localEntropy μ T x).2) μ :=
  lintegral_le_essSup_of_prob μ _

/-- The summary of §4.4: on a compact space,
`ess inf h̲_μ ≤ h̲_μ(T) ≤ H̲_μ(T) ≤ H̄_μ(T) ≤ h̄_μ(T) ≤ ess sup h̄_μ`.
Blueprint node `meas:chain`. -/
theorem entropy_chain [CompactSpace X] {T : X → X} (hT : Continuous T) (μ : Measure X)
    [IsProbabilityMeasure μ] :
    essInf (fun x ↦ (localEntropy μ T x).1) μ ≤ (measureEntropy μ T).1 ∧
      (measureEntropy μ T).1 ≤ (informationRate μ T).1 ∧
      (informationRate μ T).1 ≤ (informationRate μ T).2 ∧
      (informationRate μ T).2 ≤ (measureEntropy μ T).2 ∧
      (measureEntropy μ T).2 ≤ essSup (fun x ↦ (localEntropy μ T x).2) μ :=
  ⟨essInf_le_measureEntropy_fst hT μ, measureEntropy_fst_le_informationRate_fst hT μ,
    informationRate_fst_le_snd μ T, informationRate_snd_le_measureEntropy_snd hT μ,
    measureEntropy_snd_le_essSup hT μ⟩

end Kolmogorov.PointToSet
