/-
Copyright (c) 2026 Emma Dinowitz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emma Dinowitz
-/
import KolmogorovMathlib.PointToSet.Measure.Ergodic.OrbitEntropy

/-!
# Local entropy along an ergodic decomposition (Theorem 7.5(b))

Theorem 7.5(b) of *Entropy of non-invariant measures and orbit complexity of random points*: on a
compact space, if `μ = ∫ κ ω dQ(ω)` is an invariant probability measure and `κ ω` is ergodic for
`Q`-a.e. `ω`, then `Φ_μ(x) = (h_{κ ω}(T), h_{κ ω}(T))` and `Φ_{κ ω}(x) = Φ_μ(x)` for `M`-a.e.
`(ω, x)`, `M = Q ⊗ κ`, where `h` is the Kolmogorov–Sinai entropy (equal to the Feng–Huang entropy
of the ergodic `κ ω`, `measureEntropy_eq_ksEntropy`).

Proof (algorithmic; no Jacobs theorem). Theorem 7.3(a) (`ae_compProd_localEntropy_le`) gives
`Φ_{κ ω} ≤ Φ_μ` and the ergodic Brin–Katok formula (`ae_localEntropy_eq_ksEntropy`) gives
`Φ_{κ ω} = (h_ω, h_ω)`. It remains to show `h̄_μ(T, x) ≤ h_ω` for `M`-a.e. `(ω, x)`
(`ae_compProd_upperLocalEntropy_le_ksEntropy`): take an oracle `A` admissible for `μ`; `M`-a.e.
`x` is `μ`-random, so `h̄_μ(T, x) = K̄^A(x, T)` (Theorem 3.3). For each dyadic scale, the
`A`-computable partition `U` of Lemma 2 built for `μ` is also one for `κ ω` (its complement is
`μ`-null, hence `κ ω`-null for `Q`-a.e. `ω`); for `κ ω`-a.e. `x`, the itinerary `φ(x)` is generic
for the coded measure of `κ ω` (classical Birkhoff for the ergodic `κ ω` applied to the cells,
`ae_isGenericPoint_symbolicCode_of_ergodic`); block coding gives
`limsup K^A(φ(x)↾n)/n ≤ h(coded κ ω) = h_{κ ω}(T, Q) ≤ h_ω`; and
`K_n^A(x, T, ε) ≤ K^A(φ(x)↾n) + c` (the coding step `orbitUpper_exists_orbitCode_le` of
`OrbitUpper`).

The passage from "`Q`-a.e. `ω`, `κ ω`-a.e. `x`" to "`M`-a.e. `(ω, x)`"
(`Measure.ae_compProd_of_ae_ae`) needs measurable sets; the Kolmogorov–Sinai entropy `h_ω` is
replaced there by the Feng–Huang entropy `∫ h̲_{κ ω} d(κ ω)`, which is measurable in `ω` and equal
to `h_ω` for ergodic `κ ω`.

The invariance hypothesis `hinv` is redundant (it follows from the ergodicity of the components);
it is kept so that the statements match their callers.

Blueprint node `erg:decomposition-entropy`.
-/

namespace Kolmogorov.PointToSet

open Filter Set MeasureTheory ProbabilityTheory
open scoped Topology ENNReal Computability

variable {X : Type*} [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
  {Ω : Type*} [MeasurableSpace Ω]

/-! ### Generic itineraries for an ergodic measure -/

omit [CompactSpace X] in
/-- For an ergodic invariant probability measure `ν` and a computable partition `U` for `ν`, the
itinerary of `ν`-almost every point is generic for the coded measure (classical Birkhoff theorem
applied to the indicators of the cells `⋂_{i<k} T^{-i} U_{w_i}`). Blueprint node
`erg:decomposition-entropy`. -/
theorem ae_isGenericPoint_symbolicCode_of_ergodic {p : ℕ} [NeZero p] {P : Presentation X}
    {A : Set ℕ} {T : X → X} (ν : Measure X) [IsProbabilityMeasure ν] (herg : Ergodic T ν)
    {U : Fin p → Set X} (hU : IsComputablePartitionIn P A ν U) :
    ∀ᵐ x ∂ν, x ∈ codingDomain T U ∧
      IsGenericPoint (codedMeasure ν T U) (symbolicCode T U x) := by
  have hTmp := herg.toMeasurePreserving
  have hUm : ∀ j, MeasurableSet (U j) := fun j ↦
    (isOpen_of_isCeOpenFamilyIn_typical hU.1 j).measurableSet
  have hD : ∀ᵐ x ∂ν, x ∈ codingDomain T U := measure_compl_codingDomain hTmp hUm hU.2.2
  have hcell : ∀ k (w : Fin k → Fin p), MeasurableSet (Ergodic.refinement T U k w) :=
    fun k w ↦ MeasurableSet.iInter fun i ↦ hTmp.measurable.iterate i (hUm _)
  have hB : ∀ᵐ x ∂ν, ∀ k (w : Fin k → Fin p), Tendsto
      (fun n : ℕ ↦ birkhoffAverage ℝ T ((Ergodic.refinement T U k w).indicator (1 : X → ℝ)) n x)
      atTop (𝓝 (∫ y, (Ergodic.refinement T U k w).indicator (1 : X → ℝ) y ∂ν)) := by
    refine ae_all_iff.mpr fun k ↦ ae_all_iff.mpr fun w ↦ ?_
    refine Ergodic.ae_tendsto_birkhoffAverage herg
      (Measurable.indicator (f := (1 : X → ℝ)) measurable_one (hcell k w))
      (C := 1) fun y ↦ ?_
    by_cases hy : y ∈ Ergodic.refinement T U k w <;> simp [hy]
  filter_upwards [hD, hB] with x hx hxB
  refine ⟨hx, fun k w ↦ ?_⟩
  rw [codedMeasure_wordCylinder hTmp hU w]
  have h := hxB k w
  rw [integral_indicator_one (hcell k w), measureReal_def] at h
  convert h using 1
  funext n
  rw [birkhoffAverage_indicator_eq_typical, ← ncard_eq_typicalVisitCount]
  congr 3
  ext j
  simp only [mem_ofPred_eq, Ergodic.refinement, mem_iInter, mem_preimage]
  refine and_congr_right fun _ ↦ forall_congr' fun i ↦ ?_
  rw [← Function.iterate_add_apply, add_comm]
  constructor
  · intro h
    rw [← h]
    exact iterate_mem_symbolicCode hU.2.1 hx _
  · exact symbolicCode_eq_of_mem hU.2.1

/-! ### The upper bound at a fixed scale -/

/-- The upper bound of Theorem 1(a) at a fixed scale, for a point whose itinerary through a
computable partition `U` (for the ergodic `ν`) is generic: `K̄^A(x, T, ε) ≤ h_ν(T)` when the
cells of a measurable partition `Q ⊇ U` have diameter `< ε`. No randomness is assumed. -/
private theorem orbitComplexityAt_snd_le_ksEntropy_of_generic (P : Presentation X) (T : X → X)
    (hT : Continuous T) (A : Set ℕ) (hP : ComputablePresentationIn P A)
    (hTA : IsRepresentedMapIn P P A T) (ν : Measure X) [IsProbabilityMeasure ν]
    (herg : Ergodic T ν) {p : ℕ} [NeZero p] {U Q : Fin p → Set X}
    (hU : IsComputablePartitionIn P A ν U) (hQ : Ergodic.IsMeasurablePartition Q)
    (hUQ : ∀ j, U j ⊆ Q j) {ε : ℝ} (hdiam : ∀ j, Metric.diam (Q j) < ε) {x : X}
    (hdom : x ∈ codingDomain T U)
    (hgen : IsGenericPoint (codedMeasure ν T U) (symbolicCode T U x)) :
    (orbitComplexityAt P T A x ε).2 ≤ Ergodic.ksEntropy ν T := by
  have hTm : MeasurePreserving T ν ν := herg.toMeasurePreserving
  set ω := symbolicCode T U x with hω
  obtain ⟨c, hc⟩ := orbitUpper_exists_orbitCode_le P T A hP hTA hU.1 hUQ hdiam
  have hcost : ∀ n, 1 ≤ n → finiteScaleBSCost P T (fun _ ↦ 1) A x n ε ≤
      (wordComplexity A ω n : ℝ≥0∞) / n + (c : ℝ≥0∞) / n := by
    intro n hn
    obtain ⟨i, hi, hK⟩ := hc x ω (iterate_mem_symbolicCode hU.2.1 hdom) n
    refine (finiteScaleBSCost_one_le P T A x hn hi).trans ?_
    rw [← ENNReal.add_div]
    gcongr
    exact_mod_cast hK
  have := isProbabilityMeasure_codedMeasure hT.measurable hU
  have hlim := limsup_wordComplexity_le_shiftEntropy A (codedMeasure ν T U)
    (ergodic_codedMeasure herg hU).toMeasurePreserving hgen
  rw [shiftEntropy_codedMeasure hTm hU hQ hUQ] at hlim
  have hc0 : Tendsto (fun n : ℕ ↦ (c : ℝ≥0∞) / n) atTop (𝓝 0) := by
    have h := ENNReal.Tendsto.const_mul ENNReal.tendsto_inv_nat_nhds_zero
      (Or.inr (ENNReal.natCast_ne_top c))
    rw [mul_zero] at h
    simpa only [div_eq_mul_inv] using h
  calc (orbitComplexityAt P T A x ε).2
      ≤ limsup (fun n : ℕ ↦ (wordComplexity A ω n : ℝ≥0∞) / n + (c : ℝ≥0∞) / n) atTop :=
        limsup_le_limsup (eventually_atTop.mpr ⟨1, hcost⟩)
    _ = limsup (fun n : ℕ ↦ (wordComplexity A ω n : ℝ≥0∞) / n) atTop :=
        ENNReal.limsup_add_of_right_tendsto_zero hc0 _
    _ ≤ Ergodic.entropyRate ν T Q := hlim
    _ ≤ Ergodic.ksEntropy ν T := Ergodic.entropyRate_le_ksEntropy ν T hQ

/-! ### The upper bound along the decomposition -/

/-- The core of `ae_compProd_upperLocalEntropy_le_ksEntropy`, fibrewise: for `Q`-a.e. `ω` and
`κ ω`-a.e. `x`, `h̄_μ(T, x) ≤ h_{κ ω}(T)` with `μ = Q.bind κ`. -/
private theorem ae_ae_upperLocalEntropy_le_ksEntropy {T : X → X} (hT : Continuous T)
    (Q : Measure Ω) [IsProbabilityMeasure Q] (κ : Kernel Ω X) [IsMarkovKernel κ]
    (herg : ∀ᵐ ω ∂Q, Ergodic T (κ ω)) :
    ∀ᵐ ω ∂Q, ∀ᵐ x ∂(κ ω), (localEntropy (Q.bind κ) T x).2 ≤ Ergodic.ksEntropy (κ ω) T := by
  have : IsProbabilityMeasure (Q.bind κ) :=
    isProbabilityMeasure_bind κ.aemeasurable (Eventually.of_forall fun ω ↦ inferInstance)
  have : Nonempty X := nonempty_of_isProbabilityMeasure (Q.bind κ)
  obtain ⟨P⟩ := exists_presentation (X := X)
  obtain ⟨A, hA'⟩ := exists_measureAdmissible_base P T hT (Q.bind κ)
  have hA := hA' A (TuringReducible.refl _)
  -- Lemma 2 for `μ`, at every dyadic scale
  have hpart : ∀ q : ℕ, ∃ (p : ℕ) (U Q' : Fin p → Set X), 0 < p ∧
      IsComputablePartitionIn P A (Q.bind κ) U ∧ Ergodic.IsMeasurablePartition Q' ∧
        (∀ j, U j ⊆ Q' j) ∧ ∀ j, Metric.diam (Q' j) < dyadicRadius q :=
    fun q ↦ exists_computablePartition P A (Q.bind κ) hA.1 hA.2.2 (dyadicRadius_pos q)
  choose pp U Q' hpos hU hQ hUQ hdiam using hpart
  have : ∀ q, NeZero (pp q) := fun q ↦ ⟨(hpos q).ne'⟩
  -- `μ`-null measurable sets are `κ ω`-null for `Q`-a.e. `ω`
  have hnull : ∀ {s : Set X}, MeasurableSet s → Q.bind κ s = 0 → ∀ᵐ ω ∂Q, κ ω s = 0 := by
    intro s hs h0
    rwa [Measure.bind_apply hs κ.aemeasurable, lintegral_eq_zero_iff (κ.measurable_coe hs)]
      at h0
  have hUnull : ∀ᵐ ω ∂Q, ∀ q, κ ω (⋃ j, U q j)ᶜ = 0 := by
    refine ae_all_iff.mpr fun q ↦ hnull ?_ (hU q).2.2
    exact (MeasurableSet.iUnion fun j ↦
      (isOpen_of_isCeOpenFamilyIn_typical (hU q).1 j).measurableSet).compl
  have hRnull : ∀ᵐ ω ∂Q, κ ω (toMeasurable (Q.bind κ) (randomPoints P A (Q.bind κ))ᶜ) = 0 :=
    hnull (measurableSet_toMeasurable _ _)
      (by rw [measure_toMeasurable]; exact measure_compl_randomPoints P A _)
  filter_upwards [herg, hUnull, hRnull] with ω hω hωU hωR
  have hUω : ∀ q, IsComputablePartitionIn P A (κ ω) (U q) := fun q ↦
    ⟨(hU q).1, (hU q).2.1, hωU q⟩
  have hrand : ∀ᵐ x ∂(κ ω), x ∈ randomPoints P A (Q.bind κ) :=
    measure_mono_null (subset_toMeasurable _ _) hωR
  have hgen : ∀ᵐ x ∂(κ ω), ∀ q, x ∈ codingDomain T (U q) ∧
      IsGenericPoint (codedMeasure (κ ω) T (U q)) (symbolicCode T (U q) x) :=
    ae_all_iff.mpr fun q ↦ ae_isGenericPoint_symbolicCode_of_ergodic (κ ω) hω (hUω q)
  filter_upwards [hrand, hgen] with x hx hxg
  rw [← orbitComplexities_eq_localEntropy P T hT A _ hA hx,
    orbitComplexities_eq_iSup_orbitComplexityAt]
  exact iSup_le fun q ↦ orbitComplexityAt_snd_le_ksEntropy_of_generic P T hT A hA.1 hA.2.1
    (κ ω) hω (hUω q) (hQ q) (hUQ q) (hdiam q) (hxg q).1 (hxg q).2

/-- The lower Feng–Huang entropy of the component, `ω ↦ ∫ h̲_{κ ω} d(κ ω)`, is measurable. -/
private theorem measurable_measureEntropy_fst_kernel {T : X → X} (hT : Continuous T)
    (κ : Kernel Ω X) [IsMarkovKernel κ] :
    Measurable fun ω ↦ (measureEntropy (κ ω) T).1 :=
  Measurable.lintegral_kernel_prod_right (f := fun ω x ↦ (localEntropy (κ ω) T x).1)
    (measurable_localEntropy_kernel hT κ).fst

omit [MetricSpace X] [CompactSpace X] [BorelSpace X] in
/-- A property of `Q`-a.e. `ω` holds at `M`-a.e. `(ω, x)`. -/
private theorem ae_compProd_fst {Q : Measure Ω} [IsProbabilityMeasure Q] {κ : Kernel Ω X}
    [IsMarkovKernel κ] {r : Ω → Prop} (h : ∀ᵐ ω ∂Q, r ω) : ∀ᵐ p ∂(Q ⊗ₘ κ), r p.1 := by
  rw [← Measure.fst_compProd Q κ, Measure.fst] at h
  exact ae_of_ae_map measurable_fst.aemeasurable h

/-- The upper local entropy of a mixture of ergodic measures is at most the Kolmogorov–Sinai
entropy of the component, almost everywhere. Blueprint node `erg:decomposition-entropy`. -/
theorem ae_compProd_upperLocalEntropy_le_ksEntropy {T : X → X} (hT : Continuous T)
    (Q : Measure Ω) [IsProbabilityMeasure Q] (κ : Kernel Ω X) [IsMarkovKernel κ]
    (hinv : MeasurePreserving T (Q.bind κ) (Q.bind κ)) (herg : ∀ᵐ ω ∂Q, Ergodic T (κ ω)) :
    ∀ᵐ p ∂(Q ⊗ₘ κ), (localEntropy (Q.bind κ) T p.2).2 ≤ Ergodic.ksEntropy (κ p.1) T := by
  -- the invariance of `Q.bind κ` is not needed: it follows from the ergodicity of the components
  have _ := hinv
  have hG := measurable_measureEntropy_fst_kernel hT κ
  have hμ : Measurable fun p : Ω × X ↦ localEntropy (Q.bind κ) T p.2 :=
    (measurable_localEntropy (Q.bind κ) hT).comp measurable_snd
  have h1 : ∀ᵐ p ∂(Q ⊗ₘ κ), (localEntropy (Q.bind κ) T p.2).2 ≤ (measureEntropy (κ p.1) T).1 := by
    refine Measure.ae_compProd_of_ae_ae (measurableSet_le hμ.snd (hG.comp measurable_fst)) ?_
    filter_upwards [ae_ae_upperLocalEntropy_le_ksEntropy hT Q κ herg, herg] with ω hω hωe
    rwa [measureEntropy_eq_ksEntropy hT _ hωe]
  filter_upwards [h1, ae_compProd_fst (κ := κ) herg] with p hp hpe
  rwa [measureEntropy_eq_ksEntropy hT _ hpe] at hp

/-- Theorem 7.5(b), with the Kolmogorov–Sinai entropy: along an ergodic decomposition the local
entropy of the mixture is that of the component, and both equal `(h_ω, h_ω)`.
Blueprint node `erg:decomposition-entropy`. -/
theorem ae_compProd_localEntropy_eq_ksEntropy_of_ergodicDecomposition {T : X → X}
    (hT : Continuous T) (Q : Measure Ω) [IsProbabilityMeasure Q] (κ : Kernel Ω X)
    [IsMarkovKernel κ] (hinv : MeasurePreserving T (Q.bind κ) (Q.bind κ))
    (herg : ∀ᵐ ω ∂Q, Ergodic T (κ ω)) :
    ∀ᵐ p ∂(Q ⊗ₘ κ),
      localEntropy (Q.bind κ) T p.2 = (Ergodic.ksEntropy (κ p.1) T, Ergodic.ksEntropy (κ p.1) T) ∧
        localEntropy (κ p.1) T p.2 = localEntropy (Q.bind κ) T p.2 := by
  have hG := measurable_measureEntropy_fst_kernel hT κ
  have hK := measurable_localEntropy_kernel hT κ
  -- the ergodic Brin–Katok formula, lifted to `M`
  have hBK : ∀ᵐ p ∂(Q ⊗ₘ κ), localEntropy (κ p.1) T p.2 =
      ((measureEntropy (κ p.1) T).1, (measureEntropy (κ p.1) T).1) := by
    refine Measure.ae_compProd_of_ae_ae (measurableSet_eq_fun hK
      ((hG.comp measurable_fst).prodMk (hG.comp measurable_fst))) ?_
    filter_upwards [herg] with ω hω
    exact ae_localEntropy_eq_measureEntropy_of_ergodic hT (κ ω) hω
  filter_upwards [hBK, ae_compProd_fst (κ := κ) herg,
    ae_compProd_upperLocalEntropy_le_ksEntropy hT Q κ hinv herg,
    ae_compProd_localEntropy_le hT Q κ] with p hp hpe hup hle
  rw [measureEntropy_eq_ksEntropy hT _ hpe] at hp
  rw [hp] at hle
  have hfs := localEntropy_fst_le_snd (Q.bind κ) T p.2
  have h1 : (localEntropy (Q.bind κ) T p.2).1 = Ergodic.ksEntropy (κ p.1) T :=
    le_antisymm (hfs.trans hup) hle.1
  have h2 : (localEntropy (Q.bind κ) T p.2).2 = Ergodic.ksEntropy (κ p.1) T :=
    le_antisymm hup hle.2
  have heq : localEntropy (Q.bind κ) T p.2 =
      (Ergodic.ksEntropy (κ p.1) T, Ergodic.ksEntropy (κ p.1) T) := Prod.ext h1 h2
  exact ⟨heq, hp.trans heq.symm⟩

/-- Theorem 7.5(b) in the form of the chapter (`IntegralAffinity`), with the Feng–Huang entropy
of the component and without the finiteness hypothesis. Blueprint node
`erg:decomposition-entropy`. -/
theorem ae_compProd_localEntropy_eq_measureEntropy_of_ergodicDecomposition {T : X → X}
    (hT : Continuous T) (Q : Measure Ω) [IsProbabilityMeasure Q] (κ : Kernel Ω X)
    [IsMarkovKernel κ] (hinv : MeasurePreserving T (Q.bind κ) (Q.bind κ))
    (herg : ∀ᵐ ω ∂Q, Ergodic T (κ ω)) :
    ∀ᵐ p ∂(Q ⊗ₘ κ),
      localEntropy (Q.bind κ) T p.2 =
          ((measureEntropy (κ p.1) T).1, (measureEntropy (κ p.1) T).1) ∧
        localEntropy (κ p.1) T p.2 = localEntropy (Q.bind κ) T p.2 := by
  filter_upwards [ae_compProd_localEntropy_eq_ksEntropy_of_ergodicDecomposition hT Q κ hinv herg,
    ae_compProd_fst (κ := κ) herg] with p hp hpe
  rwa [measureEntropy_eq_ksEntropy hT _ hpe]

end Kolmogorov.PointToSet
