/-
Copyright (c) 2026 Emma Dinowitz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emma Dinowitz
-/
import KolmogorovMathlib.PointToSet.Measure.Domination
import Mathlib.Probability.Kernel.Composition.MeasureCompProd
import Mathlib.Probability.Kernel.Composition.MeasureComp

/-!
# The entropy law under absolute continuity, convex combinations and integrals

Consequences of the domination lemma (Lemma 7.1) for the pair of local entropies
`Φ_μ = localEntropy μ T` and the entropy law `Λ_μ = (Φ_μ)_* μ` (E. Dinowitz, *Entropy of
non-invariant measures and orbit complexity of random points*, §§6–7).

* `ae_localEntropy_eq_of_absolutelyContinuous`, `entropyLaw_absolutelyContinuous`
  (Proposition 6.4): if `ν ≪ μ` then `Φ_ν = Φ_μ` holds `ν`-almost everywhere, hence
  `Λ_ν = (Φ_μ)_* ν ≪ Λ_μ`.
* `ae_localEntropy_eq_of_sum`, `entropyLaw_sum` (Proposition 6.3): for a countable convex
  combination `μ = ∑_j t_j μ_j` with all `t_j > 0`, `Φ_μ = Φ_{μ_j}` holds `μ_j`-almost
  everywhere and `Λ_μ = ∑_j t_j Λ_{μ_j}`.
* `ae_compProd_localEntropy_le`, `kernelEntropyLaw_eq_iff`, `lintegral_measureEntropy_le`
  (Theorem 7.3): for an integral decomposition `μ = ∫ μ_ω dQ(ω)` given by a kernel `κ`, with
  `M = Q ⊗ κ` on `Ω × X`, `Φ_{μ_ω}(x) ≤ Φ_μ(x)` coordinatewise for `M`-almost every `(ω, x)`;
  integral affinity `Λ_μ = ∫ Λ_{μ_ω} dQ(ω)` holds if and only if `Φ_{μ_ω}(x) = Φ_μ(x)` for
  `M`-almost every `(ω, x)`; and the Feng–Huang entropies are superaffine,
  `h̲_μ(T) ≥ ∫ h̲_{μ_ω}(T) dQ(ω)` and `h̄_μ(T) ≥ ∫ h̄_{μ_ω}(T) dQ(ω)`.

The proofs here are classical: they use Lemma 7.1 in place of the randomness argument of the
sketches of Propositions 6.3 and 6.4.

Blueprint nodes `meas:abs-cont`, `meas:affine`, `meas:integral`.
-/

namespace Kolmogorov.PointToSet

open Filter Set MeasureTheory ProbabilityTheory
open scoped Topology ENNReal

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [SecondCountableTopology X]

/-! ### Absolute continuity (Proposition 6.4) -/

/-- Proposition 6.4: if `ν ≪ μ` then `Φ_ν = Φ_μ` holds `ν`-almost everywhere.
Blueprint node `meas:abs-cont`. -/
theorem ae_localEntropy_eq_of_absolutelyContinuous {T : X → X} (hT : Continuous T)
    {μ ν : Measure X} [IsFiniteMeasure μ] [IsFiniteMeasure ν] (h : ν ≪ μ) :
    ∀ᵐ x ∂ν, localEntropy ν T x = localEntropy μ T x := by
  filter_upwards [ae_localEntropy_le hT μ ν, h.ae_le (ae_localEntropy_le hT ν μ)] with x h1 h2
  exact Prod.ext (le_antisymm h1.1 h2.1) (le_antisymm h1.2 h2.2)

/-- Proposition 6.4: if `ν ≪ μ` then the entropy law of `ν` is the law of `Φ_μ` under `ν`. -/
theorem entropyLaw_eq_map_of_absolutelyContinuous {T : X → X} (hT : Continuous T)
    {μ ν : Measure X} [IsFiniteMeasure μ] [IsFiniteMeasure ν] (h : ν ≪ μ) :
    entropyLaw ν T = Measure.map (localEntropy μ T) ν := by
  exact Measure.map_congr (ae_localEntropy_eq_of_absolutelyContinuous hT h)

/-- Proposition 6.4: if `ν ≪ μ` then `Λ_ν ≪ Λ_μ`. Blueprint node `meas:abs-cont`. -/
theorem entropyLaw_absolutelyContinuous {T : X → X} (hT : Continuous T)
    {μ ν : Measure X} [IsFiniteMeasure μ] [IsFiniteMeasure ν] (h : ν ≪ μ) :
    entropyLaw ν T ≪ entropyLaw μ T := by
  rw [entropyLaw_eq_map_of_absolutelyContinuous hT h]
  exact h.map (measurable_localEntropy μ hT)

/-! ### Countable convex combinations (Proposition 6.3) -/

/-- Proposition 6.3: for a countable combination `μ = ∑_j t_j μ_j` with all `t_j > 0`, the
local entropies of `μ` and of `μ_j` agree `μ_j`-almost everywhere.
Blueprint node `meas:affine`. -/
theorem ae_localEntropy_eq_of_sum {T : X → X} (hT : Continuous T) {ι : Type*} [Countable ι]
    (t : ι → ℝ≥0∞) (μs : ι → Measure X) [∀ j, IsFiniteMeasure (μs j)]
    [IsFiniteMeasure (Measure.sum fun j ↦ t j • μs j)] (ht : ∀ j, t j ≠ 0) (j : ι) :
    ∀ᵐ x ∂μs j, localEntropy (Measure.sum fun j ↦ t j • μs j) T x = localEntropy (μs j) T x := by
  have hac : μs j ≪ Measure.sum fun j ↦ t j • μs j := by
    intro s hs
    have hle := Measure.le_iff'.1 (Measure.le_sum (fun j ↦ t j • μs j) j) s
    rw [hs, nonpos_iff_eq_zero, Measure.smul_apply, smul_eq_mul, mul_eq_zero] at hle
    exact hle.resolve_left (ht j)
  filter_upwards [ae_localEntropy_eq_of_absolutelyContinuous hT hac] with x hx
  exact hx.symm

/-- Proposition 6.3 (affinity of the entropy law): for a countable combination
`μ = ∑_j t_j μ_j` with all `t_j > 0`, `Λ_μ = ∑_j t_j Λ_{μ_j}`.
Blueprint node `meas:affine`. -/
theorem entropyLaw_sum {T : X → X} (hT : Continuous T) {ι : Type*} [Countable ι]
    (t : ι → ℝ≥0∞) (μs : ι → Measure X) [∀ j, IsFiniteMeasure (μs j)]
    [IsFiniteMeasure (Measure.sum fun j ↦ t j • μs j)] (ht : ∀ j, t j ≠ 0) :
    entropyLaw (Measure.sum fun j ↦ t j • μs j) T =
      Measure.sum fun j ↦ t j • entropyLaw (μs j) T := by
  unfold entropyLaw
  rw [Measure.map_sum (measurable_localEntropy _ hT).aemeasurable]
  congr 1
  funext j
  rw [Measure.map_smul _ (measurable_localEntropy _ hT).aemeasurable,
    Measure.map_congr (ae_localEntropy_eq_of_sum hT t μs ht j)]

/-- Corollary 6.5(a): the Feng–Huang entropies are affine on countable convex combinations
with positive weights. Blueprint node `meas:affine`. -/
theorem measureEntropy_sum {T : X → X} (hT : Continuous T) {ι : Type*} [Countable ι]
    (t : ι → ℝ≥0∞) (μs : ι → Measure X) [∀ j, IsFiniteMeasure (μs j)]
    [IsFiniteMeasure (Measure.sum fun j ↦ t j • μs j)] (ht : ∀ j, t j ≠ 0) :
    (measureEntropy (Measure.sum fun j ↦ t j • μs j) T).1 =
        ∑' j, t j * (measureEntropy (μs j) T).1 ∧
      (measureEntropy (Measure.sum fun j ↦ t j • μs j) T).2 =
        ∑' j, t j * (measureEntropy (μs j) T).2 := by
  simp only [measureEntropy, lintegral_sum_measure, lintegral_smul_measure, smul_eq_mul]
  constructor <;> refine tsum_congr fun j ↦ congrArg (t j * ·) (lintegral_congr_ae ?_) <;>
    filter_upwards [ae_localEntropy_eq_of_sum hT t μs ht j] with x hx <;> rw [hx]

/-! ### Integral decompositions (Theorem 7.3) -/

section integral

variable {Ω : Type*} [MeasurableSpace Ω]

/-- If two measurable `ℝ≥0∞`-valued functions satisfy `U ≤ V` almost everywhere for a finite
measure and have the same law, then they agree almost everywhere. -/
private lemma ae_eq_of_ae_le_of_map_eq {α : Type*} [MeasurableSpace α] {M : Measure α}
    [IsFiniteMeasure M] {U V : α → ℝ≥0∞} (hU : Measurable U) (hV : Measurable V)
    (hle : ∀ᵐ a ∂M, U a ≤ V a) (hmap : Measure.map U M = Measure.map V M) :
    ∀ᵐ a ∂M, U a = V a := by
  have hq : ∀ c : ℝ≥0∞, ∀ᵐ a ∂M, (V a < c ↔ U a < c) := by
    intro c
    have hsub : V ⁻¹' Iio c ≤ᵐ[M] U ⁻¹' Iio c := by
      filter_upwards [hle] with a ha hVa
      exact lt_of_le_of_lt ha hVa
    have hmeas : M (V ⁻¹' Iio c) = M (U ⁻¹' Iio c) := by
      rw [← Measure.map_apply hV measurableSet_Iio, ← Measure.map_apply hU measurableSet_Iio,
        hmap]
    have heq := ae_eq_of_ae_subset_of_measure_ge hsub hmeas.ge
      (hV measurableSet_Iio).nullMeasurableSet (measure_ne_top _ _)
    filter_upwards [heq] with a ha
    exact Iff.of_eq ha
  have hall := ae_all_iff.2 fun q : ℚ ↦ hq ((q : ℝ).toNNReal : ℝ≥0∞)
  filter_upwards [hle, hall] with a ha hqa
  refine le_antisymm ha (not_lt.1 fun hlt ↦ ?_)
  obtain ⟨q, -, h1, h2⟩ := ENNReal.lt_iff_exists_rat_btwn.1 hlt
  exact (lt_irrefl _ (((hqa q).2 h1).trans h2))

/-- The pair of local entropies of the fibre measures `μ_ω = κ ω` is jointly measurable in
the label and the point. Blueprint node `meas:integral`. -/
theorem measurable_localEntropy_kernel {T : X → X} (hT : Continuous T) (κ : Kernel Ω X)
    [IsFiniteKernel κ] : Measurable fun p : Ω × X ↦ localEntropy (κ p.1) T p.2 := by
  have hball : ∀ (n : ℕ) (ε : ℝ),
      Measurable fun p : Ω × X ↦ κ p.1 (bowenBall T n p.2 ε) := by
    intro n ε
    have hD : MeasurableSet {q : (Ω × X) × X | q.2 ∈ bowenBall T n q.1.2 ε} := by
      simp only [mem_bowenBall_iff, ofPred_forall]
      refine MeasurableSet.iInter fun k ↦ MeasurableSet.iInter fun _ ↦ measurableSet_lt ?_
        measurable_const
      exact ((hT.iterate k).measurable.comp (measurable_snd.comp measurable_fst)).dist
        ((hT.iterate k).measurable.comp measurable_snd)
    exact Kernel.measurable_kernel_prodMk_left (κ := Kernel.prodMkRight X κ) hD
  have hrate : ∀ (n : ℕ) (ε : ℝ),
      Measurable fun p : Ω × X ↦ localEntropyRate (κ p.1) T p.2 n ε := fun n ε ↦
    (infoBits_antitone.measurable.comp (hball n ε)).div_const _
  have hAt : ∀ ε : ℝ, Measurable fun p : Ω × X ↦ localEntropyAt (κ p.1) T p.2 ε := fun ε ↦
    (Measurable.liminf fun n ↦ hrate n ε).prodMk (Measurable.limsup fun n ↦ hrate n ε)
  exact (Measurable.iSup fun p ↦ (hAt (dyadicRadius p)).fst).prodMk
    (Measurable.iSup fun p ↦ (hAt (dyadicRadius p)).snd)

/-- Theorem 7.3(a): for an integral decomposition `μ = ∫ μ_ω dQ(ω)`,
`Φ_{μ_ω}(x) ≤ Φ_μ(x)` coordinatewise for `M`-almost every `(ω, x)`, where `M = Q ⊗ κ`.
Blueprint node `meas:integral`. -/
theorem ae_compProd_localEntropy_le {T : X → X} (hT : Continuous T) (Q : Measure Ω)
    [IsFiniteMeasure Q] (κ : Kernel Ω X) [IsFiniteKernel κ] :
    ∀ᵐ p ∂(Q ⊗ₘ κ), (localEntropy (κ p.1) T p.2).1 ≤ (localEntropy (Q.bind κ) T p.2).1 ∧
      (localEntropy (κ p.1) T p.2).2 ≤ (localEntropy (Q.bind κ) T p.2).2 := by
  have hK := measurable_localEntropy_kernel hT κ
  have hμ : Measurable fun p : Ω × X ↦ localEntropy (Q.bind κ) T p.2 :=
    (measurable_localEntropy (Q.bind κ) hT).comp measurable_snd
  refine Measure.ae_compProd_of_ae_ae ((measurableSet_le hK.fst hμ.fst).inter
    (measurableSet_le hK.snd hμ.snd)) (Eventually.of_forall fun ω ↦ ?_)
  exact ae_localEntropy_le hT (Q.bind κ) (κ ω)

/-- Theorem 7.3(b): integral affinity `Λ_μ = ∫ Λ_{μ_ω} dQ(ω)`, the equality between the law
of `Φ_{μ_ω}(x)` under `M` and the entropy law of `μ`, holds if and only if
`Φ_{μ_ω}(x) = Φ_μ(x)` for `M`-almost every `(ω, x)`. Blueprint node `meas:integral`. -/
theorem kernelEntropyLaw_eq_iff {T : X → X} (hT : Continuous T) (Q : Measure Ω)
    [IsFiniteMeasure Q] (κ : Kernel Ω X) [IsFiniteKernel κ] :
    Measure.map (fun p : Ω × X ↦ localEntropy (κ p.1) T p.2) (Q ⊗ₘ κ) =
        entropyLaw (Q.bind κ) T ↔
      ∀ᵐ p ∂(Q ⊗ₘ κ), localEntropy (κ p.1) T p.2 = localEntropy (Q.bind κ) T p.2 := by
  set M := Q ⊗ₘ κ
  have hK := measurable_localEntropy_kernel hT κ
  have hΦ := measurable_localEntropy (Q.bind κ) hT
  have hΦ2 : Measurable fun p : Ω × X ↦ localEntropy (Q.bind κ) T p.2 :=
    hΦ.comp measurable_snd
  have hS : Measure.map Prod.snd M = Q.bind κ := Measure.snd_compProd Q κ
  have hlaw : entropyLaw (Q.bind κ) T =
      Measure.map (fun p : Ω × X ↦ localEntropy (Q.bind κ) T p.2) M := by
    calc entropyLaw (Q.bind κ) T
        = Measure.map (localEntropy (Q.bind κ) T) (Measure.map Prod.snd M) := by
          rw [hS]; rfl
      _ = _ := Measure.map_map hΦ measurable_snd
  rw [hlaw]
  constructor
  · intro h
    have hcoord : ∀ (f : ℝ≥0∞ × ℝ≥0∞ → ℝ≥0∞), Measurable f →
        Measure.map (fun p : Ω × X ↦ f (localEntropy (κ p.1) T p.2)) M =
          Measure.map (fun p : Ω × X ↦ f (localEntropy (Q.bind κ) T p.2)) M := by
      intro f hf
      have h' := congrArg (Measure.map f) h
      rw [Measure.map_map hf hK, Measure.map_map hf hΦ2] at h'
      exact h'
    have hle := ae_compProd_localEntropy_le hT Q κ
    have h1 := ae_eq_of_ae_le_of_map_eq hK.fst hΦ2.fst
      (hle.mono fun _ hp ↦ hp.1) (hcoord Prod.fst measurable_fst)
    have h2 := ae_eq_of_ae_le_of_map_eq hK.snd hΦ2.snd
      (hle.mono fun _ hp ↦ hp.2) (hcoord Prod.snd measurable_snd)
    filter_upwards [h1, h2] with p hp1 hp2
    exact Prod.ext hp1 hp2
  · exact Measure.map_congr

/-- Theorem 7.3(c): the Feng–Huang entropies are superaffine on integral decompositions,
`h̲_μ(T) ≥ ∫ h̲_{μ_ω}(T) dQ(ω)` and `h̄_μ(T) ≥ ∫ h̄_{μ_ω}(T) dQ(ω)`.
Blueprint node `meas:integral`. -/
theorem lintegral_measureEntropy_le {T : X → X} (hT : Continuous T) (Q : Measure Ω)
    [IsFiniteMeasure Q] (κ : Kernel Ω X) [IsFiniteKernel κ] :
    ∫⁻ ω, (measureEntropy (κ ω) T).1 ∂Q ≤ (measureEntropy (Q.bind κ) T).1 ∧
      ∫⁻ ω, (measureEntropy (κ ω) T).2 ∂Q ≤ (measureEntropy (Q.bind κ) T).2 := by
  have hK := measurable_localEntropy_kernel hT κ
  have hΦ := measurable_localEntropy (Q.bind κ) hT
  have hle := ae_compProd_localEntropy_le hT Q κ
  have hsnd : ∀ g : ℝ≥0∞ × ℝ≥0∞ → ℝ≥0∞, Measurable g →
      ∫⁻ x, g (localEntropy (Q.bind κ) T x) ∂(Q.bind κ) =
        ∫⁻ p, g (localEntropy (Q.bind κ) T p.2) ∂(Q ⊗ₘ κ) := by
    intro g hg
    have hS : Measure.map Prod.snd (Q ⊗ₘ κ) = Q.bind κ := Measure.snd_compProd Q κ
    calc ∫⁻ x, g (localEntropy (Q.bind κ) T x) ∂(Q.bind κ)
        = ∫⁻ x, g (localEntropy (Q.bind κ) T x) ∂(Measure.map Prod.snd (Q ⊗ₘ κ)) := by
          rw [hS]
      _ = _ := lintegral_map (hg.comp hΦ) measurable_snd
  simp only [measureEntropy]
  constructor
  · rw [← Measure.lintegral_compProd hK.fst, hsnd Prod.fst measurable_fst]
    exact lintegral_mono_ae (hle.mono fun _ hp ↦ hp.1)
  · rw [← Measure.lintegral_compProd hK.snd, hsnd Prod.snd measurable_snd]
    exact lintegral_mono_ae (hle.mono fun _ hp ↦ hp.2)

end integral

end Kolmogorov.PointToSet
