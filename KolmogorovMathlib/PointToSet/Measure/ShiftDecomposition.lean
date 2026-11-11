/-
Copyright (c) 2026 Emma Dinowitz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emma Dinowitz
-/
import KolmogorovMathlib.PointToSet.Measure.ShiftDecompositionAux
import KolmogorovMathlib.PointToSet.Measure.ShiftSmoothAux
import KolmogorovMathlib.PointToSet.Measure.ShiftGeneric
import KolmogorovMathlib.PointToSet.Measure.IntegralAffinity
import KolmogorovMathlib.PointToSet.Measure.Decomposition

/-!
# Integral decompositions on a shift

Examples and criteria for integral affinity on a one-sided shift (E. Dinowitz, *Entropy of
non-invariant measures and orbit complexity of random points*, §§7.2–7.3). The setting is that
of §7.1: a kernel `κ : Kernel Ω X` (`μ_ω = κ ω`), a label measure `Q` (the paper's `P`),
`μ = Q.bind κ` and `M = Q ⊗ₘ κ`; integral affinity is the equality
`Measure.map (fun p ↦ localEntropy (κ p.1) T p.2) M = entropyLaw μ T`.

* Proposition 7.6 (information density `i_n(ω, x) = log₂ (μ_ω[x↾n] / μ[x↾n])`, `infoDensity`):
  (i) `ae_neg_logb_eq_add_infoDensity`, `ae_eventually_neg_two_logb_le_infoDensity`;
  (ii) `integralAffinity_of_tendsto_infoDensity`, `integralAffinity_iff_tendsto_infoDensity`;
  (iii) `ae_tendsto_infoDensity_of_absolutelyContinuous` (martingale convergence along
  cylinders, `ae_tendsto_logb_ratio_cylinder`). The identity `∫ i_n dM = I(ω; x↾n)` is not
  stated.
* Example 7.4(3) (invariant fibres): `map_localEntropy_diagKernel_ne_entropyLaw`.
* Example 7.4(2) (any gap): `localEntropy_gapKernel`, `bind_gapKernel`,
  `integralAffinity_gapKernel_iff`.
* Example 7.8 (zero mutual information rate is not enough): `ae_localEntropy_revealKernel`
  (`Φ_{μ_ω} = (1/2, 1)` almost everywhere), `integral_infoDensity_revealKernel_le`
  (`∫ i_n dM = O(n / log n)`), `ae_frequently_half_le_infoDensity_revealKernel`,
  `map_localEntropy_revealKernel_ne_entropyLaw`.
* Remark 7.7 (smooth families): `ae_infoDensity_le_smoothFamily` (`i_n ≤ 3 log₂ n + O(1)`) and
  `integralAffinity_smoothFamily`, with the kernel given abstractly by its values.

All statements are proved. Helper material is in `ShiftDecompositionAux` and
`ShiftSmoothAux`; Proposition 7.10 is in `ShiftGeneric`.

Blueprint node `meas:examples`.
-/

namespace Kolmogorov.PointToSet

open Filter Set MeasureTheory ProbabilityTheory
open scoped Topology ENNReal Computability

/-! ### The information density (Proposition 7.6) -/

section density

variable {α : Type*} [MetricSpace (ℕ → α)] [MeasurableSpace (ℕ → α)] {Ω : Type*}
  [MeasurableSpace Ω]

/-- The information density `i_n(ω, x) = log₂ (μ_ω[x↾n] / μ[x↾n])` of Proposition 7.6, for a
kernel `κ` (`μ_ω = κ ω`) and a measure `μ` (in the applications `μ = Q.bind κ`). It is a real
number, with the junk value `log₂ 0 = 0` when one of the masses vanishes; both masses are
positive and finite `M`-almost everywhere (`ae_compProd_cylinder_ne_zero`), which is where the
paper defines `i_n`. Blueprint node `meas:examples`. -/
noncomputable def infoDensity (μ : Measure (ℕ → α)) (κ : Kernel Ω (ℕ → α)) (n : ℕ)
    (p : Ω × (ℕ → α)) : ℝ :=
  Real.logb 2 ((κ p.1 (PiNat.cylinder p.2 n)).toReal / (μ (PiNat.cylinder p.2 n)).toReal)

variable [BorelSpace (ℕ → α)] {β : ℝ}

/-- `M`-almost everywhere both cylinder masses `μ_ω[x↾n]` and `μ[x↾n]` are positive, for every
`n`. -/
theorem ae_compProd_cylinder_ne_zero [Countable α] (hβ : 0 < β) (hβ₁ : β < 1)
    (hd : ∀ x y : ℕ → α, x ≠ y → dist x y = β ^ PiNat.firstDiff x y) (Q : Measure Ω)
    [IsFiniteMeasure Q] (κ : Kernel Ω (ℕ → α)) [IsFiniteKernel κ] :
    ∀ᵐ p ∂(Q ⊗ₘ κ), ∀ n, κ p.1 (PiNat.cylinder p.2 n) ≠ 0 ∧
      (Q.bind κ) (PiNat.cylinder p.2 n) ≠ 0 := by
  have hK : ∀ᵐ p ∂(Q ⊗ₘ κ), ∀ n, κ p.1 (PiNat.cylinder p.2 n) ≠ 0 := by
    have hmeas : MeasurableSet {p : Ω × (ℕ → α) | ∀ n, κ p.1 (PiNat.cylinder p.2 n) ≠ 0} := by
      have h : {p : Ω × (ℕ → α) | ∀ n, κ p.1 (PiNat.cylinder p.2 n) ≠ 0} =
          ⋂ n, ((fun p : Ω × (ℕ → α) ↦ κ p.1 (PiNat.cylinder p.2 n)) ⁻¹' {0})ᶜ := by
        ext p
        simp
      rw [h]
      exact MeasurableSet.iInter fun n ↦
        ((measurable_kernel_cylinder hβ hβ₁ hd κ n) (measurableSet_singleton 0)).compl
    exact Measure.ae_compProd_of_ae_ae hmeas
      (.of_forall fun ω ↦ ae_measure_cylinder_ne_zero hβ hβ₁ hd (κ ω))
  have hμ : ∀ᵐ p ∂(Q ⊗ₘ κ), ∀ n, (Q.bind κ) (PiNat.cylinder p.2 n) ≠ 0 := by
    have h : ∀ᵐ x ∂(Q ⊗ₘ κ).snd, ∀ n, (Q.bind κ) (PiNat.cylinder x n) ≠ 0 := by
      rw [Measure.snd_compProd]
      exact ae_measure_cylinder_ne_zero hβ hβ₁ hd _
    exact ae_of_ae_map (μ := Q ⊗ₘ κ) measurable_snd.aemeasurable h
  filter_upwards [hK, hμ] with p h1 h2 n
  exact ⟨h1 n, h2 n⟩

/-- The cylinder form of the domination lemma (Lemma 7.1) for an integral decomposition: for
`M`-almost every `(ω, x)`, `μ[x↾n] ≤ n² μ_ω[x↾n]` for all sufficiently large `n`. -/
theorem ae_eventually_measure_cylinder_le [Countable α] (hβ : 0 < β) (hβ₁ : β < 1)
    (hd : ∀ x y : ℕ → α, x ≠ y → dist x y = β ^ PiNat.firstDiff x y) (Q : Measure Ω)
    [IsFiniteMeasure Q] (κ : Kernel Ω (ℕ → α)) [IsFiniteKernel κ] (μ : Measure (ℕ → α))
    [IsFiniteMeasure μ] :
    ∀ᵐ p ∂(Q ⊗ₘ κ), ∀ᶠ n : ℕ in atTop,
      μ (PiNat.cylinder p.2 n) ≤ (n : ℝ≥0∞) ^ 2 * κ p.1 (PiNat.cylinder p.2 n) := by
  set t : ℕ → Set (Ω × (ℕ → α)) := fun n ↦
    {p | (n : ℝ≥0∞) ^ 2 * κ p.1 (PiNat.cylinder p.2 n) < μ (PiNat.cylinder p.2 n)}
  set s : ℕ → Set (Ω × (ℕ → α)) := fun n ↦ {p | 1 ≤ n ∧ p ∈ t n}
  have ht : ∀ n, MeasurableSet (t n) := fun n ↦
    measurableSet_lt (measurable_const.mul (measurable_kernel_cylinder hβ hβ₁ hd κ n))
      ((measurable_measure_cylinder hβ hβ₁ hd μ n).comp measurable_snd)
  have key : ∀ n, (Q ⊗ₘ κ) (s n) ≤ (Q univ * μ univ) * ENNReal.ofReal (1 / (n : ℝ) ^ 2) := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [s]
    have h0 : ((n : ℝ≥0∞) ^ 2) ≠ 0 := pow_ne_zero _ (by exact_mod_cast hn.ne')
    have htop : ((n : ℝ≥0∞) ^ 2) ≠ ⊤ := ENNReal.pow_ne_top (ENNReal.natCast_ne_top n)
    calc (Q ⊗ₘ κ) (s n) ≤ (Q ⊗ₘ κ) (t n) := measure_mono fun p hp ↦ hp.2
      _ = ∫⁻ ω, κ ω (Prod.mk ω ⁻¹' t n) ∂Q := Measure.compProd_apply (ht n)
      _ ≤ ∫⁻ _, μ univ / (n : ℝ≥0∞) ^ 2 ∂Q := lintegral_mono fun ω ↦
          measure_setOf_mul_lt_measure_cylinder_le hβ hβ₁ hd μ (κ ω) n h0 htop
      _ = (Q univ * μ univ) * ENNReal.ofReal (1 / (n : ℝ) ^ 2) := by
          rw [lintegral_const, div_eq_mul_inv, ENNReal.ofReal_div_of_pos (by positivity),
            ENNReal.ofReal_one, ENNReal.ofReal_pow (Nat.cast_nonneg _), ENNReal.ofReal_natCast,
            one_div]
          ring
  have hsum : ∑' n, (Q ⊗ₘ κ) (s n) ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum key)
    rw [ENNReal.tsum_mul_left, ← ENNReal.ofReal_tsum_of_nonneg (fun n ↦ by positivity)
      (Real.summable_one_div_nat_pow.2 one_lt_two)]
    exact ENNReal.mul_ne_top (ENNReal.mul_ne_top (measure_ne_top Q univ)
      (measure_ne_top μ univ)) ENNReal.ofReal_ne_top
  filter_upwards [ae_eventually_notMem hsum] with p hp
  filter_upwards [hp, eventually_ge_atTop 1] with n hn h1
  simp only [s, t, mem_ofPred_eq, h1, true_and, not_lt] at hn
  exact hn

/-- Positive finite cylinder masses: `(μ[x↾n]).toReal ≠ 0`. -/
private lemma toReal_ne_zero_of {q : ℝ≥0∞} (h0 : q ≠ 0) (ht : q ≠ ⊤) : q.toReal ≠ 0 :=
  (ENNReal.toReal_pos h0 ht).ne'

/-- Proposition 7.6(i), first part: `-log₂ μ[x↾n] = -log₂ μ_ω[x↾n] + i_n(ω, x)` for all `n`,
for `M`-almost every `(ω, x)` (`M = Q ⊗ κ`, `μ = Q.bind κ`). Blueprint node `meas:examples`. -/
theorem ae_neg_logb_eq_add_infoDensity [Countable α] (hβ : 0 < β) (hβ₁ : β < 1)
    (hd : ∀ x y : ℕ → α, x ≠ y → dist x y = β ^ PiNat.firstDiff x y) (Q : Measure Ω)
    [IsFiniteMeasure Q] (κ : Kernel Ω (ℕ → α)) [IsFiniteKernel κ] :
    ∀ᵐ p ∂(Q ⊗ₘ κ), ∀ n, -Real.logb 2 ((Q.bind κ) (PiNat.cylinder p.2 n)).toReal =
      -Real.logb 2 (κ p.1 (PiNat.cylinder p.2 n)).toReal + infoDensity (Q.bind κ) κ n p := by
  filter_upwards [ae_compProd_cylinder_ne_zero hβ hβ₁ hd Q κ] with p hp n
  rw [infoDensity, Real.logb_div (toReal_ne_zero_of (hp n).1 (measure_ne_top _ _))
    (toReal_ne_zero_of (hp n).2 (measure_ne_top _ _))]
  ring

/-- Proposition 7.6(i), second part: `i_n ≥ -2 log₂ n` for all sufficiently large `n`, for
`M`-almost every `(ω, x)`. Blueprint node `meas:examples`. -/
theorem ae_eventually_neg_two_logb_le_infoDensity [Countable α] (hβ : 0 < β) (hβ₁ : β < 1)
    (hd : ∀ x y : ℕ → α, x ≠ y → dist x y = β ^ PiNat.firstDiff x y) (Q : Measure Ω)
    [IsFiniteMeasure Q] (κ : Kernel Ω (ℕ → α)) [IsFiniteKernel κ] :
    ∀ᵐ p ∂(Q ⊗ₘ κ), ∀ᶠ n : ℕ in atTop,
      -(2 * Real.logb 2 n) ≤ infoDensity (Q.bind κ) κ n p := by
  filter_upwards [ae_compProd_cylinder_ne_zero hβ hβ₁ hd Q κ,
    ae_eventually_measure_cylinder_le hβ hβ₁ hd Q κ (Q.bind κ)] with p hp hle
  filter_upwards [hle, eventually_ge_atTop 1] with n hn h1
  set a := (Q.bind κ) (PiNat.cylinder p.2 n)
  set b := κ p.1 (PiNat.cylinder p.2 n)
  have ha : 0 < a.toReal := ENNReal.toReal_pos (hp n).2 (measure_ne_top _ _)
  have hb : 0 < b.toReal := ENNReal.toReal_pos (hp n).1 (measure_ne_top _ _)
  have hn0 : (0 : ℝ) < n := by exact_mod_cast h1
  have hreal : a.toReal ≤ (n : ℝ) ^ 2 * b.toReal := by
    have := ENNReal.toReal_mono (ENNReal.mul_ne_top (ENNReal.pow_ne_top
      (ENNReal.natCast_ne_top n)) (measure_ne_top _ _)) hn
    simpa [ENNReal.toReal_mul] using this
  have hlog := Real.logb_le_logb_of_le one_lt_two ha hreal
  rw [Real.logb_mul (by positivity) hb.ne', Real.logb_pow] at hlog
  rw [infoDensity, Real.logb_div hb.ne' ha.ne']
  push_cast at hlog
  linarith

omit [MetricSpace (ℕ → α)] [MeasurableSpace (ℕ → α)] [BorelSpace (ℕ → α)] in
/-- If `u n / n → 0` then `ofReal (u n) / n → 0` in `ℝ≥0∞`. -/
private lemma tendsto_ofReal_div_natCast {u : ℕ → ℝ}
    (h : Tendsto (fun n : ℕ ↦ u n / n) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ ↦ ENNReal.ofReal (u n) / n) atTop (𝓝 0) := by
  have := ENNReal.tendsto_ofReal h
  rw [ENNReal.ofReal_zero] at this
  refine this.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  rw [ENNReal.ofReal_div_of_pos (by exact_mod_cast hn), ENNReal.ofReal_natCast]

omit [MetricSpace (ℕ → α)] [MeasurableSpace (ℕ → α)] [BorelSpace (ℕ → α)] in
/-- Comparison of the information rates of two positive finite masses `a`, `b`:
`I(a)/n ≤ I(b)/n + ofReal(log₂ b - log₂ a)/n`. -/
private lemma infoBits_div_le {a b : ℝ≥0∞} (ha0 : a ≠ 0) (hb0 : b ≠ 0) (n : ℕ) :
    infoBits a / n ≤
      infoBits b / n + ENNReal.ofReal (Real.logb 2 b.toReal - Real.logb 2 a.toReal) / n := by
  rw [← ENNReal.add_div]
  refine ENNReal.div_le_div_right ?_ _
  rw [infoBits_of_ne ha0, infoBits_of_ne hb0]
  calc ENNReal.ofReal (-Real.logb 2 a.toReal)
      = ENNReal.ofReal (-Real.logb 2 b.toReal +
          (Real.logb 2 b.toReal - Real.logb 2 a.toReal)) := by congr 1; ring
    _ ≤ _ := ENNReal.ofReal_add_le

omit [BorelSpace (ℕ → α)] in
/-- On a shift, if `i_n / n → 0` at a point `(ω, x)` where all cylinder masses are positive
and finite, then `Φ_{μ_ω}(x) = Φ_μ(x)`. -/
private lemma localEntropy_eq_of_tendsto [Countable α] (hβ : 0 < β) (hβ₁ : β < 1)
    (hd : ∀ x y : ℕ → α, x ≠ y → dist x y = β ^ PiNat.firstDiff x y) (μ : Measure (ℕ → α))
    [IsFiniteMeasure μ] (κ : Kernel Ω (ℕ → α)) [IsFiniteKernel κ] (p : Ω × (ℕ → α))
    (hp : ∀ n, κ p.1 (PiNat.cylinder p.2 n) ≠ 0 ∧ μ (PiNat.cylinder p.2 n) ≠ 0)
    (h : Tendsto (fun n : ℕ ↦ infoDensity μ κ n p / n) atTop (𝓝 0)) :
    localEntropy (κ p.1) shiftMap p.2 = localEntropy μ shiftMap p.2 := by
  have hi : ∀ n, infoDensity μ κ n p = Real.logb 2 (κ p.1 (PiNat.cylinder p.2 n)).toReal -
      Real.logb 2 (μ (PiNat.cylinder p.2 n)).toReal := fun n ↦ by
    rw [infoDensity, Real.logb_div (toReal_ne_zero_of (hp n).1 (measure_ne_top _ _))
      (toReal_ne_zero_of (hp n).2 (measure_ne_top _ _))]
  have hd1 := tendsto_ofReal_div_natCast h
  have hd2 : Tendsto (fun n : ℕ ↦ ENNReal.ofReal (-infoDensity μ κ n p) / n) atTop (𝓝 0) :=
    tendsto_ofReal_div_natCast (by simpa [neg_div] using h.neg)
  have h1 : ∀ n : ℕ, infoBits (μ (PiNat.cylinder p.2 n)) / n ≤
      infoBits (κ p.1 (PiNat.cylinder p.2 n)) / n +
        ENNReal.ofReal (infoDensity μ κ n p) / n := fun n ↦ by
    rw [hi]; exact infoBits_div_le (hp n).2 (hp n).1 n
  have h2 : ∀ n : ℕ, infoBits (κ p.1 (PiNat.cylinder p.2 n)) / n ≤
      infoBits (μ (PiNat.cylinder p.2 n)) / n +
        ENNReal.ofReal (-infoDensity μ κ n p) / n := fun n ↦ by
    rw [hi, neg_sub]; exact infoBits_div_le (hp n).1 (hp n).2 n
  rw [localEntropy_shiftMap hβ hβ₁ hd, localEntropy_shiftMap hβ hβ₁ hd]
  exact Prod.ext
    (le_antisymm (liminf_le_liminf_of_le_add_tendsto_zero (.of_forall h2) hd2)
      (liminf_le_liminf_of_le_add_tendsto_zero (.of_forall h1) hd1))
    (le_antisymm (limsup_le_limsup_of_le_add_tendsto_zero (.of_forall h2) hd2)
      (limsup_le_limsup_of_le_add_tendsto_zero (.of_forall h1) hd1))

/-- Proposition 7.6(ii), first part: on a shift, if `i_n / n → 0` for `M`-almost every
`(ω, x)`, then integral affinity `Λ_μ = ∫ Λ_{μ_ω} dQ(ω)` holds, in the form of the equality
between the law of `Φ_{μ_ω}(x)` under `M = Q ⊗ κ` and the entropy law of `μ = Q.bind κ`.

The alphabet is only assumed countable (the paper: finite); `SecondCountableTopology` is
automatic for a first-difference metric on a countable alphabet and is assumed for
convenience. Blueprint node `meas:examples`. -/
theorem integralAffinity_of_tendsto_infoDensity [Countable α]
    [SecondCountableTopology (ℕ → α)] (hβ : 0 < β) (hβ₁ : β < 1)
    (hd : ∀ x y : ℕ → α, x ≠ y → dist x y = β ^ PiNat.firstDiff x y) (Q : Measure Ω)
    [IsFiniteMeasure Q] (κ : Kernel Ω (ℕ → α)) [IsFiniteKernel κ]
    (h : ∀ᵐ p ∂(Q ⊗ₘ κ), Tendsto (fun n : ℕ ↦ infoDensity (Q.bind κ) κ n p / n) atTop (𝓝 0)) :
    Measure.map (fun p : Ω × (ℕ → α) ↦ localEntropy (κ p.1) shiftMap p.2) (Q ⊗ₘ κ) =
      entropyLaw (Q.bind κ) shiftMap := by
  rw [kernelEntropyLaw_eq_iff (continuous_shiftMap hβ hβ₁ hd)]
  filter_upwards [h, ae_compProd_cylinder_ne_zero hβ hβ₁ hd Q κ] with p hp hpos
  exact localEntropy_eq_of_tendsto hβ hβ₁ hd _ κ p hpos hp

/-- Proposition 7.6(ii), second part: on a shift, if the local entropies of `μ_ω` exist as
finite limits at `M`-almost every `(ω, x)` (`h̲_{μ_ω}(σ, x) = h̄_{μ_ω}(σ, x) < ∞`), then
integral affinity holds if and only if `i_n / n → 0` `M`-almost everywhere.

As in `integralAffinity_of_tendsto_infoDensity`, the alphabet is countable, `Q` and `κ` are
probability measures (the paper's setting). Blueprint node `meas:examples`. -/
theorem integralAffinity_iff_tendsto_infoDensity [Countable α]
    [SecondCountableTopology (ℕ → α)] (hβ : 0 < β) (hβ₁ : β < 1)
    (hd : ∀ x y : ℕ → α, x ≠ y → dist x y = β ^ PiNat.firstDiff x y) (Q : Measure Ω)
    [IsProbabilityMeasure Q] (κ : Kernel Ω (ℕ → α)) [IsMarkovKernel κ]
    (hfin : ∀ᵐ p ∂(Q ⊗ₘ κ), (localEntropy (κ p.1) shiftMap p.2).1 =
      (localEntropy (κ p.1) shiftMap p.2).2 ∧ (localEntropy (κ p.1) shiftMap p.2).2 ≠ ⊤) :
    Measure.map (fun p : Ω × (ℕ → α) ↦ localEntropy (κ p.1) shiftMap p.2) (Q ⊗ₘ κ) =
        entropyLaw (Q.bind κ) shiftMap ↔
      ∀ᵐ p ∂(Q ⊗ₘ κ), Tendsto (fun n : ℕ ↦ infoDensity (Q.bind κ) κ n p / n) atTop (𝓝 0) := by
  refine ⟨fun hA ↦ ?_, integralAffinity_of_tendsto_infoDensity hβ hβ₁ hd Q κ⟩
  rw [kernelEntropyLaw_eq_iff (continuous_shiftMap hβ hβ₁ hd)] at hA
  filter_upwards [hA, hfin, ae_compProd_cylinder_ne_zero hβ hβ₁ hd Q κ] with p hp hf hpos
  set c := (localEntropy (κ p.1) shiftMap p.2).2
  -- the information rates of a mass sequence with equal lower and upper limit `c < ∞`
  have hconv : ∀ ν : Measure (ℕ → α), IsProbabilityMeasure ν → (∀ n, ν (PiNat.cylinder p.2 n) ≠ 0) →
      localEntropy ν shiftMap p.2 = (c, c) →
      Tendsto (fun n : ℕ ↦ -Real.logb 2 (ν (PiNat.cylinder p.2 n)).toReal / n) atTop
        (𝓝 c.toReal) := by
    intro ν hν hν0 hΦ
    rw [localEntropy_shiftMap hβ hβ₁ hd, Prod.ext_iff] at hΦ
    have hT : Tendsto (fun n : ℕ ↦ infoBits (ν (PiNat.cylinder p.2 n)) / n) atTop (𝓝 c) :=
      tendsto_of_liminf_eq_limsup hΦ.1 hΦ.2
    refine ((ENNReal.tendsto_toReal hf.2).comp hT).congr fun n ↦ ?_
    have hle : (ν (PiNat.cylinder p.2 n)).toReal ≤ 1 := by
      have := ENNReal.toReal_mono ENNReal.one_ne_top
        (prob_le_one (μ := ν) (s := PiNat.cylinder p.2 n))
      simpa using this
    have hnn : 0 ≤ -Real.logb 2 (ν (PiNat.cylinder p.2 n)).toReal :=
      neg_nonneg.2 (Real.logb_nonpos one_lt_two ENNReal.toReal_nonneg hle)
    simp only [Function.comp_apply]
    rw [infoBits_of_ne (hν0 n), ENNReal.toReal_div, ENNReal.toReal_ofReal hnn,
      ENNReal.toReal_natCast]
  have hκ := hconv (κ p.1) inferInstance (fun n ↦ (hpos n).1)
    (Prod.ext hf.1 rfl)
  have hμ := hconv (Q.bind κ) inferInstance (fun n ↦ (hpos n).2)
    (hp ▸ Prod.ext hf.1 rfl)
  have hsub := hμ.sub hκ
  rw [sub_self] at hsub
  refine hsub.congr fun n ↦ ?_
  rw [infoDensity, Real.logb_div (toReal_ne_zero_of (hpos n).1 (measure_ne_top _ _))
    (toReal_ne_zero_of (hpos n).2 (measure_ne_top _ _))]
  ring

/-- Proposition 7.6(iii): if `μ_ω ≪ μ` for `Q`-almost every `ω`, then `i_n(ω, x)` converges to
a finite limit for `M`-almost every `(ω, x)`.

The paper's proof: `2^{i_n}` is, under `Q ⊗ μ`, the density of `M` on the σ-algebra generated
by `ω` and `x↾n`, a martingale closed by `dM/d(Q ⊗ μ)`, which is positive and finite
`M`-almost everywhere. Blueprint node `meas:examples`. -/
theorem ae_tendsto_infoDensity_of_absolutelyContinuous [Countable α] (hβ : 0 < β)
    (hβ₁ : β < 1) (hd : ∀ x y : ℕ → α, x ≠ y → dist x y = β ^ PiNat.firstDiff x y)
    (Q : Measure Ω) [IsProbabilityMeasure Q] (κ : Kernel Ω (ℕ → α)) [IsMarkovKernel κ]
    (h : ∀ᵐ ω ∂Q, κ ω ≪ Q.bind κ) :
    ∀ᵐ p ∂(Q ⊗ₘ κ), ∃ c : ℝ, Tendsto (fun n : ℕ ↦ infoDensity (Q.bind κ) κ n p) atTop (𝓝 c) := by
  have hm : ∀ n, Measurable fun p : Ω × (ℕ → α) ↦ infoDensity (Q.bind κ) κ n p := by
    intro n
    have h1 := measurable_kernel_cylinder hβ hβ₁ hd κ n
    have h2 : Measurable fun p : Ω × (ℕ → α) ↦ (Q.bind κ) (PiNat.cylinder p.2 n) :=
      (measurable_measure_cylinder hβ hβ₁ hd (Q.bind κ) n).comp measurable_snd
    unfold infoDensity Real.logb
    exact (Real.measurable_log.comp (h1.ennreal_toReal.div h2.ennreal_toReal)).div_const _
  refine Measure.ae_compProd_of_ae_ae
    (StronglyMeasurable.measurableSet_exists_tendsto fun n ↦ (hm n).stronglyMeasurable) ?_
  filter_upwards [h] with ω hω
  have := ae_tendsto_logb_ratio_cylinder hβ hβ₁ hd hω
  filter_upwards [this] with x hx
  exact hx

end density

/-! ### Example 7.4(3): invariant fibres -/

section fibres

attribute [local instance] cantorMetricSpace

/-- The map `T = id × σ` on `X = {0,1}^ℕ × {0,1}^ℕ` (Example 7.4(3)); `X` carries the maximum
metric (Mathlib's product metric). Blueprint node `meas:examples`. -/
def fibreMap : (ℕ → Bool) × (ℕ → Bool) → (ℕ → Bool) × (ℕ → Bool) :=
  Prod.map id shiftMap

/-- The measure `μ'` of Example 7.4(3): the law of `(y, y)` for a fair `y`.
Blueprint node `meas:examples`. -/
noncomputable def diagMeasure : Measure ((ℕ → Bool) × (ℕ → Bool)) :=
  uniformMeasure.map fun y ↦ (y, y)

/-- The disintegration of Example 7.4(3): the label is `ω = y`, and `μ'_ω = δ_{(ω, ω)}`.
Blueprint node `meas:examples`. -/
noncomputable def diagKernel : Kernel (ℕ → Bool) ((ℕ → Bool) × (ℕ → Bool)) :=
  Kernel.deterministic (fun y ↦ (y, y)) (measurable_id.prodMk measurable_id)

instance : IsMarkovKernel diagKernel := by
  unfold diagKernel; infer_instance

/-- `μ' = ∫ μ'_ω dP(ω)` for the fair-coin measure `P`. Blueprint node `meas:examples`. -/
theorem bind_diagKernel : uniformMeasure.bind diagKernel = diagMeasure :=
  Measure.deterministic_comp_eq_map _

/-- The map `id × σ` is continuous. -/
theorem continuous_fibreMap : Continuous fibreMap :=
  continuous_id.prodMap (continuous_shiftMap (by norm_num) (by norm_num) cantor_hd)

/-- The label `ω = y` (the first coordinate) is a `T`-invariant function.
Blueprint node `meas:examples`. -/
theorem fst_comp_fibreMap : Prod.fst ∘ fibreMap = Prod.fst := rfl

/-- The fibres `{ω} × {0,1}^ℕ` are closed and `T`-invariant (`T⁻¹ F = F`).
Blueprint node `meas:examples`. -/
theorem isClosed_fibre_and_preimage_eq (ω : ℕ → Bool) :
    IsClosed ({ω} ×ˢ (univ : Set (ℕ → Bool))) ∧
      fibreMap ⁻¹' ({ω} ×ˢ univ) = {ω} ×ˢ univ := by
  refine ⟨isClosed_singleton.prod isClosed_univ, ?_⟩
  ext ⟨a, b⟩
  simp [fibreMap]

/-- The fibre measures `μ'_ω = δ_{(ω, ω)}` are carried by their fibres. -/
theorem diagKernel_apply (ω : ℕ → Bool) : diagKernel ω = Measure.dirac (ω, ω) := by
  rw [diagKernel, Kernel.deterministic_apply]

/-- Example 7.4(3): `Φ_{μ'_ω}(ω, ω) = (0, 0)`. Blueprint node `meas:examples`. -/
theorem localEntropy_diagKernel (ω : ℕ → Bool) :
    localEntropy (diagKernel ω) fibreMap (ω, ω) = (0, 0) := by
  rw [diagKernel_apply]
  exact localEntropy_dirac _ _

/-- A Bowen ball of `id × σ` of radius `2^{-k}` about `(y, y)` is `[y↾(1+k)] × [y↾(n+k)]`. -/
private lemma bowenBall_fibreMap (y : ℕ → Bool) {n : ℕ} (hn : 1 ≤ n) (k : ℕ) :
    bowenBall fibreMap n (y, y) ((1 / 2 : ℝ) ^ k) =
      PiNat.cylinder y (1 + k) ×ˢ PiNat.cylinder y (n + k) := by
  rw [← bowenBall_shiftMap_eq_cylinder (by norm_num) (by norm_num) cantor_hd y le_rfl k,
    ← bowenBall_shiftMap_eq_cylinder (by norm_num) (by norm_num) cantor_hd y hn k]
  ext ⟨a, b⟩
  simp only [mem_bowenBall_iff, mem_prod, fibreMap, Prod.map_iterate, Function.iterate_id,
    Prod.map_apply, id, Prod.dist_eq, max_lt_iff]
  constructor
  · intro h
    exact ⟨fun j hj ↦ by
      obtain rfl : j = 0 := by omega
      simpa using (h 0 hn).1, fun j hj ↦ (h j hj).2⟩
  · rintro ⟨h1, h2⟩ j hj
    exact ⟨by simpa using h1 0 one_pos, h2 j hj⟩

/-- Example 7.4(3): `Φ_{μ'}(y, y) = (1, 1)` for every `y`: a Bowen ball of radius `2^{-k}`
about `(y, y)` meets the diagonal in the points `(y', y')` with `y'↾(n+k) = y↾(n+k)`.
Blueprint node `meas:examples`. -/
theorem localEntropy_diagMeasure (y : ℕ → Bool) :
    localEntropy diagMeasure fibreMap (y, y) = (1, 1) := by
  have hmass : ∀ k n : ℕ, 1 ≤ n →
      diagMeasure (bowenBall fibreMap n (y, y) (dyadicRadius k)) = (2 : ℝ≥0∞)⁻¹ ^ (n + k) := by
    intro k n hn
    rw [dyadicRadius, ← one_div, bowenBall_fibreMap y hn k, diagMeasure,
      Measure.map_apply (measurable_id'.prodMk measurable_id')
        ((measurableSet_cantor_cylinder y _).prod (measurableSet_cantor_cylinder y _))]
    have h : ((fun y' : ℕ → Bool ↦ (y', y')) ⁻¹'
        (PiNat.cylinder y (1 + k) ×ˢ PiNat.cylinder y (n + k))) = PiNat.cylinder y (n + k) := by
      ext y'
      simp only [mem_preimage, mem_prod]
      exact ⟨fun h ↦ h.2, fun h ↦ ⟨PiNat.cylinder_anti y (by omega) h, h⟩⟩
    rw [h, uniformMeasure_cylinder]
  have hAt : ∀ k : ℕ, localEntropyAt diagMeasure fibreMap (y, y) (dyadicRadius k) = (1, 1) := by
    intro k
    have hT : Tendsto (fun n ↦ localEntropyRate diagMeasure fibreMap (y, y) n (dyadicRadius k))
        atTop (𝓝 1) := by
      refine (tendsto_natCast_add_div_natCast k).congr' ?_
      filter_upwards [eventually_ge_atTop 1] with n hn
      rw [localEntropyRate, hmass k n hn, infoBits_two_inv_pow]
    exact Prod.ext hT.liminf_eq hT.limsup_eq
  simp only [localEntropy, hAt, iSup_const]

/-- Example 7.4(3), failure of integral affinity although the fibres are closed and invariant:
the law of `Φ_{μ'_ω}(x)` under `M = P ⊗ μ'_•` is `δ_{(0, 0)}`, while `Λ_{μ'} = δ_{(1, 1)}`.
Blueprint node `meas:examples`. -/
theorem map_localEntropy_diagKernel_ne_entropyLaw :
    Measure.map (fun p : (ℕ → Bool) × ((ℕ → Bool) × (ℕ → Bool)) ↦
        localEntropy (diagKernel p.1) fibreMap p.2) (uniformMeasure ⊗ₘ diagKernel) ≠
      entropyLaw (uniformMeasure.bind diagKernel) fibreMap := by
  have hd : Measurable fun y : ℕ → Bool ↦ (y, y) := measurable_id'.prodMk measurable_id'
  have hL : Measure.map (fun p : (ℕ → Bool) × ((ℕ → Bool) × (ℕ → Bool)) ↦
      localEntropy (diagKernel p.1) fibreMap p.2) (uniformMeasure ⊗ₘ diagKernel) =
      Measure.dirac (0, 0) := by
    rw [diagKernel, Measure.compProd_deterministic,
      Measure.map_map (measurable_localEntropy_kernel continuous_fibreMap _)
        (measurable_id'.prodMk hd)]
    have h : ((fun p : (ℕ → Bool) × ((ℕ → Bool) × (ℕ → Bool)) ↦
        localEntropy (Kernel.deterministic (fun y : ℕ → Bool ↦ (y, y)) hd p.1) fibreMap p.2) ∘
        fun a ↦ (a, (a, a))) = fun _ ↦ ((0, 0) : ℝ≥0∞ × ℝ≥0∞) := by
      funext a
      exact localEntropy_diagKernel a
    rw [h, Measure.map_const]
    simp
  have hR : entropyLaw (uniformMeasure.bind diagKernel) fibreMap = Measure.dirac (1, 1) := by
    rw [bind_diagKernel, entropyLaw, diagMeasure,
      Measure.map_map (measurable_localEntropy _ continuous_fibreMap) hd]
    have h : (localEntropy (uniformMeasure.map fun y : ℕ → Bool ↦ (y, y)) fibreMap ∘
        fun y : ℕ → Bool ↦ (y, y)) = fun _ ↦ ((1, 1) : ℝ≥0∞ × ℝ≥0∞) := by
      funext y
      exact localEntropy_diagMeasure y
    rw [h, Measure.map_const]
    simp
  rw [hL, hR]
  intro h
  have := congrArg (fun ν : Measure (ℝ≥0∞ × ℝ≥0∞) ↦ ν {((0, 0) : ℝ≥0∞ × ℝ≥0∞)}) h
  simp at this

end fibres

/-! ### Example 7.4(2): any gap -/

section gap

attribute [local instance] cantorMetricSpace

open scoped Classical in
/-- The sequence that copies `y` on the coordinates in `S` and `z` elsewhere.
Blueprint node `meas:examples`. -/
noncomputable def revealSeq (S : Set ℕ) (y z : ℕ → Bool) : ℕ → Bool :=
  fun i ↦ if i ∈ S then y i else z i

/-- `revealSeq S` is jointly measurable. -/
theorem measurable_revealSeq (S : Set ℕ) :
    Measurable fun p : (ℕ → Bool) × (ℕ → Bool) ↦ revealSeq S p.1 p.2 := by
  refine Measurable.of_eval fun i ↦ ?_
  by_cases hi : i ∈ S
  · simp only [revealSeq, hi, ite_true]
    exact (measurable_pi_apply i).comp measurable_fst
  · simp only [revealSeq, hi, ite_false]
    exact (measurable_pi_apply i).comp measurable_snd

/-- `revealSeq S y` is measurable. -/
theorem measurable_revealSeq_left (S : Set ℕ) (y : ℕ → Bool) : Measurable (revealSeq S y) :=
  (measurable_revealSeq S).comp measurable_prodMk_left

/-- The kernel of Example 7.4(2): `μ_ω` is the law of the sequence that agrees with `ω` on `S`
and is fair and independent elsewhere, i.e. `μ_ω = ⨂_i (δ_{ω i}` if `i ∈ S`, fair coin
otherwise`)`. The paper's label is `(ω_i)_{i ∈ S}`; here the label is the whole sequence `ω`
under the fair-coin measure, of which `μ_ω` only uses the coordinates in `S`.
Blueprint node `meas:examples`. -/
noncomputable def gapKernel (S : Set ℕ) : Kernel (ℕ → Bool) (ℕ → Bool) :=
  Kernel.map (Kernel.prod (Kernel.deterministic id measurable_id)
    (Kernel.const (ℕ → Bool) uniformMeasure)) fun p ↦ revealSeq S p.1 p.2

/-- `μ_ω` is the image of the fair-coin measure under `z ↦ revealSeq S ω z`. -/
theorem gapKernel_apply (S : Set ℕ) (ω : ℕ → Bool) :
    gapKernel S ω = uniformMeasure.map (revealSeq S ω) := by
  rw [gapKernel, Kernel.map_apply _ (measurable_revealSeq S), Kernel.prod_apply,
    Kernel.deterministic_apply, Kernel.const_apply, Measure.dirac_prod,
    Measure.map_map (measurable_revealSeq S) measurable_prodMk_left]
  rfl

instance (S : Set ℕ) : IsMarkovKernel (gapKernel S) :=
  ⟨fun ω ↦ by
    rw [gapKernel_apply]
    infer_instance⟩

/-- The number `#([0, n) \ S)` of coordinates below `n` outside `S`. -/
noncomputable def gapCount (S : Set ℕ) (n : ℕ) : ℕ :=
  (Iio n \ S).ncard

/-- The fair-coin measure is a product of a probability measure on `Bool`. -/
private lemma uniformMeasure_eq_infinitePi :
    ∃ c : Measure Bool, IsProbabilityMeasure c ∧
      uniformMeasure = Measure.infinitePi fun _ : ℕ ↦ c :=
  ⟨_, inferInstance, rfl⟩

/-- The fair-coin mass of a finite-dimensional cylinder: `P(z_i = x_i, i ∈ F) = 2^{-#F}`. -/
theorem uniformMeasure_pi_singleton (F : Finset ℕ) (x : ℕ → Bool) :
    uniformMeasure (Set.pi F fun i ↦ {x i}) = (2 : ℝ≥0∞)⁻¹ ^ F.card := by
  have h1 : ∀ b : Bool, uniformMeasure (Set.pi ({0} : Finset ℕ) fun _ ↦ {b}) = 2⁻¹ := by
    intro b
    have h := uniformMeasure_cylinder (fun _ ↦ b) 1
    have hc : PiNat.cylinder (fun _ : ℕ ↦ b) 1 = Set.pi ({0} : Finset ℕ) fun _ ↦ {b} := by
      ext z
      simp [PiNat.mem_cylinder_iff]
    rwa [hc, pow_one] at h
  obtain ⟨c, hc, hU⟩ := uniformMeasure_eq_infinitePi
  rw [hU] at h1 ⊢
  simp only [Measure.infinitePi_pi _ (fun _ _ ↦ measurableSet_singleton _),
    Finset.prod_singleton] at h1
  rw [Measure.infinitePi_pi _ (fun _ _ ↦ measurableSet_singleton _),
    Finset.prod_congr rfl fun i _ ↦ h1 (x i), Finset.prod_const]

/-- Example 7.4(2): if `x` agrees with `ω` on `S` then `μ_ω[x↾n] = 2^{-#([0, n) \ S)}`.
Blueprint node `meas:examples`. -/
theorem gapKernel_cylinder (S : Set ℕ) {ω x : ℕ → Bool} (hx : ∀ i ∈ S, x i = ω i) (n : ℕ) :
    gapKernel S ω (PiNat.cylinder x n) = (2 : ℝ≥0∞)⁻¹ ^ gapCount S n := by
  classical
  set F := (Finset.range n).filter (· ∉ S)
  have hpre : revealSeq S ω ⁻¹' PiNat.cylinder x n = Set.pi F fun i ↦ {x i} := by
    ext z
    simp only [mem_preimage, PiNat.mem_cylinder_iff, revealSeq, Set.mem_pi, Finset.coe_filter,
      Finset.mem_range, F]
    constructor
    · rintro h i ⟨hi, hS⟩
      simpa [hS] using h i hi
    · intro h i hi
      by_cases hS : i ∈ S
      · simp [hS, hx i hS]
      · simpa [hS] using h i ⟨hi, hS⟩
  have hcard : F.card = gapCount S n := by
    rw [gapCount, ← Set.ncard_coe_finset]
    congr 1
    ext i
    simp [F]
  rw [gapKernel_apply, Measure.map_apply (measurable_revealSeq_left S ω)
    (measurableSet_cantor_cylinder x n), hpre, uniformMeasure_pi_singleton, hcard]

/-- Example 7.4(2): `-log₂ μ_ω[x↾n] = #([0, n) \ S)` whenever `x` agrees with `ω` on `S`.
Blueprint node `meas:examples`. -/
theorem infoBits_gapKernel_cylinder (S : Set ℕ) {ω x : ℕ → Bool} (hx : ∀ i ∈ S, x i = ω i)
    (n : ℕ) : infoBits (gapKernel S ω (PiNat.cylinder x n)) = gapCount S n := by
  rw [gapKernel_cylinder S hx, infoBits_two_inv_pow]

/-- `μ_ω`-almost every `x` agrees with `ω` on `S`. -/
theorem ae_gapKernel (S : Set ℕ) (ω : ℕ → Bool) : ∀ᵐ x ∂gapKernel S ω, ∀ i ∈ S, x i = ω i := by
  have hm : MeasurableSet {x : ℕ → Bool | ∀ i ∈ S, x i = ω i} := by
    have h : {x : ℕ → Bool | ∀ i ∈ S, x i = ω i} = ⋂ i ∈ S, (fun x : ℕ → Bool ↦ x i) ⁻¹' {ω i} := by
      ext x
      simp
    rw [h]
    exact MeasurableSet.biInter S.to_countable fun i _ ↦
      (measurable_pi_apply i) (measurableSet_singleton _)
  rw [gapKernel_apply, ae_map_iff (measurable_revealSeq_left S ω).aemeasurable hm]
  exact .of_forall fun z i hi ↦ by simp [revealSeq, hi]

/-- Example 7.4(2): for `μ_ω`-almost every `x`, `Φ_{μ_ω}(x)` is the pair of the lower and upper
densities of `ℕ \ S`. Blueprint node `meas:examples`. -/
theorem localEntropy_gapKernel (S : Set ℕ) (ω : ℕ → Bool) :
    ∀ᵐ x ∂gapKernel S ω, localEntropy (gapKernel S ω) shiftMap x =
      (liminf (fun n : ℕ ↦ (gapCount S n : ℝ≥0∞) / n) atTop,
        limsup (fun n : ℕ ↦ (gapCount S n : ℝ≥0∞) / n) atTop) := by
  filter_upwards [ae_gapKernel S ω] with x hx
  simp only [localEntropy_shiftMap (by norm_num) (by norm_num) cantor_hd,
    infoBits_gapKernel_cylinder S hx]

/-- Copying a fair sequence on `S` and another, independent, fair sequence off `S` gives a fair
sequence. -/
theorem map_prod_revealSeq (S : Set ℕ) :
    (uniformMeasure.prod uniformMeasure).map (fun p ↦ revealSeq S p.1 p.2) = uniformMeasure := by
  classical
  have hg := measurable_revealSeq S
  obtain ⟨c, hc, hU⟩ := uniformMeasure_eq_infinitePi
  rw [hU]
  refine Measure.eq_infinitePi _ fun F t ht ↦ ?_
  have hpre : (fun p : (ℕ → Bool) × (ℕ → Bool) ↦ revealSeq S p.1 p.2) ⁻¹' Set.pi F t =
      Set.pi (F.filter (· ∈ S)) t ×ˢ Set.pi (F.filter (· ∉ S)) t := by
    ext ⟨y, z⟩
    simp only [mem_preimage, Set.mem_pi, Finset.coe_filter, mem_ofPred_eq, mem_prod, revealSeq]
    constructor
    · intro h
      exact ⟨fun i ⟨hi, hS⟩ ↦ by simpa [hS] using h i hi,
        fun i ⟨hi, hS⟩ ↦ by simpa [hS] using h i hi⟩
    · rintro ⟨h1, h2⟩ i hi
      by_cases hS : i ∈ S
      · simpa [hS] using h1 i ⟨hi, hS⟩
      · simpa [hS] using h2 i ⟨hi, hS⟩
  rw [Measure.map_apply hg (MeasurableSet.pi F.countable_toSet fun i _ ↦ ht i), hpre,
    Measure.prod_prod, Measure.infinitePi_pi _ (fun i _ ↦ ht i),
    Measure.infinitePi_pi _ (fun i _ ↦ ht i), Finset.prod_filter_mul_prod_filter_not]

/-- `∫ U(revealSeq S y ⁻¹' s) dU(y) = U(s)` for a measurable `s`. -/
private lemma lintegral_uniformMeasure_revealSeq (S : Set ℕ) {s : Set (ℕ → Bool)}
    (hs : MeasurableSet s) :
    ∫⁻ y, uniformMeasure (revealSeq S y ⁻¹' s) ∂uniformMeasure = uniformMeasure s := by
  have hg := measurable_revealSeq S
  conv_rhs => rw [← map_prod_revealSeq S]
  rw [Measure.map_apply hg hs, Measure.prod_apply (hg hs)]
  rfl

/-- Example 7.4(2): the components integrate to the fair-coin measure, `∫ μ_ω dP(ω) = μ`.
Blueprint node `meas:examples`. -/
theorem bind_gapKernel (S : Set ℕ) : uniformMeasure.bind (gapKernel S) = uniformMeasure := by
  ext s hs
  rw [Measure.bind_apply hs (Kernel.aemeasurable _), ← lintegral_uniformMeasure_revealSeq S hs]
  refine lintegral_congr fun ω ↦ ?_
  rw [gapKernel_apply, Measure.map_apply (measurable_revealSeq_left S ω) hs]

/-- Example 7.4(2), consequence: for this decomposition of the fair-coin measure (whose entropy
law is `δ_{(1, 1)}`), integral affinity holds if and only if `ℕ \ S` has lower and upper
density `1`. In particular it fails as soon as `S` has positive upper density.
Blueprint node `meas:examples`. -/
theorem integralAffinity_gapKernel_iff (S : Set ℕ) :
    Measure.map (fun p : (ℕ → Bool) × (ℕ → Bool) ↦ localEntropy (gapKernel S p.1) shiftMap p.2)
        (uniformMeasure ⊗ₘ gapKernel S) = entropyLaw (uniformMeasure.bind (gapKernel S)) shiftMap ↔
      (liminf (fun n : ℕ ↦ (gapCount S n : ℝ≥0∞) / n) atTop,
        limsup (fun n : ℕ ↦ (gapCount S n : ℝ≥0∞) / n) atTop) = (1, 1) := by
  have hT := continuous_shiftMap (by norm_num) (by norm_num) cantor_hd
  set d := (liminf (fun n : ℕ ↦ (gapCount S n : ℝ≥0∞) / n) atTop,
    limsup (fun n : ℕ ↦ (gapCount S n : ℝ≥0∞) / n) atTop)
  have hK : ∀ᵐ p ∂(uniformMeasure ⊗ₘ gapKernel S),
      localEntropy (gapKernel S p.1) shiftMap p.2 = d :=
    Measure.ae_compProd_of_ae_ae ((measurable_localEntropy_kernel hT _)
      (measurableSet_singleton d)) (.of_forall fun ω ↦ localEntropy_gapKernel S ω)
  rw [kernelEntropyLaw_eq_iff hT, bind_gapKernel]
  simp only [localEntropy_uniformMeasure_shiftMap]
  constructor
  · intro h
    have h' : ∀ᵐ _ ∂(uniformMeasure ⊗ₘ gapKernel S), d = ((1, 1) : ℝ≥0∞ × ℝ≥0∞) := by
      filter_upwards [h, hK] with p hp hp'
      rw [← hp', hp]
    exact (Filter.eventually_const).1 h'
  · intro h
    filter_upwards [hK] with p hp
    rw [hp, h]

end gap

/-! ### Example 7.8: zero mutual information rate is not enough -/

section revealedBlocks

attribute [local instance] cantorMetricSpace

/-- The label measure of Example 7.8: `(e_k)_k` independent Bernoulli(`1/k`) variables and an
independent fair sequence `y`. -/
noncomputable def revealLabelMeasure : Measure ((ℕ → Bool) × (ℕ → Bool)) :=
  (Measure.infinitePi fun k ↦
    ProbabilityTheory.bernoulliMeasure true false (revealProb k)).prod uniformMeasure

/-- The label measure is the product of the law of `(e_k)_k` and the fair-coin measure. -/
theorem revealLabelMeasure_eq : revealLabelMeasure = revealIndicatorMeasure.prod uniformMeasure :=
  rfl

instance : IsProbabilityMeasure revealLabelMeasure := by
  unfold revealLabelMeasure; infer_instance

/-- The map `((e, y), z) ↦ revealSeq (revealedSet e) y z` is measurable. -/
theorem measurable_revealBlocks :
    Measurable fun p : ((ℕ → Bool) × (ℕ → Bool)) × (ℕ → Bool) ↦
      revealSeq (revealedSet p.1.1) p.1.2 p.2 := by
  classical
  refine Measurable.of_eval fun i ↦ ?_
  have h : (fun p : ((ℕ → Bool) × (ℕ → Bool)) × (ℕ → Bool) ↦
      revealSeq (revealedSet p.1.1) p.1.2 p.2 i) =
      fun p ↦ if p.1.1 ∈ {e : ℕ → Bool | i ∈ revealedSet e} then p.1.2 i else p.2 i := by
    funext p
    simp only [revealSeq, mem_ofPred_eq]
  rw [h]
  exact Measurable.ite ((measurableSet_mem_revealedSet i).preimage
    (measurable_fst.comp measurable_fst))
    ((measurable_pi_apply i).comp (measurable_snd.comp measurable_fst))
    ((measurable_pi_apply i).comp measurable_snd)

/-- The kernel of Example 7.8: given the label `(e, y)`, `μ_{(e, y)}` fixes the revealed blocks
`J_k` (`e_k = 1`, `k ≥ 2`) to the values of `y` and is fair elsewhere.

The paper's label is `((e_k)_k, (x↾J_k)_{k : e_k = 1})`; here it is `(e, y)` with `y` fair,
of which `μ_{(e, y)}` only uses `e` and the revealed blocks of `y`, and the point is
`x = revealSeq (revealedSet e) y z` with `z` fair, so that the joint law of `(e, x↾J_k)` and `x`
is the paper's. Blueprint node `meas:examples`. -/
noncomputable def revealKernel : Kernel ((ℕ → Bool) × (ℕ → Bool)) (ℕ → Bool) :=
  Kernel.map (Kernel.prod (Kernel.deterministic id measurable_id)
    (Kernel.const ((ℕ → Bool) × (ℕ → Bool)) uniformMeasure))
    fun p ↦ revealSeq (revealedSet p.1.1) p.1.2 p.2

/-- `μ_{(e, y)}` is the law of `revealSeq (revealedSet e) y z` for a fair `z`. -/
theorem revealKernel_apply (ω : (ℕ → Bool) × (ℕ → Bool)) :
    revealKernel ω = uniformMeasure.map (revealSeq (revealedSet ω.1) ω.2) := by
  rw [revealKernel, Kernel.map_apply _ measurable_revealBlocks, Kernel.prod_apply,
    Kernel.deterministic_apply, Kernel.const_apply, Measure.dirac_prod,
    Measure.map_map measurable_revealBlocks measurable_prodMk_left]
  rfl

instance : IsMarkovKernel revealKernel :=
  ⟨fun ω ↦ by rw [revealKernel_apply]; infer_instance⟩

/-- Example 7.8: `μ = ∫ μ_ω dP(ω)` is the fair-coin measure. Blueprint node `meas:examples`. -/
theorem bind_revealKernel : revealLabelMeasure.bind revealKernel = uniformMeasure := by
  ext s hs
  have hm : Measurable fun ω ↦ revealKernel ω s := Kernel.measurable_coe _ hs
  rw [Measure.bind_apply hs (Kernel.aemeasurable _), revealLabelMeasure,
    lintegral_prod _ hm.aemeasurable]
  have h : ∀ e : ℕ → Bool,
      ∫⁻ y, revealKernel (e, y) s ∂uniformMeasure = uniformMeasure s := fun e ↦ by
    rw [← lintegral_uniformMeasure_revealSeq (revealedSet e) hs]
    refine lintegral_congr fun y ↦ ?_
    rw [revealKernel_apply, Measure.map_apply (measurable_revealSeq_left _ y) hs]
  simp only [h, lintegral_const, measure_univ, mul_one]

/-- `μ_{(e, y)}` is the measure of Example 7.4(2) for the revealed set `S = revealedSet e`. -/
theorem revealKernel_eq_gapKernel (ω : (ℕ → Bool) × (ℕ → Bool)) :
    revealKernel ω = gapKernel (revealedSet ω.1) ω.2 := by
  rw [revealKernel_apply, gapKernel_apply]

/-- A property of the revealing indicators `e` that holds almost surely holds for almost every
label `(e, y)`. -/
private lemma ae_label_of_ae {P : (ℕ → Bool) → Prop}
    (h : ∀ᵐ e ∂revealIndicatorMeasure, P e) : ∀ᵐ ω ∂revealLabelMeasure, P ω.1 := by
  have hmap : revealLabelMeasure.map Prod.fst = revealIndicatorMeasure := by
    rw [revealLabelMeasure_eq, Measure.map_fst_prod, measure_univ, one_smul]
  rw [← hmap] at h
  exact ae_of_ae_map measurable_fst.aemeasurable h

/-- A property of the label that holds almost surely holds `M`-almost everywhere. -/
private lemma ae_compProd_of_ae_label {P : (ℕ → Bool) × (ℕ → Bool) → Prop}
    (h : ∀ᵐ ω ∂revealLabelMeasure, P ω) :
    ∀ᵐ p ∂(revealLabelMeasure ⊗ₘ revealKernel), P p.1 := by
  rw [← Measure.fst_compProd revealLabelMeasure revealKernel, Measure.fst] at h
  exact ae_of_ae_map measurable_fst.aemeasurable h

/-- `M`-almost every point agrees with the label on the revealed blocks. -/
private lemma ae_agree_revealKernel :
    ∀ᵐ p ∂(revealLabelMeasure ⊗ₘ revealKernel), ∀ i ∈ revealedSet p.1.1, p.2 i = p.1.2 i := by
  have hm : MeasurableSet {p : ((ℕ → Bool) × (ℕ → Bool)) × (ℕ → Bool) |
      ∀ i ∈ revealedSet p.1.1, p.2 i = p.1.2 i} := by
    have h : {p : ((ℕ → Bool) × (ℕ → Bool)) × (ℕ → Bool) |
        ∀ i ∈ revealedSet p.1.1, p.2 i = p.1.2 i} =
        ⋂ i, ({p | i ∈ revealedSet p.1.1}ᶜ ∪
          ⋃ b : Bool, {p | p.2 i = b} ∩ {p | p.1.2 i = b}) := by
      ext p
      simp only [mem_ofPred_eq, mem_iInter, mem_union, mem_compl_iff, mem_iUnion, mem_inter_iff]
      refine forall_congr' fun i ↦ ⟨fun h ↦ ?_, fun h hi ↦ ?_⟩
      · by_cases hi : i ∈ revealedSet p.1.1
        · exact Or.inr ⟨_, h hi, rfl⟩
        · exact Or.inl hi
      · rcases h with h | ⟨b, h1, h2⟩
        · exact absurd hi h
        · rw [h1, h2]
    rw [h]
    refine MeasurableSet.iInter fun i ↦ MeasurableSet.union ?_ (MeasurableSet.iUnion fun b ↦ ?_)
    · exact ((measurableSet_mem_revealedSet i).preimage
        (measurable_fst.comp measurable_fst)).compl
    · exact (((measurable_pi_apply i).comp measurable_snd) (measurableSet_singleton b)).inter
        ((show Measurable fun p : ((ℕ → Bool) × (ℕ → Bool)) × (ℕ → Bool) ↦ p.1.2 i from
          (measurable_pi_apply i).comp (measurable_snd.comp measurable_fst))
          (measurableSet_singleton b))
  refine Measure.ae_compProd_of_ae_ae hm (.of_forall fun ω ↦ ?_)
  rw [revealKernel_eq_gapKernel]
  exact ae_gapKernel _ _

/-- At a point that agrees with its label on the revealed blocks, the information density is
the number of revealed coordinates: `i_n = #([0, n) ∩ S)`. -/
private lemma infoDensity_revealKernel_eq {p : ((ℕ → Bool) × (ℕ → Bool)) × (ℕ → Bool)}
    (hp : ∀ i ∈ revealedSet p.1.1, p.2 i = p.1.2 i) (n : ℕ) :
    infoDensity (revealLabelMeasure.bind revealKernel) revealKernel n p =
      revealCount p.1.1 n := by
  rw [infoDensity, bind_revealKernel, uniformMeasure_cylinder, revealKernel_eq_gapKernel,
    gapKernel_cylinder _ hp]
  have hR : (gapCount (revealedSet p.1.1) n : ℝ) + revealCount p.1.1 n = n := by
    exact_mod_cast ncard_diff_revealedSet_add p.1.1 n
  simp only [ENNReal.toReal_pow, ENNReal.toReal_inv, ENNReal.toReal_ofNat]
  rw [Real.logb_div (by positivity) (by positivity), Real.logb_pow, Real.logb_pow,
    Real.logb_inv, Real.logb_self_eq_one one_lt_two]
  linarith

/-- Example 7.8: `Φ_{μ_ω}(x) = (1/2, 1)` for `M`-almost every `(ω, x)`.

The paper's argument: almost surely `e_k = 1` for infinitely many `k` (second Borel–Cantelli
lemma, `∑ 1/k = ∞`), and at `n = 2^{k+1}` at least half of the coordinates below `n` are
revealed. For the upper bound `1/2 + o(1)` on the revealed proportion the paper's
`e_{k-1} e_k = 0` for all large `k` only gives `3/4`; the proof uses, for every `m`, that
almost surely `e_j e_k = 0` for all large `k` and `k - m ≤ j < k` (first Borel–Cantelli lemma,
`∑_k m²/k² < ∞`; `ae_eventually_sparse`). Blueprint node `meas:examples`. -/
theorem ae_localEntropy_revealKernel :
    ∀ᵐ p ∂(revealLabelMeasure ⊗ₘ revealKernel),
      localEntropy (revealKernel p.1) shiftMap p.2 = (2⁻¹, 1) := by
  have hT := continuous_shiftMap (by norm_num) (by norm_num) cantor_hd
  refine Measure.ae_compProd_of_ae_ae
    ((measurable_localEntropy_kernel hT _) (measurableSet_singleton _)) ?_
  filter_upwards [ae_label_of_ae (ae_frequently_reveal.and (ae_all_iff.2 ae_eventually_sparse))]
    with ω hω
  rw [revealKernel_eq_gapKernel]
  filter_upwards [localEntropy_gapKernel (revealedSet ω.1) ω.2] with x hx
  rw [hx]
  exact density_compl_revealedSet hω.1 hω.2

/-- Example 7.8: the mutual information `I(ω; x↾n) = ∫ i_n dM` is `O(n / log n)`: here `i_n` is
the number of revealed coordinates below `n` (`M`-almost everywhere), of mean at most
`∑_{k ≤ log₂ n} 2^k / k ≤ 12 n / log₂ n`. Blueprint node `meas:examples`. -/
theorem integral_infoDensity_revealKernel_le :
    ∃ C : ℝ, ∀ n : ℕ, 2 ≤ n →
      ∫ p, infoDensity (revealLabelMeasure.bind revealKernel) revealKernel n p
          ∂(revealLabelMeasure ⊗ₘ revealKernel) ≤ C * n / Real.logb 2 n := by
  refine ⟨12, fun n hn ↦ ?_⟩
  have hcongr : (fun p ↦ infoDensity (revealLabelMeasure.bind revealKernel) revealKernel n p)
      =ᵐ[revealLabelMeasure ⊗ₘ revealKernel] fun p ↦ (revealCount p.1.1 n : ℝ) := by
    filter_upwards [ae_agree_revealKernel] with p hp
    exact infoDensity_revealKernel_eq hp n
  have hmap : (revealLabelMeasure ⊗ₘ revealKernel).map (fun p ↦ p.1.1) =
      revealIndicatorMeasure := by
    rw [show (fun p : ((ℕ → Bool) × (ℕ → Bool)) × (ℕ → Bool) ↦ p.1.1) =
      Prod.fst ∘ Prod.fst from rfl, ← Measure.map_map measurable_fst measurable_fst]
    change (Measure.fst (revealLabelMeasure ⊗ₘ revealKernel)).map Prod.fst = _
    rw [Measure.fst_compProd, revealLabelMeasure_eq, Measure.map_fst_prod, measure_univ,
      one_smul]
  have hint := integral_map (μ := revealLabelMeasure ⊗ₘ revealKernel)
    (φ := fun p ↦ p.1.1) (f := fun e ↦ (revealCount e n : ℝ))
    (measurable_fst.comp measurable_fst).aemeasurable
    (measurable_revealCount n).aestronglyMeasurable
  rw [hmap] at hint
  rw [integral_congr_ae hcongr, ← hint]
  exact integral_revealCount_le hn

/-- Example 7.8: `i_n ≥ n / 2` for infinitely many `n`, `M`-almost everywhere, so `i_n / n`
does not tend to `0` pointwise although its mean does. Blueprint node `meas:examples`. -/
theorem ae_frequently_half_le_infoDensity_revealKernel :
    ∀ᵐ p ∂(revealLabelMeasure ⊗ₘ revealKernel), ∃ᶠ n : ℕ in atTop,
      (n : ℝ) / 2 ≤ infoDensity (revealLabelMeasure.bind revealKernel) revealKernel n p := by
  filter_upwards [ae_agree_revealKernel,
    ae_compProd_of_ae_label (ae_label_of_ae ae_frequently_reveal)] with p hp hfr
  refine (frequently_le_two_mul_revealCount hfr).mono fun n hn ↦ ?_
  rw [infoDensity_revealKernel_eq hp]
  have : (n : ℝ) ≤ 2 * revealCount p.1.1 n := by exact_mod_cast hn
  linarith

/-- Example 7.8: integral affinity fails, in the lower coordinate: `Φ_{μ_ω} = (1/2, 1)`
`M`-almost everywhere while `Φ_μ = (1, 1)`. Proved from `bind_revealKernel` and
`ae_localEntropy_revealKernel`. Blueprint node `meas:examples`. -/
theorem map_localEntropy_revealKernel_ne_entropyLaw :
    Measure.map (fun p : ((ℕ → Bool) × (ℕ → Bool)) × (ℕ → Bool) ↦
        localEntropy (revealKernel p.1) shiftMap p.2) (revealLabelMeasure ⊗ₘ revealKernel) ≠
      entropyLaw (revealLabelMeasure.bind revealKernel) shiftMap := by
  have hT := continuous_shiftMap (by norm_num) (by norm_num) cantor_hd
  rw [Ne, kernelEntropyLaw_eq_iff hT, bind_revealKernel]
  intro h
  have h' : ∀ᵐ _ ∂(revealLabelMeasure ⊗ₘ revealKernel),
      ((2⁻¹, 1) : ℝ≥0∞ × ℝ≥0∞) = (1, 1) := by
    filter_upwards [h, ae_localEntropy_revealKernel] with p hp hp'
    rw [← hp', hp, localEntropy_uniformMeasure_shiftMap]
  have := congrArg Prod.fst ((Filter.eventually_const).1 h')
  norm_num at this

end revealedBlocks

/-! ### Remark 7.7: smooth families -/

section smooth

attribute [local instance] cantorMetricSpace

/-- `log₂ n / n → 0`. -/
private lemma tendsto_logb_div_natCast :
    Tendsto (fun n : ℕ ↦ Real.logb 2 n / n) atTop (𝓝 0) := by
  have := (Real.tendsto_pow_logb_div_mul_add_atTop (b := 2) 1 0 1
    (by norm_num)).comp tendsto_natCast_atTop_atTop
  refine this.congr fun n ↦ ?_
  simp

/-- Remark 7.7, the key bound: let `μ_θ = ⨂_i Bernoulli(β_i(θ))` with `β_i : [0, 1] → [δ, 1 - δ]`
uniformly Lipschitz. For every probability measure `P` on `[0, 1]` and `M`-almost every
`(θ, x)`, `i_n ≤ 3 log₂ n + O(1)`.

The kernel is given abstractly, with its values prescribed by `hκ` (its existence, i.e. the
measurability of `θ ↦ μ_θ`, is not addressed here). Blueprint node `meas:examples`. -/
theorem ae_infoDensity_le_smoothFamily (β : ℕ → unitInterval → unitInterval) {δ : ℝ}
    (hδ : 0 < δ) (hβ : ∀ i θ, δ ≤ (β i θ : ℝ) ∧ (β i θ : ℝ) ≤ 1 - δ) {L : NNReal}
    (hL : ∀ i, LipschitzWith L (β i)) (κ : Kernel unitInterval (ℕ → Bool)) [IsMarkovKernel κ]
    (hκ : ∀ θ, κ θ =
      Measure.infinitePi fun i ↦ ProbabilityTheory.bernoulliMeasure true false (β i θ))
    (P : Measure unitInterval) [IsProbabilityMeasure P] :
    ∀ᵐ p ∂(P ⊗ₘ κ), ∃ C : ℝ, ∀ᶠ n : ℕ in atTop,
      infoDensity (P.bind κ) κ n p ≤ 3 * Real.logb 2 n + C := by
  filter_upwards [ae_logb_ratio_le_smoothFamily β hδ hβ hL κ hκ P] with p hp
  exact ⟨1, hp⟩

/-- Remark 7.7: for a smooth family `μ_θ = ⨂_i Bernoulli(β_i(θ))` (`β_i` with values in
`[δ, 1 - δ]`, uniformly Lipschitz), integral affinity holds for every probability measure `P`
on `[0, 1]`, although the `μ_θ` are in general mutually singular and not invariant. Proved
from `ae_infoDensity_le_smoothFamily`, Proposition 7.6(i) and 7.6(ii).
Blueprint node `meas:examples`. -/
theorem integralAffinity_smoothFamily (β : ℕ → unitInterval → unitInterval) {δ : ℝ}
    (hδ : 0 < δ) (hβ : ∀ i θ, δ ≤ (β i θ : ℝ) ∧ (β i θ : ℝ) ≤ 1 - δ) {L : NNReal}
    (hL : ∀ i, LipschitzWith L (β i)) (κ : Kernel unitInterval (ℕ → Bool)) [IsMarkovKernel κ]
    (hκ : ∀ θ, κ θ =
      Measure.infinitePi fun i ↦ ProbabilityTheory.bernoulliMeasure true false (β i θ))
    (P : Measure unitInterval) [IsProbabilityMeasure P] :
    Measure.map (fun p : unitInterval × (ℕ → Bool) ↦ localEntropy (κ p.1) shiftMap p.2)
      (P ⊗ₘ κ) = entropyLaw (P.bind κ) shiftMap := by
  refine integralAffinity_of_tendsto_infoDensity (by norm_num) (by norm_num) cantor_hd P κ ?_
  filter_upwards [ae_infoDensity_le_smoothFamily β hδ hβ hL κ hκ P,
    ae_eventually_neg_two_logb_le_infoDensity (by norm_num) (by norm_num) cantor_hd P κ]
    with p ⟨C, hC⟩ hlow
  have hl : Tendsto (fun n : ℕ ↦ -(2 * Real.logb 2 n) / n) atTop (𝓝 0) := by
    simpa [neg_div, mul_div_assoc] using (tendsto_logb_div_natCast.const_mul 2).neg
  have hu : Tendsto (fun n : ℕ ↦ (3 * Real.logb 2 n + C) / n) atTop (𝓝 0) := by
    have h1 := tendsto_logb_div_natCast.const_mul 3
    have h2 := tendsto_const_nhds (x := C).div_atTop tendsto_natCast_atTop_atTop
    simpa [add_div, mul_div_assoc] using h1.add h2
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hl hu ?_ ?_
  · filter_upwards [hlow, eventually_ge_atTop 1] with n hn h1
    exact div_le_div_of_nonneg_right hn (Nat.cast_nonneg n)
  · filter_upwards [hC, eventually_ge_atTop 1] with n hn h1
    exact div_le_div_of_nonneg_right hn (Nat.cast_nonneg n)

end smooth

end Kolmogorov.PointToSet
