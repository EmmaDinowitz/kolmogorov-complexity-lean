/-
Copyright (c) 2026 Emma Dinowitz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emma Dinowitz
-/
import KolmogorovMathlib.PointToSet.Measure.Shift
import KolmogorovMathlib.PointToSet.Measure.InformationRate
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.PSeries
import Mathlib.MeasureTheory.Integral.Indicator
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.Probability.ProductMeasure

/-!
# Compactness is needed in Proposition 4.7 (Example 5.4)

Baire space `ℕ → ℕ` with the shift `σ` and the first-difference metric
`dist x y = (1/2) ^ firstDiff x y` (`baireMetricSpace`, a local instance) is complete and
separable but not compact, and its Bowen balls are cylinders. For `i ≥ 0` let
`p_i = (i + 2)^{-2}` (`baireProb`), `L_i = (i + 2)^2` (`baireLength`) and let `ν_i`
(`baireFactor`) be the probability measure on `ℕ` with mass `1 - p_i` at `0` and mass
`p_i 2^{-L_i}` at each of `1, …, 2^{L_i}`; `μ = ⨂_i ν_i` (`baireMeasure`, built with
`Measure.infinitePi`). Then (E. Dinowitz, *Entropy of non-invariant measures and orbit
complexity of random points*, Example 5.4):

* `ae_localEntropy_baireMeasure`, `entropyLaw_baireMeasure`, `measureEntropy_baireMeasure`:
  since `∑ p_i < ∞`, by Borel–Cantelli almost every point has finitely many nonzero coordinates,
  `-log₂ μ[x↾n]` is bounded in `n`, so `Φ_μ = (0, 0)` a.e., `Λ_μ = δ_{(0, 0)}` and
  `h̲_μ(σ) = h̄_μ(σ) = 0`;
* `lintegral_infoBits_cylinder_baireMeasureOf`, `lintegral_infoBits_baireFactor`,
  `summable_binEntropy_baireProb`, `informationRate_baireMeasure`: the mean information of the
  `n`-cylinders is `∑_{i<n} H(ν_i)` with `H(ν_i) = H(p_i) + 1` and `∑ H(p_i) < ∞`, so
  `H̲_μ(σ) = H̄_μ(σ) = 1`;
* `measureEntropy_snd_lt_informationRate_snd_baireMeasure`,
  `exists_measure_measureEntropy_lt_informationRate`: `H̄_μ(σ) = 1 > 0 = h̄_μ(σ)`, so the
  inequality `H̄_μ(T) ≤ h̄_μ(T)` of Proposition 4.7 fails without compactness;
* remarks of the example: `informationRate_baireMeasureOf_cube` (with `L_i = (i + 2)^3` the
  information rates are infinite, while `measureEntropy_baireMeasureOf` still gives `(0, 0)`),
  `isCompact_baireSupport`, `baireMeasureOf_compl_baireSupport` (`μ` is carried by the compact
  set `∏_i {0, …, 2^{L_i}}`), `map_shiftMap_baireMeasureOf_ne` (`μ` is not shift-invariant);
* after Proposition 6.10: `tendsto_measure_lt_localEntropyRate_baireMeasureOf`,
  `tendsto_measure_localEntropyRate_lt_baireMeasureOf` (the rates in probability are `0`).

The construction is carried out for an arbitrary length sequence `L` (`baireFactorOf`,
`baireMeasureOf`) wherever the argument does not use `L_i = (i + 2)^2`.

Blueprint node `meas:examples`.
-/

namespace Kolmogorov.PointToSet

open Filter Set MeasureTheory
open scoped Topology ENNReal

/-! ### Products of probability measures on `ℕ` -/

/-- The information of a product of masses at most `1` is the sum of their informations. -/
theorem infoBits_mul_of_le_one {a b : ℝ≥0∞} (ha : a ≤ 1) (hb : b ≤ 1) :
    infoBits (a * b) = infoBits a + infoBits b := by
  rcases eq_or_ne a 0 with rfl | ha0
  · simp
  rcases eq_or_ne b 0 with rfl | hb0
  · simp
  have hat : a ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top ha
  have hbt : b ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hb
  have ha' : 0 < a.toReal := ENNReal.toReal_pos ha0 hat
  have hb' : 0 < b.toReal := ENNReal.toReal_pos hb0 hbt
  have ha1 : a.toReal ≤ 1 := ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using ha)
  have hb1 : b.toReal ≤ 1 := ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using hb)
  rw [infoBits_of_ne (mul_ne_zero ha0 hb0), infoBits_of_ne ha0, infoBits_of_ne hb0,
    ENNReal.toReal_mul, Real.logb_mul ha'.ne' hb'.ne', neg_add,
    ENNReal.ofReal_add (neg_nonneg.2 (Real.logb_nonpos one_lt_two ha'.le ha1))
      (neg_nonneg.2 (Real.logb_nonpos one_lt_two hb'.le hb1))]

/-- The information of a finite product of masses at most `1` is the sum of the informations. -/
theorem infoBits_prod_of_le_one {ι : Type*} (s : Finset ι) {a : ι → ℝ≥0∞}
    (ha : ∀ i ∈ s, a i ≤ 1) : infoBits (∏ i ∈ s, a i) = ∑ i ∈ s, infoBits (a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [infoBits_of_ne one_ne_zero]
  | insert j s hj ih =>
    rw [Finset.prod_insert hj, Finset.sum_insert hj,
      infoBits_mul_of_le_one (ha j (Finset.mem_insert_self j s))
        (Finset.prod_le_one fun i hi ↦ ha i (Finset.mem_insert_of_mem hi)),
      ih fun i hi ↦ ha i (Finset.mem_insert_of_mem hi)]

section infinitePi

variable (ν : ℕ → Measure ℕ) [∀ i, IsProbabilityMeasure (ν i)]

/-- The product measure of a cylinder `[x↾n]` is `∏_{i<n} ν_i {x_i}`. -/
theorem infinitePi_cylinder_nat (x : ℕ → ℕ) (n : ℕ) :
    Measure.infinitePi ν (PiNat.cylinder x n) = ∏ i ∈ Finset.range n, ν i {x i} := by
  rw [PiNat.cylinder_eq_pi]
  exact Measure.infinitePi_pi (μ := ν) fun _ _ ↦ MeasurableSet.of_discrete

/-- The product measure of a coordinate preimage `{x | x_i ∈ S}` is `ν_i S`. -/
theorem infinitePi_preimage_eval_nat (i : ℕ) (S : Set ℕ) :
    Measure.infinitePi ν ((fun x : ℕ → ℕ ↦ x i) ⁻¹' S) = ν i S := by
  rw [← Measure.map_apply (measurable_pi_apply i) MeasurableSet.of_discrete,
    Measure.infinitePi_map_eval]

/-- Under a product measure `-log₂ μ[x↾n] = ∑_{i<n} -log₂ ν_i {x_i}`. -/
theorem infoBits_infinitePi_cylinder_nat (x : ℕ → ℕ) (n : ℕ) :
    infoBits (Measure.infinitePi ν (PiNat.cylinder x n)) =
      ∑ i ∈ Finset.range n, infoBits (ν i {x i}) := by
  rw [infinitePi_cylinder_nat, infoBits_prod_of_le_one _ fun i _ ↦ prob_le_one]

/-- Under a product measure the mean information of the `n`-cylinders is the sum of the Shannon
entropies (in bits) of the first `n` factors. -/
theorem lintegral_infoBits_infinitePi_cylinder_nat (n : ℕ) :
    ∫⁻ x, infoBits (Measure.infinitePi ν (PiNat.cylinder x n)) ∂Measure.infinitePi ν =
      ∑ i ∈ Finset.range n, ∫⁻ k, infoBits (ν i {k}) ∂ν i := by
  simp_rw [infoBits_infinitePi_cylinder_nat]
  rw [lintegral_finsetSum _ fun i _ ↦ show Measurable fun x : ℕ → ℕ ↦ infoBits (ν i {x i}) from
    (Measurable.of_discrete (f := fun k : ℕ ↦ infoBits (ν i {k}))).comp
      (measurable_pi_apply i)]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [← Measure.infinitePi_map_eval ν i, lintegral_map Measurable.of_discrete
    (measurable_pi_apply i), Measure.infinitePi_map_eval]

/-- Almost every point of a product measure has all its coordinates in the atoms of the
factors. -/
theorem ae_infinitePi_apply_ne_zero :
    ∀ᵐ x ∂Measure.infinitePi ν, ∀ i, ν i {x i} ≠ 0 := by
  rw [ae_all_iff]
  intro i
  have h : ν i {k | ν i {k} = 0} = 0 := by
    have : {k | ν i {k} = 0} = ⋃ k ∈ {k | ν i {k} = 0}, ({k} : Set ℕ) := by
      ext k; simp
    rw [this, measure_biUnion_null_iff (Set.to_countable _)]
    exact fun k hk ↦ hk
  rw [ae_iff]
  simp only [ne_eq, not_not]
  exact (infinitePi_preimage_eval_nat ν i {k | ν i {k} = 0}).trans h

end infinitePi

/-! ### Baire space -/

/-- The Baire metric `dist x y = (1/2) ^ firstDiff x y` on `ℕ → ℕ`. Its uniformity, hence its
topology, is definitionally the product one, so the product σ-algebra is its Borel σ-algebra.
Not a global instance: use `attribute [local instance] baireMetricSpace`.
Blueprint node `meas:examples`. -/
@[reducible] noncomputable def baireMetricSpace : MetricSpace (ℕ → ℕ) :=
  PiNat.metricSpaceOfDiscreteUniformity fun _ ↦ rfl

attribute [local instance] baireMetricSpace

/-- The Baire metric is the first-difference metric with ratio `1/2`. -/
theorem baireMetricSpace_dist_eq {x y : ℕ → ℕ} (h : x ≠ y) :
    dist x y = (1 / 2 : ℝ) ^ PiNat.firstDiff x y :=
  PiNat.dist_eq_of_ne h

/-- The product σ-algebra of Baire space is the Borel σ-algebra of the Baire metric. -/
theorem borelSpace_baireMetricSpace : BorelSpace (ℕ → ℕ) := inferInstance

/-- Baire space is separable. -/
theorem secondCountableTopology_baireMetricSpace : SecondCountableTopology (ℕ → ℕ) :=
  inferInstance

/-- Baire space is complete. -/
theorem completeSpace_baireMetricSpace : CompleteSpace (ℕ → ℕ) := inferInstance

/-- Baire space is not compact. -/
theorem not_compactSpace_baireMetricSpace : ¬ CompactSpace (ℕ → ℕ) := by
  intro h
  have hc : IsCompact (univ : Set ℕ) := by
    have := isCompact_univ.image (continuous_apply 0 : Continuous fun x : ℕ → ℕ ↦ x 0)
    convert this
    ext k
    simp
  exact noncompact_univ ℕ hc

/-- The shift is continuous for the Baire metric. -/
theorem continuous_shiftMap_baire : Continuous (shiftMap : (ℕ → ℕ) → ℕ → ℕ) :=
  continuous_shiftMap (by norm_num) (by norm_num) fun _ _ ↦ baireMetricSpace_dist_eq

/-! ### The measure of Example 5.4 -/

/-- The probability `p_i = (i + 2)^{-2}` that the `i`-th coordinate is nonzero (Example 5.4).
Blueprint node `meas:examples`. -/
noncomputable def baireProb (i : ℕ) : ℝ := (((i : ℝ) + 2) ^ 2)⁻¹

/-- The length `L_i = (i + 2)^2` of Example 5.4: a nonzero `i`-th coordinate is uniform on
`{1, …, 2^{L_i}}`. Blueprint node `meas:examples`. -/
def baireLength (i : ℕ) : ℕ := (i + 2) ^ 2

/-- The weights of `ν_i` for a length sequence `L`: `1 - p_i` at `0`, `p_i 2^{-L_i}` at each of
`1, …, 2^{L_i}`, and `0` elsewhere. Blueprint node `meas:examples`. -/
noncomputable def baireWeight (L : ℕ → ℕ) (i k : ℕ) : ℝ :=
  if k = 0 then 1 - baireProb i else if k ≤ 2 ^ L i then baireProb i / 2 ^ L i else 0

/-- The measure `ν_i` on `ℕ` with mass `1 - p_i` at `0` and mass `p_i 2^{-L_i}` at each of
`1, …, 2^{L_i}`, for a length sequence `L`. Blueprint node `meas:examples`. -/
noncomputable def baireFactorOf (L : ℕ → ℕ) (i : ℕ) : Measure ℕ :=
  Measure.sum fun k ↦ ENNReal.ofReal (baireWeight L i k) • Measure.dirac k

/-- `p_i > 0`. -/
theorem baireProb_pos (i : ℕ) : 0 < baireProb i := by unfold baireProb; positivity

/-- `p_i ≤ 1/4`. -/
theorem baireProb_le (i : ℕ) : baireProb i ≤ 1 / 4 := by
  unfold baireProb
  rw [one_div]
  gcongr
  have : (0 : ℝ) ≤ i := i.cast_nonneg
  nlinarith

/-- `p_i L_i = 1`. -/
theorem baireProb_mul_baireLength (i : ℕ) : baireProb i * baireLength i = 1 := by
  unfold baireProb baireLength
  push_cast
  field_simp

/-- The weights are nonnegative. -/
theorem baireWeight_nonneg (L : ℕ → ℕ) (i k : ℕ) : 0 ≤ baireWeight L i k := by
  have := baireProb_pos i
  have := baireProb_le i
  unfold baireWeight
  split_ifs <;> first | linarith | positivity

/-- The weights vanish beyond `2^{L_i}`. -/
theorem baireWeight_eq_zero (L : ℕ → ℕ) (i : ℕ) {k : ℕ} (hk : 2 ^ L i < k) :
    baireWeight L i k = 0 := by
  have hk0 : k ≠ 0 := fun h ↦ by simp [h] at hk
  simp [baireWeight, hk0, not_le.2 hk]

/-- The weights sum to `1`. -/
theorem sum_baireWeight (L : ℕ → ℕ) (i : ℕ) :
    ∑ k ∈ Finset.range (2 ^ L i + 1), baireWeight L i k = 1 := by
  rw [Finset.sum_range_succ']
  have h : ∀ k ∈ Finset.range (2 ^ L i), baireWeight L i (k + 1) = baireProb i / 2 ^ L i :=
    fun k hk ↦ by
      rw [Finset.mem_range] at hk
      simp [baireWeight, Nat.succ_le_of_lt hk]
  rw [Finset.sum_congr rfl h, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  simp only [baireWeight, ite_true]
  push_cast
  field_simp
  ring

/-- The mass of a set under `ν_i` is the sum of the weights of its points. -/
theorem baireFactorOf_apply (L : ℕ → ℕ) (i : ℕ) (S : Set ℕ) :
    baireFactorOf L i S = ∑' k, S.indicator (fun k ↦ ENNReal.ofReal (baireWeight L i k)) k := by
  rw [baireFactorOf, Measure.sum_apply _ (MeasurableSet.of_discrete)]
  congr 1 with k
  rw [Measure.smul_apply, Measure.dirac_apply' _ (MeasurableSet.of_discrete)]
  by_cases hk : k ∈ S <;> simp [hk]

/-- `ν_i {k}` is the weight of `k`. -/
theorem baireFactorOf_singleton (L : ℕ → ℕ) (i k : ℕ) :
    baireFactorOf L i {k} = ENNReal.ofReal (baireWeight L i k) := by
  rw [baireFactorOf_apply, tsum_eq_single k (fun j hj ↦ by simp [hj])]
  simp

/-- A set of points of weight `0` is `ν_i`-null. -/
theorem baireFactorOf_eq_zero (L : ℕ → ℕ) (i : ℕ) {S : Set ℕ}
    (hS : ∀ k ∈ S, baireWeight L i k = 0) : baireFactorOf L i S = 0 := by
  rw [baireFactorOf_apply]
  refine ENNReal.tsum_eq_zero.2 fun k ↦ ?_
  by_cases hk : k ∈ S <;> simp [hk, hS]

/-- `ν_i` is a probability measure. -/
instance (L : ℕ → ℕ) (i : ℕ) : IsProbabilityMeasure (baireFactorOf L i) := by
  constructor
  rw [baireFactorOf_apply, tsum_eq_sum (s := Finset.range (2 ^ L i + 1))]
  · simp only [indicator_univ]
    rw [← ENNReal.ofReal_sum_of_nonneg (fun k _ ↦ baireWeight_nonneg L i k), sum_baireWeight,
      ENNReal.ofReal_one]
  · intro k hk
    rw [Finset.mem_range, not_lt] at hk
    simp [baireWeight_eq_zero L i (show 2 ^ L i < k by omega)]

/-- `ν_i(ℕ ∖ {0}) ≤ p_i`. -/
theorem baireFactorOf_ne_zero_le (L : ℕ → ℕ) (i : ℕ) :
    baireFactorOf L i {k | k ≠ 0} ≤ ENNReal.ofReal (baireProb i) := by
  have hS : {k : ℕ | k ≠ 0} = {0}ᶜ := by ext; simp
  have hp := baireProb_le i
  rw [hS, prob_compl_eq_one_sub (MeasurableSet.of_discrete), baireFactorOf_singleton,
    tsub_le_iff_right, ← ENNReal.ofReal_add (baireProb_pos i).le (baireWeight_nonneg L i 0)]
  simp [baireWeight]

/-- The product measure `μ = ⨂_i ν_i` for a length sequence `L`. Blueprint node
`meas:examples`. -/
noncomputable def baireMeasureOf (L : ℕ → ℕ) : Measure (ℕ → ℕ) :=
  Measure.infinitePi (baireFactorOf L)

/-- `μ` is a probability measure. -/
instance (L : ℕ → ℕ) : IsProbabilityMeasure (baireMeasureOf L) := by
  unfold baireMeasureOf; infer_instance

/-- The factor `ν_i` of Example 5.4, with `L_i = (i + 2)^2`. Blueprint node `meas:examples`. -/
noncomputable abbrev baireFactor (i : ℕ) : Measure ℕ := baireFactorOf baireLength i

/-- The measure `μ = ⨂_i ν_i` of Example 5.4, with `L_i = (i + 2)^2`.
Blueprint node `meas:examples`. -/
noncomputable abbrev baireMeasure : Measure (ℕ → ℕ) := baireMeasureOf baireLength

/-! ### Summability -/

/-- `∑ p_i < ∞`. -/
theorem summable_baireProb : Summable baireProb := by
  have h := (summable_nat_add_iff 2).2 (Real.summable_one_div_nat_pow.2 one_lt_two)
  refine h.congr fun i ↦ ?_
  simp [baireProb]

/-- `-(1 - p) log (1 - p) ≤ p` for `p < 1`. -/
private lemma neg_one_sub_mul_log_one_sub_le {p : ℝ} (hp1 : p < 1) :
    -((1 - p) * Real.log (1 - p)) ≤ p := by
  have h1 : 0 < 1 - p := by linarith
  have := Real.one_sub_inv_le_log_of_pos h1
  have h2 : (1 - p) * (1 - (1 - p)⁻¹) = -p := by field_simp; ring
  nlinarith [mul_le_mul_of_nonneg_left this h1.le]

/-- `-log (1 - p) ≤ 2 p` for `0 ≤ p ≤ 1/2`. -/
private lemma neg_log_one_sub_le {p : ℝ} (hp0 : 0 ≤ p) (hp : p ≤ 1 / 2) :
    -Real.log (1 - p) ≤ 2 * p := by
  have h1 : 0 < 1 - p := by linarith
  have := Real.one_sub_inv_le_log_of_pos h1
  have h2 : 1 - (1 - p)⁻¹ = -(p / (1 - p)) := by field_simp; ring
  have h3 : p / (1 - p) ≤ 2 * p := by
    rw [div_le_iff₀ h1]; nlinarith
  linarith

/-- Example 5.4: `∑_i H(p_i) < ∞` (binary entropies, here in nats). -/
theorem summable_binEntropy_baireProb : Summable fun i ↦ Real.binEntropy (baireProb i) := by
  have hs : Summable fun i : ℕ ↦ 4 * (((i + 2 : ℕ) : ℝ) ^ (3 / 2 : ℝ))⁻¹ + baireProb i :=
    (((summable_nat_add_iff 2).2 (Real.summable_nat_rpow_inv.2 (by norm_num))).mul_left 4).add
      summable_baireProb
  refine hs.of_nonneg_of_le (fun i ↦ Real.binEntropy_nonneg (baireProb_pos i).le
    (by linarith [baireProb_le i])) fun i ↦ ?_
  have hp := baireProb_pos i
  have hp4 := baireProb_le i
  have hx : (0 : ℝ) < i + 2 := by positivity
  rw [Real.binEntropy]
  have hB : (1 - baireProb i) * Real.log (1 - baireProb i)⁻¹ ≤ baireProb i := by
    rw [Real.log_inv]; linarith [neg_one_sub_mul_log_one_sub_le (p := baireProb i) (by linarith)]
  have hA : baireProb i * Real.log (baireProb i)⁻¹ ≤
      4 * (((i + 2 : ℕ) : ℝ) ^ (3 / 2 : ℝ))⁻¹ := by
    have hlog := Real.log_le_rpow_div hx.le (by norm_num : (0 : ℝ) < 1 / 2)
    have hrp : ((i : ℝ) + 2) ^ (2 : ℕ) =
        ((i : ℝ) + 2) ^ (1 / 2 : ℝ) * ((i : ℝ) + 2) ^ (3 / 2 : ℝ) := by
      rw [← Real.rpow_add hx, ← Real.rpow_natCast]; norm_num
    have hpos : 0 < ((i : ℝ) + 2) ^ (3 / 2 : ℝ) := Real.rpow_pos_of_pos hx _
    have hpos' : 0 < ((i : ℝ) + 2) ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hx _
    simp only [baireProb, inv_inv, Real.log_pow]
    push_cast
    rw [hrp]
    field_simp
    nlinarith
  linarith

/-- The tail factors `-log₂ (1 - p_i)` are summable. -/
theorem tsum_infoBits_one_sub_baireProb_ne_top :
    ∑' i, infoBits (ENNReal.ofReal (1 - baireProb i)) ≠ ⊤ := by
  refine ne_top_of_le_ne_top ((summable_baireProb.mul_left (2 / Real.log 2)).tsum_ofReal_ne_top)
    (ENNReal.tsum_le_tsum fun i ↦ ?_)
  have hp := baireProb_pos i
  have hp4 := baireProb_le i
  have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  rw [infoBits_ofReal (by linarith)]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [Real.logb, ← neg_div, div_mul_eq_mul_div, mul_comm]
  exact div_le_div_of_nonneg_right
    (by linarith [neg_log_one_sub_le hp.le (by linarith : baireProb i ≤ 1 / 2)]) hl2.le

/-! ### Shannon entropy of the factors -/

/-- `ν_q {·}` contributes `q · (-log₂ q)` to the entropy. -/
private lemma infoBits_ofReal_mul {q : ℝ} (hq : 0 < q) :
    infoBits (ENNReal.ofReal q) * ENNReal.ofReal q = ENNReal.ofReal (q * -Real.logb 2 q) := by
  rw [infoBits_ofReal hq, ENNReal.ofReal_mul hq.le, mul_comm]

/-- The Shannon entropy of `ν_i` in bits: `H(ν_i) = H(p_i) + p_i L_i`, for any length sequence.
Here `H(p) = Real.binEntropy p / log 2`. Blueprint node `meas:examples`. -/
theorem lintegral_infoBits_baireFactorOf (L : ℕ → ℕ) (i : ℕ) :
    ∫⁻ k, infoBits (baireFactorOf L i {k}) ∂baireFactorOf L i =
      ENNReal.ofReal (Real.binEntropy (baireProb i) / Real.log 2 + baireProb i * L i) := by
  have hp := baireProb_pos i
  have hp4 := baireProb_le i
  set p := baireProb i with hpdef
  have h2L : (0 : ℝ) < 2 ^ L i := by positivity
  rw [lintegral_countable']
  simp_rw [baireFactorOf_singleton]
  rw [tsum_eq_sum (s := Finset.range (2 ^ L i + 1)) fun k hk ↦ by
      rw [Finset.mem_range, not_lt] at hk
      simp [baireWeight_eq_zero L i (show 2 ^ L i < k by omega)],
    Finset.sum_range_succ']
  have h : ∀ k ∈ Finset.range (2 ^ L i),
      infoBits (ENNReal.ofReal (baireWeight L i (k + 1))) *
          ENNReal.ofReal (baireWeight L i (k + 1)) =
        ENNReal.ofReal (p / 2 ^ L i * -Real.logb 2 (p / 2 ^ L i)) := fun k hk ↦ by
    rw [Finset.mem_range] at hk
    have hw : baireWeight L i (k + 1) = p / 2 ^ L i := by
      simp [baireWeight, Nat.succ_le_of_lt hk, hpdef]
    rw [hw, infoBits_ofReal_mul (by positivity)]
  have hw0 : baireWeight L i 0 = 1 - p := by simp [baireWeight, hpdef]
  rw [Finset.sum_congr rfl h, Finset.sum_const, Finset.card_range, nsmul_eq_mul, hw0,
    infoBits_ofReal_mul (by linarith)]
  have hA : 0 ≤ p / 2 ^ L i * -Real.logb 2 (p / 2 ^ L i) := by
    refine mul_nonneg (by positivity) (neg_nonneg.2 (Real.logb_nonpos one_lt_two (by positivity)
      ((div_le_one h2L).2 (by linarith [one_le_pow₀ (M₀ := ℝ) (n := L i) one_le_two]))))
  have hB : 0 ≤ (1 - p) * -Real.logb 2 (1 - p) :=
    mul_nonneg (by linarith) (neg_nonneg.2 (Real.logb_nonpos one_lt_two (by linarith)
      (by linarith)))
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_add (mul_nonneg (by positivity) hA) hB]
  congr 1
  push_cast
  have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hp1 : 0 < 1 - p := by linarith
  rw [Real.binEntropy, Real.logb, Real.logb, Real.log_div hp.ne' h2L.ne', Real.log_pow,
    Real.log_inv, Real.log_inv]
  field_simp
  ring

/-- Example 5.4: `H(ν_i) = H(p_i) + 1` bits, since `p_i L_i = 1`.
Blueprint node `meas:examples`. -/
theorem lintegral_infoBits_baireFactor (i : ℕ) :
    ∫⁻ k, infoBits (baireFactor i {k}) ∂baireFactor i =
      1 + ENNReal.ofReal (Real.binEntropy (baireProb i) / Real.log 2) := by
  rw [lintegral_infoBits_baireFactorOf, baireProb_mul_baireLength, add_comm,
    ENNReal.ofReal_add zero_le_one (div_nonneg (Real.binEntropy_nonneg (baireProb_pos i).le
      (by linarith [baireProb_le i])) (Real.log_pos one_lt_two).le), ENNReal.ofReal_one]

/-- Example 5.4: the mean information of the `n`-cylinders is `∑_{i<n} H(ν_i)`, with
`H(ν_i) = H(p_i) + p_i L_i` bits. Blueprint node `meas:examples`. -/
theorem lintegral_infoBits_cylinder_baireMeasureOf (L : ℕ → ℕ) (n : ℕ) :
    ∫⁻ x, infoBits (baireMeasureOf L (PiNat.cylinder x n)) ∂baireMeasureOf L =
      ∑ i ∈ Finset.range n,
        ENNReal.ofReal (Real.binEntropy (baireProb i) / Real.log 2 + baireProb i * L i) := by
  rw [baireMeasureOf, lintegral_infoBits_infinitePi_cylinder_nat]
  exact Finset.sum_congr rfl fun i _ ↦ lintegral_infoBits_baireFactorOf L i

/-! ### Local entropies: Borel–Cantelli -/

/-- Example 5.4: since `∑ p_i < ∞`, by Borel–Cantelli almost every point has only finitely many
nonzero coordinates. Blueprint node `meas:examples`. -/
theorem ae_eventually_eq_zero_baireMeasureOf (L : ℕ → ℕ) :
    ∀ᵐ x ∂baireMeasureOf L, ∀ᶠ i in atTop, x i = 0 := by
  have hBC : ∀ᵐ x ∂baireMeasureOf L, {i | x ∈ {y : ℕ → ℕ | y i ≠ 0}}.Finite := by
    refine ae_finite_setOfPred_mem (ne_top_of_le_ne_top summable_baireProb.tsum_ofReal_ne_top
      (ENNReal.tsum_le_tsum fun i ↦ ?_))
    rw [show {y : ℕ → ℕ | y i ≠ 0} = (fun y : ℕ → ℕ ↦ y i) ⁻¹' {k | k ≠ 0} from rfl,
      baireMeasureOf, infinitePi_preimage_eval_nat]
    exact baireFactorOf_ne_zero_le L i
  filter_upwards [hBC] with x hfin
  obtain ⟨N, hN⟩ := hfin.bddAbove
  filter_upwards [eventually_gt_atTop N] with i hi
  by_contra h
  exact absurd (hN h) (not_le.2 hi)

/-- Example 5.4: for almost every `x`, `-log₂ μ[x↾n]` is bounded in `n`.
Blueprint node `meas:examples`. -/
theorem ae_exists_infoBits_cylinder_le (L : ℕ → ℕ) :
    ∀ᵐ x ∂baireMeasureOf L, ∃ M : ℝ≥0∞, M ≠ ⊤ ∧
      ∀ n, infoBits (baireMeasureOf L (PiNat.cylinder x n)) ≤ M := by
  filter_upwards [ae_eventually_eq_zero_baireMeasureOf L,
    ae_infinitePi_apply_ne_zero (baireFactorOf L)] with x hev hpos
  obtain ⟨N, hN⟩ := eventually_atTop.1 hev
  set f : ℕ → ℝ≥0∞ := fun i ↦ infoBits (baireFactorOf L i {x i}) with hf
  set g : ℕ → ℝ≥0∞ := fun i ↦ infoBits (ENNReal.ofReal (1 - baireProb i)) with hg
  set s : Finset ℕ := Finset.range N with hs
  refine ⟨∑ i ∈ s, f i + ∑' i, g i, ENNReal.add_ne_top.2
    ⟨ENNReal.sum_ne_top.2 fun i _ ↦ (infoBits_lt_top (hpos i)).ne,
      tsum_infoBits_one_sub_baireProb_ne_top⟩, fun n ↦ ?_⟩
  rw [baireMeasureOf, infoBits_infinitePi_cylinder_nat]
  have hfg : ∀ i, f i ≤ (s : Set ℕ).indicator f i + g i := fun i ↦ by
    by_cases hi : i ∈ s
    · rw [indicator_of_mem (by simpa using hi)]
      exact le_self_add
    · rw [indicator_of_notMem (by simpa using hi), zero_add]
      have : x i = 0 := hN i (by simpa [hs] using hi)
      simp [hf, hg, this, baireFactorOf_singleton, baireWeight]
  calc ∑ i ∈ Finset.range n, f i
      ≤ ∑ i ∈ Finset.range n, ((s : Set ℕ).indicator f i + g i) :=
        Finset.sum_le_sum fun i _ ↦ hfg i
    _ = ∑ i ∈ Finset.range n, (s : Set ℕ).indicator f i + ∑ i ∈ Finset.range n, g i :=
        Finset.sum_add_distrib
    _ ≤ ∑' i, (s : Set ℕ).indicator f i + ∑' i, g i :=
        add_le_add (ENNReal.sum_le_tsum _) (ENNReal.sum_le_tsum _)
    _ = ∑ i ∈ s, f i + ∑' i, g i := by
        rw [tsum_eq_sum (s := s) fun i hi ↦ indicator_of_notMem (by simpa using hi) _]
        congr 1
        exact Finset.sum_congr rfl fun i hi ↦ indicator_of_mem (by simpa using hi) _

/-- `M / n → 0` for finite `M`. -/
private lemma tendsto_div_natCast_zero {M : ℝ≥0∞} (hM : M ≠ ⊤) :
    Tendsto (fun n : ℕ ↦ M / n) atTop (𝓝 0) := by
  simpa [div_eq_mul_inv] using
    ENNReal.Tendsto.const_mul ENNReal.tendsto_inv_nat_nhds_zero (Or.inr hM)

/-- Bounded information has growth rates `(0, 0)`. -/
private lemma rates_eq_zero_of_le {a : ℕ → ℝ≥0∞} {M : ℝ≥0∞} (hM : M ≠ ⊤) (h : ∀ n, a n ≤ M) :
    (liminf (fun n : ℕ ↦ a n / n) atTop, limsup (fun n : ℕ ↦ a n / n) atTop) = (0, 0) := by
  have ht := tendsto_div_natCast_zero hM
  have hs : limsup (fun n : ℕ ↦ a n / n) atTop ≤ 0 :=
    (limsup_le_limsup (.of_forall fun n ↦ ENNReal.div_le_div_right (h n) _)).trans
      ht.limsup_eq.le
  exact Prod.ext (le_antisymm (le_trans liminf_le_limsup hs) bot_le) (le_antisymm hs bot_le)

/-- Example 5.4: `Φ_μ = (0, 0)` almost everywhere, for any length sequence `L`.
Blueprint node `meas:examples`. -/
theorem ae_localEntropy_baireMeasureOf (L : ℕ → ℕ) :
    ∀ᵐ x ∂baireMeasureOf L, localEntropy (baireMeasureOf L) shiftMap x = (0, 0) := by
  filter_upwards [ae_exists_infoBits_cylinder_le L] with x ⟨M, hM, h⟩
  rw [localEntropy_shiftMap (by norm_num) (by norm_num) (fun _ _ ↦ baireMetricSpace_dist_eq)]
  exact rates_eq_zero_of_le hM h

/-- Example 5.4: `Φ_μ = (0, 0)` almost everywhere. Blueprint node `meas:examples`. -/
theorem ae_localEntropy_baireMeasure :
    ∀ᵐ x ∂baireMeasure, localEntropy baireMeasure shiftMap x = (0, 0) :=
  ae_localEntropy_baireMeasureOf baireLength

/-- Example 5.4: `Λ_μ = δ_{(0, 0)}`, for any length sequence `L`.
Blueprint node `meas:examples`. -/
theorem entropyLaw_baireMeasureOf (L : ℕ → ℕ) :
    entropyLaw (baireMeasureOf L) shiftMap = Measure.dirac (0, 0) := by
  rw [entropyLaw, Measure.map_congr (ae_localEntropy_baireMeasureOf L), Measure.map_const]
  simp

/-- Example 5.4: `Λ_μ = δ_{(0, 0)}`. Blueprint node `meas:examples`. -/
theorem entropyLaw_baireMeasure :
    entropyLaw baireMeasure shiftMap = Measure.dirac (0, 0) :=
  entropyLaw_baireMeasureOf baireLength

/-- Example 5.4: `h̲_μ(σ) = h̄_μ(σ) = 0`, for any length sequence `L`.
Blueprint node `meas:examples`. -/
theorem measureEntropy_baireMeasureOf (L : ℕ → ℕ) :
    measureEntropy (baireMeasureOf L) shiftMap = (0, 0) := by
  have h := ae_localEntropy_baireMeasureOf L
  refine Prod.ext ?_ ?_
  · refine (lintegral_congr_ae (g := fun _ ↦ 0) (h.mono fun x hx ↦ ?_)).trans lintegral_zero
    simp [hx]
  · refine (lintegral_congr_ae (g := fun _ ↦ 0) (h.mono fun x hx ↦ ?_)).trans lintegral_zero
    simp [hx]

/-- Example 5.4: `h̲_μ(σ) = h̄_μ(σ) = 0`. Blueprint node `meas:examples`. -/
theorem measureEntropy_baireMeasure : measureEntropy baireMeasure shiftMap = (0, 0) :=
  measureEntropy_baireMeasureOf baireLength

/-! ### Information rates -/

/-- Mean information between `n` and `n + C` has growth rates `(1, 1)`. -/
private lemma rates_eq_one_of {a : ℕ → ℝ≥0∞} {C : ℝ≥0∞} (hC : C ≠ ⊤)
    (h₁ : ∀ n : ℕ, (n : ℝ≥0∞) ≤ a n) (h₂ : ∀ n : ℕ, a n ≤ n + C) :
    (liminf (fun n : ℕ ↦ a n / n) atTop, limsup (fun n : ℕ ↦ a n / n) atTop) = (1, 1) := by
  have hn : ∀ n : ℕ, 1 ≤ n → (n : ℝ≥0∞) / n = 1 := fun n hn ↦
    ENNReal.div_self (by exact_mod_cast (Nat.one_pos.trans_le hn).ne') (ENNReal.natCast_ne_top n)
  have hl : 1 ≤ liminf (fun n : ℕ ↦ a n / n) atTop :=
    le_liminf_of_le (by isBoundedDefault) ((eventually_ge_atTop (1 : ℕ)).mono fun n h ↦
      (hn n h).symm.le.trans (ENNReal.div_le_div_right (h₁ n) _))
  have ht : Tendsto (fun n : ℕ ↦ 1 + C / n) atTop (𝓝 1) := by
    simpa [div_eq_mul_inv] using tendsto_const_nhds.add
      (ENNReal.Tendsto.const_mul ENNReal.tendsto_inv_nat_nhds_zero (Or.inr hC))
  have hu : limsup (fun n : ℕ ↦ a n / n) atTop ≤ 1 :=
    (limsup_le_limsup ((eventually_ge_atTop (1 : ℕ)).mono fun n h ↦
      (ENNReal.div_le_div_right (h₂ n) _).trans_eq (by rw [ENNReal.add_div, hn n h]))).trans
      ht.limsup_eq.le
  exact Prod.ext (le_antisymm (le_trans liminf_le_limsup hu) hl)
    (le_antisymm hu (le_trans hl liminf_le_limsup))

/-- Example 5.4: `H̲_μ(σ) = H̄_μ(σ) = 1`, since the mean information of the `n`-cylinders is
`n + ∑_{i<n} H(p_i) = n + O(1)`. Blueprint node `meas:examples`. -/
theorem informationRate_baireMeasure : informationRate baireMeasure shiftMap = (1, 1) := by
  rw [informationRate_shiftMap (by norm_num) (by norm_num) (fun _ _ ↦ baireMetricSpace_dist_eq)]
  set h : ℕ → ℝ≥0∞ := fun i ↦ ENNReal.ofReal (Real.binEntropy (baireProb i) / Real.log 2)
    with hh
  have ha : ∀ n : ℕ, ∫⁻ x, infoBits (baireMeasure (PiNat.cylinder x n)) ∂baireMeasure =
      n + ∑ i ∈ Finset.range n, h i := fun n ↦ by
    rw [baireMeasure, lintegral_infoBits_cylinder_baireMeasureOf]
    calc _ = ∑ i ∈ Finset.range n, (1 + h i) := Finset.sum_congr rfl fun i _ ↦ by
            rw [← lintegral_infoBits_baireFactorOf]
            exact lintegral_infoBits_baireFactor i
      _ = n + ∑ i ∈ Finset.range n, h i := by rw [Finset.sum_add_distrib]; simp
  simp only [ha]
  exact rates_eq_one_of (C := ∑' i, h i)
    ((summable_binEntropy_baireProb.div_const (Real.log 2)).tsum_ofReal_ne_top)
    (fun _ ↦ le_self_add) fun _ ↦ add_le_add le_rfl (ENNReal.sum_le_tsum _)

/-- Example 5.4 / Proposition 4.7 (compactness is needed): for the Borel probability measure
`μ = ⨂_i ν_i` on Baire space (complete, separable, not compact) and the continuous shift,
`H̄_μ(σ) = 1 > 0 = h̄_μ(σ)`, so the inequality `H̄_μ(T) ≤ h̄_μ(T)` of Proposition 4.7
(`informationRate_snd_le_measureEntropy_snd`) fails without compactness.
Blueprint node `meas:examples`. -/
theorem measureEntropy_snd_lt_informationRate_snd_baireMeasure :
    (measureEntropy baireMeasure shiftMap).2 < (informationRate baireMeasure shiftMap).2 := by
  rw [measureEntropy_baireMeasure, informationRate_baireMeasure]
  exact zero_lt_one

/-- Example 5.4, existence form: there are a complete separable, non-compact metric space, a
Borel probability measure `μ` on it and a continuous map `T` with `H̄_μ(T) > h̄_μ(T)`.
Blueprint node `meas:examples`. -/
theorem exists_measure_measureEntropy_lt_informationRate :
    ∃ (X : Type) (_ : MetricSpace X) (_ : MeasurableSpace X), BorelSpace X ∧ CompleteSpace X ∧
      SecondCountableTopology X ∧ ¬ CompactSpace X ∧ ∃ (μ : Measure X) (T : X → X),
        IsProbabilityMeasure μ ∧ Continuous T ∧
          (measureEntropy μ T).2 < (informationRate μ T).2 :=
  ⟨ℕ → ℕ, baireMetricSpace, inferInstance, inferInstance, inferInstance, inferInstance,
    not_compactSpace_baireMetricSpace, baireMeasure, shiftMap, inferInstance,
    continuous_shiftMap_baire, measureEntropy_snd_lt_informationRate_snd_baireMeasure⟩

/-! ### Further remarks of Example 5.4 -/

/-- The variant length `L_i = (i + 2)^3` of the remark in Example 5.4. -/
def baireLengthCube (i : ℕ) : ℕ := (i + 2) ^ 3

/-- `p_i (i + 2)^3 = i + 2`. -/
theorem baireProb_mul_baireLengthCube (i : ℕ) : baireProb i * baireLengthCube i = i + 2 := by
  unfold baireProb baireLengthCube
  push_cast
  field_simp

/-- Example 5.4, remark: with `L_i = (i + 2)^3` the information rates are infinite
(`H̲_μ(σ) = H̄_μ(σ) = ∞`), while the local entropies still vanish almost everywhere
(`measureEntropy_baireMeasureOf`). Blueprint node `meas:examples`. -/
theorem informationRate_baireMeasureOf_cube :
    informationRate (baireMeasureOf baireLengthCube) shiftMap = (⊤, ⊤) := by
  rw [informationRate_shiftMap (by norm_num) (by norm_num) (fun _ _ ↦ baireMetricSpace_dist_eq)]
  simp only [lintegral_infoBits_cylinder_baireMeasureOf]
  set a : ℕ → ℝ≥0∞ := fun n ↦ ∑ i ∈ Finset.range n, ENNReal.ofReal
    (Real.binEntropy (baireProb i) / Real.log 2 + baireProb i * baireLengthCube i) with ha
  have hk : ∀ k : ℕ, ∀ n : ℕ, 2 * k + 1 ≤ n → (k : ℝ≥0∞) ≤ a n / n := fun k n hn ↦ by
    have hn0 : (n : ℝ≥0∞) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
    rw [ENNReal.le_div_iff_mul_le (Or.inl hn0) (Or.inl (ENNReal.natCast_ne_top n))]
    have hsum : k * n ≤ ∑ i ∈ Finset.range n, (i + 2) := by
      have hg := Finset.sum_range_id_mul_two n
      rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, smul_eq_mul]
      have : n - 1 + 1 = n := by omega
      nlinarith
    calc (k : ℝ≥0∞) * n = ((k * n : ℕ) : ℝ≥0∞) := by push_cast; ring
      _ ≤ ((∑ i ∈ Finset.range n, (i + 2) : ℕ) : ℝ≥0∞) := by exact_mod_cast hsum
      _ = ∑ i ∈ Finset.range n, ENNReal.ofReal (baireProb i * baireLengthCube i) := by
          push_cast
          refine Finset.sum_congr rfl fun i _ ↦ ?_
          rw [baireProb_mul_baireLengthCube, ENNReal.ofReal_add (by positivity) (by norm_num),
            ENNReal.ofReal_natCast, ENNReal.ofReal_ofNat]
      _ ≤ a n := Finset.sum_le_sum fun i _ ↦ ENNReal.ofReal_le_ofReal (le_add_of_nonneg_left
          (div_nonneg (Real.binEntropy_nonneg (baireProb_pos i).le
            (by linarith [baireProb_le i])) (Real.log_pos one_lt_two).le))
  have hl : liminf (fun n : ℕ ↦ a n / n) atTop = ⊤ := by
    by_contra hne
    obtain ⟨k, hlt⟩ := ENNReal.exists_nat_gt hne
    exact hlt.not_ge (le_liminf_of_le (by isBoundedDefault)
      ((eventually_ge_atTop (2 * k + 1)).mono fun n hn ↦ hk k n hn))
  exact Prod.ext hl (top_le_iff.1 (hl ▸ liminf_le_limsup))

/-- The compact set `∏_i {0, …, 2^{L_i}}` carrying `μ`. Blueprint node `meas:examples`. -/
def baireSupport (L : ℕ → ℕ) : Set (ℕ → ℕ) := univ.pi fun i ↦ Iic (2 ^ L i)

/-- `∏_i {0, …, 2^{L_i}}` is compact. -/
theorem isCompact_baireSupport (L : ℕ → ℕ) : IsCompact (baireSupport L) :=
  isCompact_univ_pi fun _ ↦ (finite_Iic _).isCompact

/-- Example 5.4, remark: `μ` is carried by the compact set `∏_i {0, …, 2^{L_i}}`.
Blueprint node `meas:examples`. -/
theorem ae_mem_baireSupport (L : ℕ → ℕ) : ∀ᵐ x ∂baireMeasureOf L, x ∈ baireSupport L := by
  have : ∀ᵐ x ∂baireMeasureOf L, ∀ i, x i ∈ Iic (2 ^ L i) := ae_all_iff.2 fun i ↦ by
    rw [ae_iff]
    change baireMeasureOf L ((fun x : ℕ → ℕ ↦ x i) ⁻¹' {k | k ∉ Iic (2 ^ L i)}) = 0
    rw [baireMeasureOf, infinitePi_preimage_eval_nat]
    exact baireFactorOf_eq_zero L i fun k hk ↦ baireWeight_eq_zero L i (not_le.1 hk)
  filter_upwards [this] with x hx using mem_univ_pi.2 hx

/-- Example 5.4, remark: the complement of `∏_i {0, …, 2^{L_i}}` is `μ`-null.
Blueprint node `meas:examples`. -/
theorem baireMeasureOf_compl_baireSupport (L : ℕ → ℕ) :
    baireMeasureOf L (baireSupport L)ᶜ = 0 :=
  ae_iff.1 (ae_mem_baireSupport L)

/-- The compact set `{x ∈ ∏_i {0, …, 2^{L_i}} : x_i = 0 for i ≥ N}`. -/
def baireCompact (L : ℕ → ℕ) (N : ℕ) : Set (ℕ → ℕ) :=
  baireSupport L ∩ {x | ∀ i, N ≤ i → x i = 0}

/-- The sets `{x ∈ ∏_i {0, …, 2^{L_i}} : x_i = 0 for i ≥ N}` are compact. -/
theorem isCompact_baireCompact (L : ℕ → ℕ) (N : ℕ) : IsCompact (baireCompact L N) := by
  refine (isCompact_baireSupport L).inter_right ?_
  simp only [ofPred_forall]
  exact isClosed_iInter fun i ↦ isClosed_iInter fun _ ↦
    isClosed_eq (continuous_apply i) continuous_const

/-- Example 5.4, remark: the compact sets `{x ∈ ∏_i {0, …, 2^{L_i}} : x_i = 0 for i ≥ N}` have
`μ`-measure tending to `1`. (The accompanying claim on spanning numbers is not formalized.)
Blueprint node `meas:examples`. -/
theorem tendsto_baireMeasureOf_baireCompact (L : ℕ → ℕ) :
    Tendsto (fun N ↦ baireMeasureOf L (baireCompact L N)) atTop (𝓝 1) := by
  have hm : Monotone (baireCompact L) := fun N N' h x hx ↦
    ⟨hx.1, fun i hi ↦ hx.2 i (h.trans hi)⟩
  have hU : baireMeasureOf L (⋃ N, baireCompact L N) = 1 := by
    have hae : ∀ᵐ x ∂baireMeasureOf L, x ∈ ⋃ N, baireCompact L N := by
      filter_upwards [ae_mem_baireSupport L, ae_eventually_eq_zero_baireMeasureOf L]
        with x hx hev
      obtain ⟨N, hN⟩ := eventually_atTop.1 hev
      exact mem_iUnion.2 ⟨N, hx, hN⟩
    rw [measure_congr (ae_eq_univ.2 (ae_iff.1 hae)), measure_univ]
  have := tendsto_measure_iUnion_atTop (μ := baireMeasureOf L) hm
  rw [hU] at this
  exact this

/-- Example 5.4, remark: `μ` is not shift-invariant (the law of `x_0` is `ν_0`, that of
`(σ x)_0 = x_1` is `ν_1 ≠ ν_0`). Blueprint node `meas:examples`. -/
theorem map_shiftMap_baireMeasureOf_ne (L : ℕ → ℕ) :
    Measure.map shiftMap (baireMeasureOf L) ≠ baireMeasureOf L := by
  intro h
  have h1 := congrArg (fun m : Measure (ℕ → ℕ) ↦ m ((fun x : ℕ → ℕ ↦ x 0) ⁻¹' {0})) h
  rw [Measure.map_apply (show Measurable (shiftMap : (ℕ → ℕ) → ℕ → ℕ) from
      Measurable.of_eval fun j ↦ measurable_pi_apply (j + 1))
    ((measurable_pi_apply 0) (measurableSet_singleton 0)),
    show shiftMap ⁻¹' ((fun x : ℕ → ℕ ↦ x 0) ⁻¹' {0}) = (fun x : ℕ → ℕ ↦ x 1) ⁻¹' {0} from rfl,
    baireMeasureOf, infinitePi_preimage_eval_nat, infinitePi_preimage_eval_nat,
    baireFactorOf_singleton, baireFactorOf_singleton] at h1
  rw [ENNReal.ofReal_eq_ofReal_iff (baireWeight_nonneg L 1 0) (baireWeight_nonneg L 0 0)] at h1
  simp only [baireWeight, baireProb, ite_true] at h1
  norm_num at h1

/-! ### Rates in probability (remark after Proposition 6.10) -/

/-- For a finite measure, if almost every point eventually leaves the measurable sets `s n`,
their measures tend to `0`. -/
private lemma tendsto_measure_zero_of_ae_eventually {X : Type*} [MeasurableSpace X]
    {μ : Measure X} [IsFiniteMeasure μ] {s : ℕ → Set X} (hs : ∀ n, MeasurableSet (s n))
    (h : ∀ᵐ x ∂μ, ∀ᶠ n in atTop, x ∉ s n) : Tendsto (fun n ↦ μ (s n)) atTop (𝓝 0) := by
  have := tendsto_measure_of_ae_tendsto_indicator (μ := μ) atTop MeasurableSet.empty hs
    MeasurableSet.univ (measure_ne_top μ _) (.of_forall fun _ ↦ subset_univ _)
    (h.mono fun x hx ↦ hx.mono fun n hn ↦ by simp [hn])
  simpa using this

/-- Example 5.4: for almost every `x`, at every dyadic scale `ε`,
`-(1/n) log₂ μ(B_n(x, σ, ε)) → 0`. Blueprint node `meas:examples`. -/
theorem ae_tendsto_localEntropyRate_baireMeasureOf (L : ℕ → ℕ) :
    ∀ᵐ x ∂baireMeasureOf L, ∀ p : ℕ,
      Tendsto (fun n ↦ localEntropyRate (baireMeasureOf L) shiftMap x n (dyadicRadius p))
        atTop (𝓝 0) := by
  filter_upwards [ae_exists_infoBits_cylinder_le L] with x ⟨M, hM, h⟩ p
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (tendsto_div_natCast_zero hM) (.of_forall fun _ ↦ bot_le)
    ((eventually_ge_atTop 1).mono fun n hn ↦ ?_)
  rw [localEntropyRate, dyadicRadius, inv_eq_one_div, bowenBall_shiftMap_eq_cylinder
    (by norm_num) (by norm_num) (fun _ _ ↦ baireMetricSpace_dist_eq) x hn p]
  exact ENNReal.div_le_div_right (h _) _

/-- Remark after Proposition 6.10, upper rate in probability: in Example 5.4, at every dyadic
scale `ε` and for every `β > 0`, `μ{x : -(1/n) log₂ μ(B_n(x, σ, ε)) > β} → 0`; that is, the
upper rate in probability `H̄^p_μ(σ, ε)` (`upperProbRate` of `Measure/ProbabilityRate.lean`)
is `0`, while `H̄_μ(σ) = 1`, so `H̄_μ ≤ H̄^p_μ` also needs compactness. Stated through the
defining limits rather than `upperProbRate`, which this file does not import.
Blueprint node `meas:examples`. -/
theorem tendsto_measure_lt_localEntropyRate_baireMeasureOf (L : ℕ → ℕ) (p : ℕ) {β : ℝ≥0∞}
    (hβ : 0 < β) :
    Tendsto (fun n : ℕ ↦ baireMeasureOf L
      {x | β < localEntropyRate (baireMeasureOf L) shiftMap x n (dyadicRadius p)})
      atTop (𝓝 0) :=
  tendsto_measure_zero_of_ae_eventually
    (fun n ↦ measurableSet_lt measurable_const
      (measurable_localEntropyRate _ continuous_shiftMap_baire n _))
    ((ae_tendsto_localEntropyRate_baireMeasureOf L).mono fun _ hx ↦
      ((hx p).eventually (gt_mem_nhds hβ)).mono fun _ hn ↦ not_lt.2 hn.le)

/-- Remark after Proposition 6.10, lower rate in probability: in Example 5.4, at every dyadic
scale `ε` and for every `α > 0`, `μ{x : -(1/n) log₂ μ(B_n(x, σ, ε)) < α} → 1`, so no `α > 0`
satisfies `μ{f_n^ε < α} → 0`; that is, the lower rate in probability `H̲^p_μ(σ, ε)`
(`lowerProbRate`) is `0`. Blueprint node `meas:examples`. -/
theorem tendsto_measure_localEntropyRate_lt_baireMeasureOf (L : ℕ → ℕ) (p : ℕ) {α : ℝ≥0∞}
    (hα : 0 < α) :
    Tendsto (fun n : ℕ ↦ baireMeasureOf L
      {x | localEntropyRate (baireMeasureOf L) shiftMap x n (dyadicRadius p) < α})
      atTop (𝓝 1) := by
  have hmeas : ∀ n : ℕ, MeasurableSet
      {x | α ≤ localEntropyRate (baireMeasureOf L) shiftMap x n (dyadicRadius p)} := fun n ↦
    measurableSet_le measurable_const
      (measurable_localEntropyRate _ continuous_shiftMap_baire n _)
  have h0 := tendsto_measure_zero_of_ae_eventually hmeas
    ((ae_tendsto_localEntropyRate_baireMeasureOf L).mono fun _ hx ↦
      ((hx p).eventually (gt_mem_nhds hα)).mono fun _ hn ↦ not_le.2 hn)
  have h1 := ENNReal.Tendsto.sub tendsto_const_nhds h0 (Or.inl ENNReal.one_ne_top)
  rw [tsub_zero] at h1
  refine h1.congr fun n ↦ ?_
  rw [← prob_compl_eq_one_sub (hmeas n)]
  congr 1
  ext x
  simp

end Kolmogorov.PointToSet
