/-
Copyright (c) 2026 Emma Dinowitz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emma Dinowitz
-/
import KolmogorovMathlib.PointToSet.Measure.ShiftProduct
import KolmogorovMathlib.PointToSet.Measure.ShiftBernoulli

/-!
# Anti-phase product measures and their mixtures (Examples 5.1, 5.2, 6.8)

On Cantor space `ℕ → Bool` with the shift and the Cantor metric (E. Dinowitz, *Entropy of
non-invariant measures and orbit complexity of random points*, Examples 5.1, 5.2, 6.8 and §6.1).
Fix a bias `p ∈ (0, 1/2)` and write `a = H(p)` (`bitEntropy p`).

* Example 5.1, concrete case: `blockBias p` has `β_i = 1/2` on the block pattern
  `⋃_j [4^j, 2·4^j)` and `β_i = p` off it; `μ₁ = productBernoulli (blockBias p)`.
  `entropyAverages_blockBias`: `a̲ = (1 + 2a)/3` and `ā = (2 + a)/3`;
  `entropyAverages_blockBias_lt`: `a̲ < ā`; `entropyLaw_blockBias`,
  `informationRate_blockBias`: the entropy law, Feng–Huang entropies, essential bounds and
  information rates of `μ₁`.
* `blockBiasSwap p` exchanges the roles of `1/2` and `p` (`μ₂`); it has the same averages
  (`entropyAverages_blockBiasSwap`, `entropyLaw_blockBiasSwap`).
* Example 6.8: `segmentMixture t ν₁ ν₂ = t ν₁ + (1 - t) ν₂` and
  `antiPhaseSegment p t = t μ₁ + (1 - t) μ₂`. `entropyLaw_antiPhaseSegment`:
  `Λ_{μ_t} = δ_{((1+2a)/3, (2+a)/3)}` for every `t ∈ [0, 1]`, with the Feng–Huang entropies and
  essential bounds; `informationRate_antiPhaseSegment`:
  `H̲_{μ_t} = (1+a)/2 - |2t-1|(1-a)/6`, `H̄_{μ_t} = (1+a)/2 + |2t-1|(1-a)/6`;
  `informationRate_antiPhaseSegment_of_endpoint`: at `t ∈ {0, 1}` the information rates are the
  Feng–Huang entropies.
* Example 5.2: `antiPhaseMixture p = ½ (μ₁ + μ₂)` (`= antiPhaseSegment p ½`);
  `entropyLaw_antiPhaseMixture`, `informationRate_antiPhaseMixture` (`H̲_μ = H̄_μ = (1+a)/2`) and
  `antiPhaseMixture_strict`: `h̲_μ < H̲_μ = H̄_μ < h̄_μ`.

The mean information of a mixture is controlled on each component
(`lintegral_infoBits_segmentMixture_bounds`): Gibbs' inequality gives the lower bound
`t I_n(ν₁) + (1 - t) I_n(ν₂)`, and since `μ_t ≥ t ν₁` each cylinder costs at most `-log₂ t`
extra bits on `ν₁` (and `-log₂ (1 - t)` on `ν₂`), which gives the upper bound plus `H(t)`.
With `I_n(μ₁) = n (a + (1 - a) f_n)` and `I_n(μ₂) = n (1 - (1 - a) f_n)` (`f_n` the density of
the block pattern) the normalized mean information of `μ_t` is
`(1 - t) + t a + (2t - 1)(1 - a) f_n + O(1/n)`, which agrees with the paper's
`(1 - t)(1 + a) + (2t - 1) A₁(n)`; its lower and upper limits are the paper's values.

The mutual singularity `μ₁ ⊥ μ₂` (Kakutani) is not needed and not stated.
Blueprint node `meas:examples`.
-/

namespace Kolmogorov.PointToSet

open Filter Set MeasureTheory ProbabilityTheory
open scoped Topology ENNReal unitInterval

attribute [local instance] cantorMetricSpace

/-! ### The concrete biases of Example 5.1 -/

/-- The bias `1/2` as a point of `[0, 1]`. -/
noncomputable def halfBias : I := ⟨2⁻¹, by norm_num, by norm_num⟩

/-- The value of `halfBias`. -/
lemma coe_halfBias : (halfBias : ℝ) = 2⁻¹ := rfl

/-- The entropy of a fair coin is one bit. -/
lemma bitEntropy_halfBias : bitEntropy (halfBias : ℝ) = 1 := by
  rw [coe_halfBias, bitEntropy, Real.binEntropy_two_inv,
    div_self (Real.log_pos one_lt_two).ne']

/-- Example 5.1 (concrete case): the biases `β_i = 1/2` for `i ∈ ⋃_j [4^j, 2·4^j)` and
`β_i = p` otherwise. Blueprint node `meas:examples`. -/
noncomputable def blockBias (p : I) (i : ℕ) : I := if blockPattern i then halfBias else p

/-- Example 5.2: the biases of Example 5.1 with the roles of `1/2` and `p` exchanged:
`β_i = p` for `i ∈ ⋃_j [4^j, 2·4^j)` and `β_i = 1/2` otherwise. Blueprint node `meas:examples`. -/
noncomputable def blockBiasSwap (p : I) (i : ℕ) : I := if blockPattern i then p else halfBias

/-- For `p < 1/2` the biases `blockBias p` lie in `[p, 1 - p]`. -/
lemma blockBias_mem {p : I} (hp : (p : ℝ) < 1 / 2) (i : ℕ) :
    (p : ℝ) ≤ blockBias p i ∧ (blockBias p i : ℝ) ≤ 1 - p := by
  unfold blockBias
  split_ifs
  · rw [coe_halfBias]; constructor <;> linarith
  · constructor <;> linarith

/-- For `p < 1/2` the biases `blockBiasSwap p` lie in `[p, 1 - p]`. -/
lemma blockBiasSwap_mem {p : I} (hp : (p : ℝ) < 1 / 2) (i : ℕ) :
    (p : ℝ) ≤ blockBiasSwap p i ∧ (blockBiasSwap p i : ℝ) ≤ 1 - p := by
  unfold blockBiasSwap
  split_ifs
  · constructor <;> linarith
  · rw [coe_halfBias]; constructor <;> linarith

/-- `∑_{i<n} H(β_i) = a n + (1 - a) #{i < n : pattern}` for `β = blockBias p`, `a = H(p)`. -/
lemma sum_bitEntropy_blockBias (p : I) (n : ℕ) :
    ∑ i ∈ Finset.range n, bitEntropy (blockBias p i) =
      bitEntropy p * n + (1 - bitEntropy p) * blockCount n := by
  induction n with
  | zero => simp [blockCount]
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, blockCount_succ]
    by_cases h : blockPattern n
    · simp only [blockBias, h, ↓reduceIte, bitEntropy_halfBias]; push_cast; ring
    · simp only [blockBias, h, ↓reduceIte]; push_cast; ring

/-- `∑_{i<n} H(β_i) = n - (1 - a) #{i < n : pattern}` for `β = blockBiasSwap p`, `a = H(p)`. -/
lemma sum_bitEntropy_blockBiasSwap (p : I) (n : ℕ) :
    ∑ i ∈ Finset.range n, bitEntropy (blockBiasSwap p i) =
      n - (1 - bitEntropy p) * blockCount n := by
  induction n with
  | zero => simp [blockCount]
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, blockCount_succ]
    by_cases h : blockPattern n
    · simp only [blockBiasSwap, h, ↓reduceIte]; push_cast; ring
    · simp only [blockBiasSwap, h, ↓reduceIte, bitEntropy_halfBias]; push_cast; ring

/-- For `n ≥ 1`, `(1/n) ∑_{i<n} H(β_i) = a + (1 - a) f_n` for `β = blockBias p`. -/
lemma entropyAverage_blockBias (p : I) {n : ℕ} (hn : 1 ≤ n) :
    entropyAverage (blockBias p) n = bitEntropy p + (1 - bitEntropy p) * blockFrequency n := by
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  rw [entropyAverage, sum_bitEntropy_blockBias, blockFrequency]
  field_simp

/-- For `n ≥ 1`, `(1/n) ∑_{i<n} H(β_i) = 1 - (1 - a) f_n` for `β = blockBiasSwap p`. -/
lemma entropyAverage_blockBiasSwap (p : I) {n : ℕ} (hn : 1 ≤ n) :
    entropyAverage (blockBiasSwap p) n = 1 + -(1 - bitEntropy p) * blockFrequency n := by
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  rw [entropyAverage, sum_bitEntropy_blockBiasSwap, blockFrequency]
  field_simp
  ring

/-- `|1 - H(p)| = 1 - H(p)`. -/
private lemma abs_one_sub_bitEntropy (p : I) : |1 - bitEntropy p| = 1 - bitEntropy p :=
  abs_of_nonneg (sub_nonneg.2 (bitEntropy_le_one _))

/-- Example 5.1 (concrete case): for `β_i = 1/2` on `⋃_j [4^j, 2·4^j)` and `β_i = p` elsewhere,
`a̲ = (1 + 2a)/3` and `ā = (2 + a)/3` with `a = H(p)`. This confirms the paper's values. The
paper takes `p ∈ (0, 1/2)` rational; the computation holds for every `p ∈ [0, 1]`.
Blueprint node `meas:examples`. -/
theorem entropyAverages_blockBias (p : I) :
    lowerEntropyAverage (blockBias p) = ENNReal.ofReal ((1 + 2 * bitEntropy p) / 3) ∧
      upperEntropyAverage (blockBias p) = ENNReal.ofReal ((2 + bitEntropy p) / 3) := by
  have h := liminf_limsup_ofReal_of_blockFrequency (u := entropyAverage (blockBias p))
    (A := bitEntropy p) (B := 1 - bitEntropy p) (c := 0) fun n hn ↦ by
      rw [entropyAverage_blockBias p hn]; simp
  rw [abs_one_sub_bitEntropy] at h
  exact ⟨h.1.trans (congrArg _ (by ring)), h.2.trans (congrArg _ (by ring))⟩

/-- Example 5.2: the biases with `1/2` and `p` exchanged have the same averages
`a̲ = (1 + 2a)/3` and `ā = (2 + a)/3`. Blueprint node `meas:examples`. -/
theorem entropyAverages_blockBiasSwap (p : I) :
    lowerEntropyAverage (blockBiasSwap p) = ENNReal.ofReal ((1 + 2 * bitEntropy p) / 3) ∧
      upperEntropyAverage (blockBiasSwap p) = ENNReal.ofReal ((2 + bitEntropy p) / 3) := by
  have h := liminf_limsup_ofReal_of_blockFrequency (u := entropyAverage (blockBiasSwap p))
    (A := 1) (B := -(1 - bitEntropy p)) (c := 0) fun n hn ↦ by
      rw [entropyAverage_blockBiasSwap p hn]; simp
  rw [abs_neg, abs_one_sub_bitEntropy] at h
  exact ⟨h.1.trans (congrArg _ (by ring)), h.2.trans (congrArg _ (by ring))⟩

/-- For `p ≠ 1/2`, `H(p) < 1`. -/
lemma bitEntropy_lt_one {p : ℝ} (hp : p ≠ 2⁻¹) : bitEntropy p < 1 := by
  rw [bitEntropy, div_lt_one (Real.log_pos one_lt_two)]
  exact Real.binEntropy_lt_log_two.2 hp

/-- For `p ∈ (0, 1/2)`, `H(p) < 1`. -/
private lemma bitEntropy_lt_one_of_lt_half {p : I} (hp : (p : ℝ) < 1 / 2) : bitEntropy p < 1 :=
  bitEntropy_lt_one (by intro h; rw [h] at hp; norm_num at hp)

/-- Example 5.1 (concrete case): `a̲ = (1 + 2a)/3 < ā = (2 + a)/3` for `p ∈ (0, 1/2)`: the
measure has different lower and upper entropy. Blueprint node `meas:examples`. -/
theorem entropyAverages_blockBias_lt {p : I} (hp : (p : ℝ) < 1 / 2) :
    lowerEntropyAverage (blockBias p) < upperEntropyAverage (blockBias p) := by
  have ha := bitEntropy_lt_one_of_lt_half hp
  have ha0 := bitEntropy_nonneg p
  rw [(entropyAverages_blockBias p).1, (entropyAverages_blockBias p).2,
    ENNReal.ofReal_lt_ofReal_iff (by linarith)]
  linarith

/-! ### Entropy laws -/

/-- `μ₁`-a.e. the local entropies of `μ₁` are `((1+2a)/3, (2+a)/3)`. -/
lemma ae_localEntropy_blockBias {p : I} (hp0 : 0 < (p : ℝ)) (hp : (p : ℝ) < 1 / 2) :
    ∀ᵐ x ∂productBernoulli (blockBias p), localEntropy (productBernoulli (blockBias p))
      shiftMap x = (ENNReal.ofReal ((1 + 2 * bitEntropy p) / 3),
        ENNReal.ofReal ((2 + bitEntropy p) / 3)) := by
  have h := ae_localEntropy_productBernoulli hp0 (blockBias_mem hp)
  rwa [(entropyAverages_blockBias p).1, (entropyAverages_blockBias p).2] at h

/-- `μ₂`-a.e. the local entropies of `μ₂` are `((1+2a)/3, (2+a)/3)`. -/
lemma ae_localEntropy_blockBiasSwap {p : I} (hp0 : 0 < (p : ℝ)) (hp : (p : ℝ) < 1 / 2) :
    ∀ᵐ x ∂productBernoulli (blockBiasSwap p), localEntropy (productBernoulli (blockBiasSwap p))
      shiftMap x = (ENNReal.ofReal ((1 + 2 * bitEntropy p) / 3),
        ENNReal.ofReal ((2 + bitEntropy p) / 3)) := by
  have h := ae_localEntropy_productBernoulli hp0 (blockBiasSwap_mem hp)
  rwa [(entropyAverages_blockBiasSwap p).1, (entropyAverages_blockBiasSwap p).2] at h

/-- Example 5.1 (concrete case) and §6.1: for `p ∈ (0, 1/2)`, `a = H(p)`, the measure
`μ₁ = ⨂_i Bernoulli(β_i)` has entropy law `δ_{((1+2a)/3, (2+a)/3)}`, Feng–Huang entropies
`h̲ = (1+2a)/3`, `h̄ = (2+a)/3`, and the essential infimum and supremum of the lower (upper) local
entropy both equal `(1+2a)/3` (`(2+a)/3`). The paper takes `p` rational (for computability of
`μ₁`), which plays no role here. Blueprint node `meas:examples`. -/
theorem entropyLaw_blockBias {p : I} (hp0 : 0 < (p : ℝ)) (hp : (p : ℝ) < 1 / 2) :
    entropyLaw (productBernoulli (blockBias p)) shiftMap =
        Measure.dirac (ENNReal.ofReal ((1 + 2 * bitEntropy p) / 3),
          ENNReal.ofReal ((2 + bitEntropy p) / 3)) ∧
      measureEntropy (productBernoulli (blockBias p)) shiftMap =
        (ENNReal.ofReal ((1 + 2 * bitEntropy p) / 3), ENNReal.ofReal ((2 + bitEntropy p) / 3)) ∧
      (essInf (fun x ↦ (localEntropy (productBernoulli (blockBias p)) shiftMap x).1)
            (productBernoulli (blockBias p)) = ENNReal.ofReal ((1 + 2 * bitEntropy p) / 3) ∧
        essSup (fun x ↦ (localEntropy (productBernoulli (blockBias p)) shiftMap x).1)
            (productBernoulli (blockBias p)) = ENNReal.ofReal ((1 + 2 * bitEntropy p) / 3)) ∧
      (essInf (fun x ↦ (localEntropy (productBernoulli (blockBias p)) shiftMap x).2)
            (productBernoulli (blockBias p)) = ENNReal.ofReal ((2 + bitEntropy p) / 3) ∧
        essSup (fun x ↦ (localEntropy (productBernoulli (blockBias p)) shiftMap x).2)
            (productBernoulli (blockBias p)) = ENNReal.ofReal ((2 + bitEntropy p) / 3)) :=
  entropyStatistics_of_ae_eq (ae_localEntropy_blockBias hp0 hp)

/-- Example 5.2: the measure `μ₂` (roles of `1/2` and `p` exchanged) has the same entropy law
`δ_{((1+2a)/3, (2+a)/3)}`, Feng–Huang entropies and essential bounds as `μ₁`.
Blueprint node `meas:examples`. -/
theorem entropyLaw_blockBiasSwap {p : I} (hp0 : 0 < (p : ℝ)) (hp : (p : ℝ) < 1 / 2) :
    entropyLaw (productBernoulli (blockBiasSwap p)) shiftMap =
        Measure.dirac (ENNReal.ofReal ((1 + 2 * bitEntropy p) / 3),
          ENNReal.ofReal ((2 + bitEntropy p) / 3)) ∧
      measureEntropy (productBernoulli (blockBiasSwap p)) shiftMap =
        (ENNReal.ofReal ((1 + 2 * bitEntropy p) / 3), ENNReal.ofReal ((2 + bitEntropy p) / 3)) ∧
      (essInf (fun x ↦ (localEntropy (productBernoulli (blockBiasSwap p)) shiftMap x).1)
            (productBernoulli (blockBiasSwap p)) = ENNReal.ofReal ((1 + 2 * bitEntropy p) / 3) ∧
        essSup (fun x ↦ (localEntropy (productBernoulli (blockBiasSwap p)) shiftMap x).1)
            (productBernoulli (blockBiasSwap p)) = ENNReal.ofReal ((1 + 2 * bitEntropy p) / 3)) ∧
      (essInf (fun x ↦ (localEntropy (productBernoulli (blockBiasSwap p)) shiftMap x).2)
            (productBernoulli (blockBiasSwap p)) = ENNReal.ofReal ((2 + bitEntropy p) / 3) ∧
        essSup (fun x ↦ (localEntropy (productBernoulli (blockBiasSwap p)) shiftMap x).2)
            (productBernoulli (blockBiasSwap p)) = ENNReal.ofReal ((2 + bitEntropy p) / 3)) :=
  entropyStatistics_of_ae_eq (ae_localEntropy_blockBiasSwap hp0 hp)

/-- Example 5.1 (concrete case): the information rates of `μ₁` are `H̲ = (1+2a)/3` and
`H̄ = (2+a)/3` (no law of large numbers is needed). Blueprint node `meas:examples`. -/
theorem informationRate_blockBias {p : I} (hp0 : 0 < (p : ℝ)) (hp : (p : ℝ) < 1 / 2) :
    informationRate (productBernoulli (blockBias p)) shiftMap =
      (ENNReal.ofReal ((1 + 2 * bitEntropy p) / 3), ENNReal.ofReal ((2 + bitEntropy p) / 3)) := by
  rw [informationRate_productBernoulli fun i ↦ ⟨hp0.trans_le (blockBias_mem hp i).1,
    by linarith [(blockBias_mem hp i).2]⟩, (entropyAverages_blockBias p).1,
    (entropyAverages_blockBias p).2]

/-! ### Two-component mixtures -/

/-- The mixture `t ν₁ + (1 - t) ν₂` of two measures, `t ∈ [0, 1]`.
Blueprint node `meas:examples`. -/
noncomputable def segmentMixture (t : I) (ν₁ ν₂ : Measure (ℕ → Bool)) : Measure (ℕ → Bool) :=
  ENNReal.ofReal t • ν₁ + ENNReal.ofReal (1 - t) • ν₂

section mixture

variable (t : I) (ν₁ ν₂ : Measure (ℕ → Bool))

/-- A mixture of probability measures is a probability measure. -/
instance [IsProbabilityMeasure ν₁] [IsProbabilityMeasure ν₂] :
    IsProbabilityMeasure (segmentMixture t ν₁ ν₂) :=
  ⟨by
    simp only [segmentMixture, Measure.add_apply, Measure.smul_apply, measure_univ, smul_eq_mul,
      mul_one]
    rw [← ENNReal.ofReal_add t.2.1 (sub_nonneg.2 t.2.2)]
    simp⟩

/-- Integrals against the mixture are the weighted sums of the integrals. -/
lemma lintegral_segmentMixture (g : (ℕ → Bool) → ℝ≥0∞) :
    ∫⁻ x, g x ∂segmentMixture t ν₁ ν₂ =
      ENNReal.ofReal t * ∫⁻ x, g x ∂ν₁ + ENNReal.ofReal (1 - t) * ∫⁻ x, g x ∂ν₂ := by
  rw [segmentMixture, lintegral_add_measure, lintegral_smul_measure, lintegral_smul_measure,
    smul_eq_mul, smul_eq_mul]

/-- The mixture dominates `t ν₁`. -/
lemma le_segmentMixture_left (s : Set (ℕ → Bool)) :
    ENNReal.ofReal t * ν₁ s ≤ segmentMixture t ν₁ ν₂ s := by
  simp only [segmentMixture, Measure.add_apply, Measure.smul_apply, smul_eq_mul]
  exact le_self_add

/-- The mixture dominates `(1 - t) ν₂`. -/
lemma le_segmentMixture_right (s : Set (ℕ → Bool)) :
    ENNReal.ofReal (1 - t) * ν₂ s ≤ segmentMixture t ν₁ ν₂ s := by
  simp only [segmentMixture, Measure.add_apply, Measure.smul_apply, smul_eq_mul]
  exact le_add_self

/-- If a component carries a.e. the local entropies `c` and has positive weight `w` in `μ`
(`w ν ≤ μ`), then `w ν`-a.e. the local entropies of `μ` are `c`. -/
private lemma ae_smul_localEntropy {μ ν : Measure (ℕ → Bool)} [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] {w : ℝ≥0∞} (hle : ∀ s, w * ν s ≤ μ s) {c : ℝ≥0∞ × ℝ≥0∞}
    (h : ∀ᵐ x ∂ν, localEntropy ν shiftMap x = c) :
    ∀ᵐ x ∂(w • ν), localEntropy μ shiftMap x = c := by
  by_cases hw : w = 0
  · simp [hw]
  rw [Measure.ae_ennreal_smul_measure_iff hw]
  have hac : ν ≪ μ := fun s hs ↦ by
    have := hle s
    rw [hs, nonpos_iff_eq_zero] at this
    exact (mul_eq_zero.1 this).resolve_left hw
  filter_upwards [ae_localEntropy_eq_of_absolutelyContinuous continuous_shiftMap_cantor hac, h]
    with x h1 h2
  rw [← h1, h2]

/-- Proposition 6.3 for two components: if both components have a.e. the local entropies `c`,
so has every mixture `t ν₁ + (1 - t) ν₂` (no singularity is needed). -/
lemma ae_localEntropy_segmentMixture [IsProbabilityMeasure ν₁] [IsProbabilityMeasure ν₂]
    {c : ℝ≥0∞ × ℝ≥0∞} (h₁ : ∀ᵐ x ∂ν₁, localEntropy ν₁ shiftMap x = c)
    (h₂ : ∀ᵐ x ∂ν₂, localEntropy ν₂ shiftMap x = c) :
    ∀ᵐ x ∂segmentMixture t ν₁ ν₂, localEntropy (segmentMixture t ν₁ ν₂) shiftMap x = c := by
  rw [segmentMixture, ae_add_measure_iff]
  exact ⟨ae_smul_localEntropy (le_segmentMixture_left t ν₁ ν₂) h₁,
    ae_smul_localEntropy (le_segmentMixture_right t ν₁ ν₂) h₂⟩

/-- Every cylinder of the mixture has positive mass if this holds for both components. -/
lemma segmentMixture_cylinder_ne_zero {ν₁ ν₂ : Measure (ℕ → Bool)} (n : ℕ)
    (h₁ : ∀ x, ν₁ (PiNat.cylinder x n) ≠ 0) (h₂ : ∀ x, ν₂ (PiNat.cylinder x n) ≠ 0)
    (x : ℕ → Bool) : segmentMixture t ν₁ ν₂ (PiNat.cylinder x n) ≠ 0 := by
  intro h
  simp only [segmentMixture, Measure.add_apply, Measure.smul_apply, smul_eq_mul, add_eq_zero,
    mul_eq_zero, ENNReal.ofReal_eq_zero, h₁ x, h₂ x, or_false] at h
  linarith [h.1, h.2]

/-- One component of the upper bound: if `w ν ≤ μ` with `w ∈ [0, 1]` and
`∫ -log₂ ν[x↾n] dν = S`, then `w ∫ -log₂ μ[x↾n] dν ≤ w S - w log₂ w`. -/
private lemma lintegral_infoBits_component_le {μ ν : Measure (ℕ → Bool)} [IsProbabilityMeasure ν]
    {w : ℝ} (hw0 : 0 ≤ w) (hw1 : w ≤ 1) (hle : ∀ s, ENNReal.ofReal w * ν s ≤ μ s) {S : ℝ}
    (hS : 0 ≤ S) (n : ℕ)
    (hν : ∫⁻ x, infoBits (ν (PiNat.cylinder x n)) ∂ν = ENNReal.ofReal S) :
    ENNReal.ofReal w * ∫⁻ x, infoBits (μ (PiNat.cylinder x n)) ∂ν ≤
      ENNReal.ofReal (w * S - w * Real.logb 2 w) := by
  rcases hw0.eq_or_lt with rfl | hw
  · simp
  have hc0 : ENNReal.ofReal w ≠ 0 := by simpa using hw
  have hlog : Real.logb 2 w ≤ 0 := Real.logb_nonpos one_lt_two hw0 hw1
  have hK : ∫⁻ x, infoBits (μ (PiNat.cylinder x n)) ∂ν ≤
      ENNReal.ofReal (S + -Real.logb 2 w) := by
    calc ∫⁻ x, infoBits (μ (PiNat.cylinder x n)) ∂ν
        ≤ ∫⁻ x, (infoBits (ν (PiNat.cylinder x n)) + ENNReal.ofReal (-Real.logb 2 w)) ∂ν := by
          refine lintegral_mono fun x ↦ (infoBits_antitone (hle _)).trans ?_
          refine (infoBits_mul_le hc0 ENNReal.ofReal_ne_top _).trans ?_
          rw [ENNReal.toReal_ofReal hw0, abs_of_nonpos hlog]
      _ = ENNReal.ofReal (S + -Real.logb 2 w) := by
          rw [lintegral_add_right _ measurable_const, lintegral_const, measure_univ, mul_one, hν,
            ← ENNReal.ofReal_add hS (by linarith)]
  calc ENNReal.ofReal w * ∫⁻ x, infoBits (μ (PiNat.cylinder x n)) ∂ν
      ≤ ENNReal.ofReal w * ENNReal.ofReal (S + -Real.logb 2 w) := by gcongr
    _ = ENNReal.ofReal (w * S - w * Real.logb 2 w) := by
        rw [← ENNReal.ofReal_mul hw0]; congr 1; ring

/-- `-t log₂ t - (1 - t) log₂ (1 - t) = H(t)`. -/
private lemma bitEntropy_eq_neg_logb (t : ℝ) :
    bitEntropy t = -(t * Real.logb 2 t) - (1 - t) * Real.logb 2 (1 - t) := by
  simp only [bitEntropy, Real.binEntropy, Real.logb, Real.log_inv]
  ring

/-- Bounds on the mean information of a mixture: if `∫ -log₂ ν_j[x↾n] dν_j = S_j` and all
cylinders of both components have positive mass, then
`t S₁ + (1 - t) S₂ ≤ ∫ -log₂ μ_t[x↾n] dμ_t ≤ t S₁ + (1 - t) S₂ + H(t)`. The lower bound is
Gibbs' inequality on each component, the upper bound uses `μ_t ≥ t ν₁` and `μ_t ≥ (1 - t) ν₂`.
Blueprint node `meas:examples`. -/
theorem lintegral_infoBits_segmentMixture_bounds {ν₁ ν₂ : Measure (ℕ → Bool)}
    [IsProbabilityMeasure ν₁] [IsProbabilityMeasure ν₂] (n : ℕ)
    (h₁ : ∀ x, ν₁ (PiNat.cylinder x n) ≠ 0) (h₂ : ∀ x, ν₂ (PiNat.cylinder x n) ≠ 0)
    {S₁ S₂ : ℝ} (hS₁ : 0 ≤ S₁) (hS₂ : 0 ≤ S₂)
    (hI₁ : ∫⁻ x, infoBits (ν₁ (PiNat.cylinder x n)) ∂ν₁ = ENNReal.ofReal S₁)
    (hI₂ : ∫⁻ x, infoBits (ν₂ (PiNat.cylinder x n)) ∂ν₂ = ENNReal.ofReal S₂) :
    ENNReal.ofReal (t * S₁ + (1 - t) * S₂) ≤
        ∫⁻ x, infoBits (segmentMixture t ν₁ ν₂ (PiNat.cylinder x n)) ∂segmentMixture t ν₁ ν₂ ∧
      ∫⁻ x, infoBits (segmentMixture t ν₁ ν₂ (PiNat.cylinder x n)) ∂segmentMixture t ν₁ ν₂ ≤
        ENNReal.ofReal (t * S₁ + (1 - t) * S₂ + bitEntropy t) := by
  have ht0 : (0 : ℝ) ≤ t := t.2.1
  have ht1 : (0 : ℝ) ≤ 1 - t := sub_nonneg.2 t.2.2
  have hpos := segmentMixture_cylinder_ne_zero t n h₁ h₂
  rw [lintegral_segmentMixture]
  constructor
  · rw [ENNReal.ofReal_add (mul_nonneg ht0 hS₁) (mul_nonneg ht1 hS₂),
      ENNReal.ofReal_mul ht0, ENNReal.ofReal_mul ht1, ← hI₁, ← hI₂]
    exact add_le_add
      (mul_le_mul_of_nonneg_left (lintegral_infoBits_cylinder_le _ _ n h₁ hpos) (zero_le))
      (mul_le_mul_of_nonneg_left (lintegral_infoBits_cylinder_le _ _ n h₂ hpos) (zero_le))
  · have e₁ := lintegral_infoBits_component_le ht0 t.2.2 (le_segmentMixture_left t ν₁ ν₂)
      hS₁ n hI₁
    have e₂ := lintegral_infoBits_component_le ht1 (by linarith [t.2.1])
      (le_segmentMixture_right t ν₁ ν₂) hS₂ n hI₂
    have n₁ : 0 ≤ (t : ℝ) * S₁ - t * Real.logb 2 t := by
      have := mul_nonpos_of_nonneg_of_nonpos ht0 (Real.logb_nonpos one_lt_two ht0 t.2.2)
      nlinarith [mul_nonneg ht0 hS₁]
    have n₂ : 0 ≤ (1 - (t : ℝ)) * S₂ - (1 - t) * Real.logb 2 (1 - t) := by
      have := mul_nonpos_of_nonneg_of_nonpos ht1
        (Real.logb_nonpos one_lt_two ht1 (by linarith [t.2.1]))
      nlinarith [mul_nonneg ht1 hS₂]
    calc _ ≤ ENNReal.ofReal (t * S₁ - t * Real.logb 2 t) +
          ENNReal.ofReal ((1 - t) * S₂ - (1 - t) * Real.logb 2 (1 - t)) := add_le_add e₁ e₂
      _ = ENNReal.ofReal (t * S₁ + (1 - t) * S₂ + bitEntropy t) := by
        rw [← ENNReal.ofReal_add n₁ n₂, bitEntropy_eq_neg_logb]
        congr 1
        ring

/-- The information rates of a mixture `t ν₁ + (1 - t) ν₂` are the lower and upper limits of
`(t S₁(n) + (1 - t) S₂(n))/n`, where `S_j(n) = ∫ -log₂ ν_j[x↾n] dν_j`: the mixture changes the
mean information by at most `H(t) ≤ 1` bit. Blueprint node `meas:examples`. -/
theorem informationRate_segmentMixture {ν₁ ν₂ : Measure (ℕ → Bool)}
    [IsProbabilityMeasure ν₁] [IsProbabilityMeasure ν₂]
    (h₁ : ∀ x n, ν₁ (PiNat.cylinder x n) ≠ 0) (h₂ : ∀ x n, ν₂ (PiNat.cylinder x n) ≠ 0)
    {S₁ S₂ : ℕ → ℝ} (hS₁ : ∀ n, 0 ≤ S₁ n) (hS₂ : ∀ n, 0 ≤ S₂ n)
    (hI₁ : ∀ n, ∫⁻ x, infoBits (ν₁ (PiNat.cylinder x n)) ∂ν₁ = ENNReal.ofReal (S₁ n))
    (hI₂ : ∀ n, ∫⁻ x, infoBits (ν₂ (PiNat.cylinder x n)) ∂ν₂ = ENNReal.ofReal (S₂ n)) :
    informationRate (segmentMixture t ν₁ ν₂) shiftMap =
      (liminf (fun n : ℕ ↦ ENNReal.ofReal ((t * S₁ n + (1 - t) * S₂ n) / n)) atTop,
        limsup (fun n : ℕ ↦ ENNReal.ofReal ((t * S₁ n + (1 - t) * S₂ n) / n)) atTop) := by
  set μ := segmentMixture t ν₁ ν₂
  set J : ℕ → ℝ≥0∞ := fun n ↦ ∫⁻ x, infoBits (μ (PiNat.cylinder x n)) ∂μ with hJ
  have hb := fun n ↦ lintegral_infoBits_segmentMixture_bounds t n (h₁ · n) (h₂ · n)
    (hS₁ n) (hS₂ n) (hI₁ n) (hI₂ n)
  have hfin : ∀ n, J n ≠ ⊤ := fun n ↦ ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hb n).2
  have hH0 : 0 ≤ bitEntropy t := bitEntropy_nonneg t
  have hlo : ∀ n, t * S₁ n + (1 - t) * S₂ n ≤ (J n).toReal := fun n ↦
    (ENNReal.ofReal_le_iff_le_toReal (hfin n)).1 (hb n).1
  have hhi : ∀ n, (J n).toReal ≤ t * S₁ n + (1 - t) * S₂ n + bitEntropy t := fun n ↦
    ENNReal.toReal_le_of_le_ofReal (add_nonneg (add_nonneg
      (mul_nonneg t.2.1 (hS₁ n)) (mul_nonneg (sub_nonneg.2 t.2.2) (hS₂ n))) hH0) (hb n).2
  have h : (fun n : ℕ ↦ J n / n) =ᶠ[atTop] fun n ↦ ENNReal.ofReal ((J n).toReal / n) :=
    (eventually_ge_atTop 1).mono fun n hn ↦ by
      dsimp only
      rw [← ofReal_div_natCast hn, ENNReal.ofReal_toReal (hfin n)]
  have hd : Tendsto (fun n : ℕ ↦ (J n).toReal / n - (t * S₁ n + (1 - t) * S₂ n) / n) atTop
      (𝓝 0) := by
    refine squeeze_zero_norm' ?_ (tendsto_const_div_atTop_nhds_zero_nat (bitEntropy t))
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    rw [← sub_div, Real.norm_eq_abs, abs_div, abs_of_pos hn',
      abs_of_nonneg (sub_nonneg.2 (hlo n))]
    exact div_le_div_of_nonneg_right (by linarith [hhi n]) hn'.le
  rw [informationRate_shiftMap (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num)
    (fun _ _ ↦ cantorMetricSpace_dist_eq)]
  change (liminf (fun n : ℕ ↦ J n / n) atTop, limsup (fun n : ℕ ↦ J n / n) atTop) = _
  rw [liminf_congr h, limsup_congr h, (liminf_limsup_ofReal_congr hd).1,
    (liminf_limsup_ofReal_congr hd).2]

end mixture

/-! ### Examples 5.2 and 6.8 -/

/-- Example 6.8: the segment of anti-phase mixtures `μ_t = t μ₁ + (1 - t) μ₂`, `t ∈ [0, 1]`,
with `μ₁ = ⨂ Bernoulli(blockBias p)` and `μ₂ = ⨂ Bernoulli(blockBiasSwap p)`.
Blueprint node `meas:examples`. -/
noncomputable def antiPhaseSegment (p t : I) : Measure (ℕ → Bool) :=
  segmentMixture t (productBernoulli (blockBias p)) (productBernoulli (blockBiasSwap p))

instance (p t : I) : IsProbabilityMeasure (antiPhaseSegment p t) := by
  unfold antiPhaseSegment; infer_instance

/-- Example 5.2: the anti-phase mixture `μ = ½ (μ₁ + μ₂)`. Blueprint node `meas:examples`. -/
noncomputable def antiPhaseMixture (p : I) : Measure (ℕ → Bool) :=
  (2⁻¹ : ℝ≥0∞) • (productBernoulli (blockBias p) + productBernoulli (blockBiasSwap p))

/-- The anti-phase mixture is the midpoint `t = 1/2` of the segment. -/
lemma antiPhaseMixture_eq (p : I) : antiPhaseMixture p = antiPhaseSegment p halfBias := by
  rw [antiPhaseMixture, antiPhaseSegment, segmentMixture, coe_halfBias,
    show (1 : ℝ) - 2⁻¹ = 2⁻¹ by norm_num, ENNReal.ofReal_inv_of_pos two_pos,
    ENNReal.ofReal_ofNat, smul_add]

instance (p : I) : IsProbabilityMeasure (antiPhaseMixture p) := by
  rw [antiPhaseMixture_eq]; infer_instance

/-- Example 6.8: for every `t ∈ [0, 1]`, `μ_t`-a.e. the local entropies are
`((1+2a)/3, (2+a)/3)`. -/
lemma ae_localEntropy_antiPhaseSegment {p : I} (hp0 : 0 < (p : ℝ)) (hp : (p : ℝ) < 1 / 2)
    (t : I) :
    ∀ᵐ x ∂antiPhaseSegment p t, localEntropy (antiPhaseSegment p t) shiftMap x =
      (ENNReal.ofReal ((1 + 2 * bitEntropy p) / 3), ENNReal.ofReal ((2 + bitEntropy p) / 3)) :=
  ae_localEntropy_segmentMixture t _ _ (ae_localEntropy_blockBias hp0 hp)
    (ae_localEntropy_blockBiasSwap hp0 hp)

/-- Example 6.8 (via Proposition 6.3): for every `t ∈ [0, 1]` the entropy law of
`μ_t = t μ₁ + (1 - t) μ₂` is `Λ_{μ_t} = δ_{((1+2a)/3, (2+a)/3)}`; hence its Feng–Huang entropies
are `((1+2a)/3, (2+a)/3)` and the essential infimum and supremum of the lower (upper) local
entropy are `(1+2a)/3` (`(2+a)/3`). Blueprint node `meas:examples`. -/
theorem entropyLaw_antiPhaseSegment {p : I} (hp0 : 0 < (p : ℝ)) (hp : (p : ℝ) < 1 / 2)
    (t : I) :
    entropyLaw (antiPhaseSegment p t) shiftMap =
        Measure.dirac (ENNReal.ofReal ((1 + 2 * bitEntropy p) / 3),
          ENNReal.ofReal ((2 + bitEntropy p) / 3)) ∧
      measureEntropy (antiPhaseSegment p t) shiftMap =
        (ENNReal.ofReal ((1 + 2 * bitEntropy p) / 3), ENNReal.ofReal ((2 + bitEntropy p) / 3)) ∧
      (essInf (fun x ↦ (localEntropy (antiPhaseSegment p t) shiftMap x).1)
            (antiPhaseSegment p t) = ENNReal.ofReal ((1 + 2 * bitEntropy p) / 3) ∧
        essSup (fun x ↦ (localEntropy (antiPhaseSegment p t) shiftMap x).1)
            (antiPhaseSegment p t) = ENNReal.ofReal ((1 + 2 * bitEntropy p) / 3)) ∧
      (essInf (fun x ↦ (localEntropy (antiPhaseSegment p t) shiftMap x).2)
            (antiPhaseSegment p t) = ENNReal.ofReal ((2 + bitEntropy p) / 3) ∧
        essSup (fun x ↦ (localEntropy (antiPhaseSegment p t) shiftMap x).2)
            (antiPhaseSegment p t) = ENNReal.ofReal ((2 + bitEntropy p) / 3)) :=
  entropyStatistics_of_ae_eq (ae_localEntropy_antiPhaseSegment hp0 hp t)

/-- Positivity of the cylinders of a product Bernoulli measure with biases in `(0, 1)`. -/
private lemma productBernoulli_cylinder_ne_zero {β : ℕ → I}
    (hβ : ∀ i, 0 < (β i : ℝ) ∧ (β i : ℝ) < 1) (x : ℕ → Bool) (n : ℕ) :
    productBernoulli β (PiNat.cylinder x n) ≠ 0 := by
  rw [productBernoulli_cylinder, ne_eq, ENNReal.ofReal_eq_zero, not_le]
  exact Finset.prod_pos fun i _ ↦ bitMass_pos (hβ i).1 (hβ i).2 _

/-- Example 6.8: the normalized mean information of `μ_t` is affine in the density `f_n` of the
block pattern up to `O(1/n)`:
`(1/n) H_{μ_t}(ξ^n) = (1 - t) + t a + (2t - 1)(1 - a) f_n + O(1/n)`, which is the paper's
`(1 - t)(1 + a) + (2t - 1) A₁(n)` with `A₁(n) = a + (1 - a) f_n`. As a consequence the information
rates are `H̲_{μ_t} = (1+a)/2 - |2t-1|(1-a)/6` and `H̄_{μ_t} = (1+a)/2 + |2t-1|(1-a)/6`,
confirming the paper's formulas. The paper takes `p ∈ (0, 1/2)`; here `p ∈ (0, 1)` with no
further condition suffices. Blueprint node `meas:examples`. -/
theorem informationRate_antiPhaseSegment {p : I} (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (t : I) :
    informationRate (antiPhaseSegment p t) shiftMap =
      (ENNReal.ofReal ((1 + bitEntropy p) / 2 - |2 * (t : ℝ) - 1| * (1 - bitEntropy p) / 6),
        ENNReal.ofReal ((1 + bitEntropy p) / 2 +
          |2 * (t : ℝ) - 1| * (1 - bitEntropy p) / 6)) := by
  have hβ₁ : ∀ i, 0 < (blockBias p i : ℝ) ∧ (blockBias p i : ℝ) < 1 := fun i ↦ by
    unfold blockBias; split_ifs
    · rw [coe_halfBias]; norm_num
    · exact ⟨hp0, hp1⟩
  have hβ₂ : ∀ i, 0 < (blockBiasSwap p i : ℝ) ∧ (blockBiasSwap p i : ℝ) < 1 := fun i ↦ by
    unfold blockBiasSwap; split_ifs
    · exact ⟨hp0, hp1⟩
    · rw [coe_halfBias]; norm_num
  have hsum : ∀ (β : ℕ → I) (n : ℕ), 0 ≤ ∑ i ∈ Finset.range n, bitEntropy (β i) :=
    fun β n ↦ Finset.sum_nonneg fun i _ ↦ bitEntropy_nonneg _
  rw [antiPhaseSegment, informationRate_segmentMixture t
    (fun x n ↦ productBernoulli_cylinder_ne_zero hβ₁ x n)
    (fun x n ↦ productBernoulli_cylinder_ne_zero hβ₂ x n) (hsum _) (hsum _)
    (lintegral_infoBits_productBernoulli hβ₁) (lintegral_infoBits_productBernoulli hβ₂)]
  have h := liminf_limsup_ofReal_of_blockFrequency
    (u := fun n : ℕ ↦ (t * ∑ i ∈ Finset.range n, bitEntropy (blockBias p i) +
      (1 - t) * ∑ i ∈ Finset.range n, bitEntropy (blockBiasSwap p i)) / n)
    (A := (1 - t) + t * bitEntropy p) (B := (2 * t - 1) * (1 - bitEntropy p)) (c := 0)
    fun n hn ↦ by
      have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
      have e : (t * ∑ i ∈ Finset.range n, bitEntropy (blockBias p i) +
          (1 - t) * ∑ i ∈ Finset.range n, bitEntropy (blockBiasSwap p i)) / n -
          ((1 - t) + t * bitEntropy p + (2 * t - 1) * (1 - bitEntropy p) *
            blockFrequency n) = 0 := by
        rw [sum_bitEntropy_blockBias, sum_bitEntropy_blockBiasSwap, blockFrequency]
        field_simp
        ring
      rw [e]; simp
  rw [abs_mul, abs_one_sub_bitEntropy] at h
  rw [h.1, h.2]
  congr 2 <;> ring

/-- Example 6.8: at the endpoints `t ∈ {0, 1}` the information interval `[H̲_{μ_t}, H̄_{μ_t}]`
equals the Feng–Huang interval `[(1+2a)/3, (2+a)/3]`. Blueprint node `meas:examples`. -/
theorem informationRate_antiPhaseSegment_of_endpoint {p : I} (hp0 : 0 < (p : ℝ))
    (hp : (p : ℝ) < 1 / 2) {t : I} (ht : (t : ℝ) = 0 ∨ (t : ℝ) = 1) :
    informationRate (antiPhaseSegment p t) shiftMap =
      measureEntropy (antiPhaseSegment p t) shiftMap := by
  rw [informationRate_antiPhaseSegment hp0 (by linarith) t,
    (entropyLaw_antiPhaseSegment hp0 hp t).2.1]
  have h1 : |2 * (t : ℝ) - 1| = 1 := by rcases ht with h | h <;> rw [h] <;> norm_num
  rw [h1]
  congr 2 <;> ring

/-- Example 5.2: the entropy law of the anti-phase mixture `μ = ½ (μ₁ + μ₂)` is
`δ_{((1+2a)/3, (2+a)/3)}`, so `h̲_μ = ess inf h̲_μ = ess sup h̲_μ = (1+2a)/3` and
`h̄_μ = ess inf h̄_μ = ess sup h̄_μ = (2+a)/3`. Proved without the singularity `μ₁ ⊥ μ₂`
(Proposition 6.3 / `entropyLaw_sum` suffices). Blueprint node `meas:examples`. -/
theorem entropyLaw_antiPhaseMixture {p : I} (hp0 : 0 < (p : ℝ)) (hp : (p : ℝ) < 1 / 2) :
    entropyLaw (antiPhaseMixture p) shiftMap =
        Measure.dirac (ENNReal.ofReal ((1 + 2 * bitEntropy p) / 3),
          ENNReal.ofReal ((2 + bitEntropy p) / 3)) ∧
      measureEntropy (antiPhaseMixture p) shiftMap =
        (ENNReal.ofReal ((1 + 2 * bitEntropy p) / 3), ENNReal.ofReal ((2 + bitEntropy p) / 3)) ∧
      (essInf (fun x ↦ (localEntropy (antiPhaseMixture p) shiftMap x).1)
            (antiPhaseMixture p) = ENNReal.ofReal ((1 + 2 * bitEntropy p) / 3) ∧
        essSup (fun x ↦ (localEntropy (antiPhaseMixture p) shiftMap x).1)
            (antiPhaseMixture p) = ENNReal.ofReal ((1 + 2 * bitEntropy p) / 3)) ∧
      (essInf (fun x ↦ (localEntropy (antiPhaseMixture p) shiftMap x).2)
            (antiPhaseMixture p) = ENNReal.ofReal ((2 + bitEntropy p) / 3) ∧
        essSup (fun x ↦ (localEntropy (antiPhaseMixture p) shiftMap x).2)
            (antiPhaseMixture p) = ENNReal.ofReal ((2 + bitEntropy p) / 3)) := by
  rw [antiPhaseMixture_eq]
  exact entropyLaw_antiPhaseSegment hp0 hp halfBias

/-- Example 5.2: the information rates of the anti-phase mixture are
`H̲_μ = H̄_μ = (1 + a)/2`. Blueprint node `meas:examples`. -/
theorem informationRate_antiPhaseMixture {p : I} (hp0 : 0 < (p : ℝ)) (hp : (p : ℝ) < 1 / 2) :
    informationRate (antiPhaseMixture p) shiftMap =
      (ENNReal.ofReal ((1 + bitEntropy p) / 2), ENNReal.ofReal ((1 + bitEntropy p) / 2)) := by
  rw [antiPhaseMixture_eq, informationRate_antiPhaseSegment hp0 (by linarith), coe_halfBias]
  norm_num

/-- Example 5.2: both Fatou inequalities are strict for the anti-phase mixture,
`h̲_μ < H̲_μ = H̄_μ < h̄_μ` (with `h̲_μ = (1+2a)/3`, `H̲_μ = H̄_μ = (1+a)/2`, `h̄_μ = (2+a)/3`,
`a = H(p) < 1`). Blueprint node `meas:examples`. -/
theorem antiPhaseMixture_strict {p : I} (hp0 : 0 < (p : ℝ)) (hp : (p : ℝ) < 1 / 2) :
    (measureEntropy (antiPhaseMixture p) shiftMap).1 <
        (informationRate (antiPhaseMixture p) shiftMap).1 ∧
      (informationRate (antiPhaseMixture p) shiftMap).1 =
        (informationRate (antiPhaseMixture p) shiftMap).2 ∧
      (informationRate (antiPhaseMixture p) shiftMap).2 <
        (measureEntropy (antiPhaseMixture p) shiftMap).2 := by
  have ha := bitEntropy_lt_one_of_lt_half hp
  have ha0 := bitEntropy_nonneg p
  rw [(entropyLaw_antiPhaseMixture hp0 hp).2.1, informationRate_antiPhaseMixture hp0 hp]
  refine ⟨?_, rfl, ?_⟩
  · exact (ENNReal.ofReal_lt_ofReal_iff (by linarith)).2 (by linarith)
  · exact (ENNReal.ofReal_lt_ofReal_iff (by linarith)).2 (by linarith)

end Kolmogorov.PointToSet
