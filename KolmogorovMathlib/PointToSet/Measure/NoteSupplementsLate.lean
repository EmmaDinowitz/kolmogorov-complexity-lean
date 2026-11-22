/-
Copyright (c) 2026 Emma Dinowitz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emma Dinowitz
-/
import KolmogorovMathlib.PointToSet.Measure.NoteSupplements
import KolmogorovMathlib.PointToSet.Measure.NoteSupplementsAux
import KolmogorovMathlib.PointToSet.Measure.ShiftAntiPhase

/-!
# Supplements to the note: §4.4, Example 5.2 (algorithmic sentence), Example 6.8 / §6.2

Formal statements of sentences of E. Dinowitz, *Entropy of non-invariant measures and orbit
complexity of random points*, that need the measures of `ShiftAntiPhase.lean` and
`ShiftBernoulli.lean` (binary shift, Cantor metric; `a = H(p)`, `0 < p < 1/2`).

* §4.4, "every inequality can be strict" and "`ess sup h̲_μ` and `H̄_μ` are not comparable":
  `noteSupp_entropy_chain_strict` (for the measures of Examples 5.1, 5.2, 5.3) and
  `noteSupp_exists_entropy_chain_strict` (existential form).
* Example 5.2, "the expected complexity rate `(1/n) ∫ K(x↾n) dμ` converges to `(1+a)/2`":
  `noteSupp_expectedOrbitComplexity_rate_antiPhaseMixture` (Bowen-ball form, every admissible
  oracle).
* Example 5.2, "every `μ`-random point is `μ₁`- or `μ₂`-random and `K(x↾n)/n` oscillates between
  `(1+2a)/3` and `(2+a)/3`": `noteSupp_randomPoints_antiPhaseSegment_subset` (first half, every
  oracle); `noteSupp_orbitComplexities_fst_antiPhaseSegment_le` (`K̲^A ≤ (1+2a)/3`, every
  admissible oracle); `noteSupp_exists_cone_orbitComplexities_antiPhaseSegment` and
  `noteSupp_exists_cone_wordComplexity_antiPhaseSegment` (the full sentence on a cone of
  oracles); `noteSupp_orbitComplexities_antiPhaseSegment_of_mem_randomPoints` (reduction to the
  components for an oracle admissible for both). Stated for every `μ_t`; Example 5.2 is
  `t = 1/2` (`antiPhaseMixture_eq`). Not proved: the sentence for every admissible oracle, which
  needs `Φ_{μ_i}(x)` at every `μ_i`-random point (an effective strong law for the
  non-identically distributed product `μ_i`).
* Example 6.8 / §6.2, "the rates in probability are `(1+2a)/3` and `(2+a)/3` and do not depend on
  `t`": `noteSupp_probRates_antiPhaseSegment` (every scale) and
  `noteSupp_iSup_probRates_antiPhaseSegment` (supremum over scales), for `0 < t < 1`.

Blueprint nodes `meas:chain`, `meas:examples`, `meas:probability-rate`.
-/

namespace Kolmogorov.PointToSet

open Filter Set MeasureTheory
open scoped Topology ENNReal unitInterval Computability

attribute [local instance] cantorMetricSpace

/-! ### Example 6.8 / §6.2: rates in probability of the anti-phase segment -/

section rates

/-- If a property holds eventually along the values `u (φ j)` with `φ j → ∞`, it holds
infinitely often along `n ↦ u (n + q)`. -/
lemma noteSupp_frequently_shift {u : ℕ → ℝ} {φ : ℕ → ℕ} (hφ : Tendsto φ atTop atTop) (q : ℕ)
    {P : ℝ → Prop} (h : ∀ᶠ j in atTop, P (u (φ j))) : ∃ᶠ n in atTop, P (u (n + q)) := by
  refine frequently_atTop.2 fun N ↦ ?_
  obtain ⟨j, hj, hjN⟩ := (h.and (hφ.eventually_ge_atTop (N + q))).exists
  exact ⟨φ j - q, by omega, by rwa [Nat.sub_add_cancel (by omega)]⟩

variable {p : I}

/-- The Cesàro average of `H(β_i)` for `μ₁` in terms of the density of the block pattern. -/
lemma noteSupp_entropyAverage_blockBias {m : ℕ} (hm : 1 ≤ m) :
    entropyAverage (blockBias p) m = bitEntropy p + (1 - bitEntropy p) * blockFrequency m :=
  entropyAverage_blockBias p hm

/-- The Cesàro average of `H(β_i)` for `μ₂` in terms of the density of the block pattern. -/
lemma noteSupp_entropyAverage_blockBiasSwap {m : ℕ} (hm : 1 ≤ m) :
    entropyAverage (blockBiasSwap p) m = 1 - (1 - bitEntropy p) * blockFrequency m := by
  rw [entropyAverage_blockBiasSwap p hm]
  ring

/-- `antiPhaseSegment p t` as a weighted sum of its two product components. -/
lemma noteSupp_antiPhaseSegment_eq (t : I) :
    antiPhaseSegment p t = ENNReal.ofReal t • productBernoulli (blockBias p) +
      ENNReal.ofReal (1 - t) • productBernoulli (blockBiasSwap p) := rfl

/-- The function `n, x ↦ -(1/n) log₂ μ_t(B_n(x, σ, 2^{-q}))` of §6.2 for `μ_t`. -/
noncomputable def noteSupp_segRate (p t : I) (q : ℕ) : ℕ → (ℕ → Bool) → ℝ≥0∞ :=
  fun n x ↦ localEntropyRate (antiPhaseSegment p t) shiftMap x n (dyadicRadius q)

/-- Both components of `μ_t` are tracked: `μ₁`-a.s. `f_n` follows the averages of `μ₁` and
`μ₂`-a.s. those of `μ₂` (`0 < t < 1`). -/
lemma noteSupp_tracks_antiPhaseSegment (hp0 : 0 < (p : ℝ)) (hp : (p : ℝ) < 1 / 2) {t : I}
    (ht0 : 0 < (t : ℝ)) (ht1 : (t : ℝ) < 1) (q : ℕ) :
    (∀ᵐ x ∂productBernoulli (blockBias p), noteSupp_Tracks (noteSupp_segRate p t q)
        (fun n ↦ entropyAverage (blockBias p) (n + q)) x) ∧
      ∀ᵐ x ∂productBernoulli (blockBiasSwap p), noteSupp_Tracks (noteSupp_segRate p t q)
        (fun n ↦ entropyAverage (blockBiasSwap p) (n + q)) x := by
  have h₁ := noteSupp_tracks_productMixture (β₁ := blockBias p) (β₂ := blockBiasSwap p) hp0
    (blockBias_mem hp) (blockBiasSwap_mem hp) (t := t) (s := 1 - t) ht0 (by linarith)
    (by linarith) q
  have h₂ := noteSupp_tracks_productMixture (β₁ := blockBiasSwap p) (β₂ := blockBias p) hp0
    (blockBiasSwap_mem hp) (blockBias_mem hp) (t := 1 - t) (s := t) (by linarith)
    (by linarith) (by linarith) q
  have e : ENNReal.ofReal (1 - (t : ℝ)) • productBernoulli (blockBiasSwap p) +
      ENNReal.ofReal t • productBernoulli (blockBias p) = antiPhaseSegment p t := by
    rw [noteSupp_antiPhaseSegment_eq, add_comm]
  rw [e] at h₂
  rw [← noteSupp_antiPhaseSegment_eq] at h₁
  exact ⟨h₁, h₂⟩

/-- Example 6.8 and §6.2, "in Example 6.8 with `0 < t < 1`, `f_n` concentrates near `A₁(n)` with
probability `t` and near `1 + a - A₁(n)` with probability `1 - t`, so the rates in probability
are `(1+2a)/3` and `(2+a)/3` and do not depend on `t`": at every dyadic scale `2^{-q}` the lower
and upper rates in probability of `f_n(x) = -(1/n) log₂ μ_t(B_n(x, σ, 2^{-q}))` under `μ_t` are
`(1+2a)/3` and `(2+a)/3` (`a = H(p)`, `p ∈ (0, 1/2)`, `0 < t < 1`), whereas the information rates
`informationRate_antiPhaseSegment` depend on `t`. Blueprint node `meas:probability-rate`. -/
theorem noteSupp_probRates_antiPhaseSegment (hp0 : 0 < (p : ℝ)) (hp : (p : ℝ) < 1 / 2)
    {t : I} (ht0 : 0 < (t : ℝ)) (ht1 : (t : ℝ) < 1) (q : ℕ) :
    lowerProbRate (antiPhaseSegment p t)
        (fun n x ↦ localEntropyRate (antiPhaseSegment p t) shiftMap x n (dyadicRadius q)) =
      ENNReal.ofReal ((1 + 2 * bitEntropy p) / 3) ∧
    upperProbRate (antiPhaseSegment p t)
        (fun n x ↦ localEntropyRate (antiPhaseSegment p t) shiftMap x n (dyadicRadius q)) =
      ENNReal.ofReal ((2 + bitEntropy p) / 3) := by
  obtain ⟨h₁, h₂⟩ := noteSupp_tracks_antiPhaseSegment hp0 hp ht0 ht1 q
  have hg : ∀ n, Measurable (noteSupp_segRate p t q n) := fun n ↦
    measurable_localEntropyRate _ continuous_shiftMap_cantor n _
  have hw₁ : ENNReal.ofReal (t : ℝ) ≠ 0 := by
    rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]; exact ht0
  set a := bitEntropy (p : ℝ) with ha
  have ha1 : a < 1 := bitEntropy_lt_one (by intro h; rw [h] at hp; norm_num at hp)
  have ha0 : 0 ≤ a := bitEntropy_nonneg p
  have hf := fun m (hm : 1 ≤ m) ↦ blockFrequency_bounds hm
  -- the averages at the shifted index, in terms of the density `f`
  have hA₁ : ∀ n, 1 ≤ n + q → entropyAverage (blockBias p) (n + q) =
      a + (1 - a) * blockFrequency (n + q) := fun n h ↦ noteSupp_entropyAverage_blockBias h
  have hA₂ : ∀ n, 1 ≤ n + q → entropyAverage (blockBiasSwap p) (n + q) =
      1 - (1 - a) * blockFrequency (n + q) := fun n h ↦ noteSupp_entropyAverage_blockBiasSwap h
  have hsmall : ∀ ε > 0, ∀ᶠ n : ℕ in atTop, (1 - a) / (3 * ((n + q : ℕ) : ℝ)) < ε := by
    intro ε hε
    have h := tendsto_const_div_atTop_nhds_zero_nat ((1 - a) / 3)
    filter_upwards [h.eventually (gt_mem_nhds hε), eventually_ge_atTop 1] with n hn hn1
    have hnq : (n : ℝ) ≤ ((n + q : ℕ) : ℝ) := by exact_mod_cast Nat.le_add_right n q
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
    calc (1 - a) / (3 * ((n + q : ℕ) : ℝ)) ≤ (1 - a) / 3 / n := by
          rw [div_div]
          exact div_le_div_of_nonneg_left (by linarith) (by positivity) (by linarith)
      _ < ε := hn
  have : IsFiniteMeasure (ENNReal.ofReal (t : ℝ) • productBernoulli (blockBias p) +
      ENNReal.ofReal (1 - (t : ℝ)) • productBernoulli (blockBiasSwap p)) := by
    rw [← noteSupp_antiPhaseSegment_eq]; infer_instance
  constructor
  · refine noteSupp_lowerProbRate_eq_of_tracks (ν₁ := productBernoulli (blockBias p))
      (ν₂ := productBernoulli (blockBiasSwap p)) (w₁ := ENNReal.ofReal t)
      (w₂ := ENNReal.ofReal (1 - t)) (g := noteSupp_segRate p t q) hg h₁ h₂ (fun ε hε ↦ ?_)
      (Or.inl ⟨hw₁, ?_⟩)
    · filter_upwards [hsmall ε hε, eventually_ge_atTop 1] with n hn hn1
      have hm : 1 ≤ n + q := by omega
      obtain ⟨hf1, hf2⟩ := hf _ hm
      rw [hA₁ n hm, hA₂ n hm]
      have hpos : 0 < ((n + q : ℕ) : ℝ) := by exact_mod_cast hm
      have : (1 - a) * (1 / (3 * ((n + q : ℕ) : ℝ))) = (1 - a) / (3 * ((n + q : ℕ) : ℝ)) := by
        ring
      constructor <;> nlinarith
    · intro ε hε
      refine noteSupp_frequently_shift (φ := fun j ↦ 4 ^ j)
        (tendsto_atTop_mono (fun j ↦ (Nat.lt_pow_self (by norm_num)).le) tendsto_id) q
        (u := fun m ↦ entropyAverage (blockBias p) m) (P := fun y ↦ y < (1 + 2 * a) / 3 + ε)
        (Eventually.of_forall fun j ↦ ?_)
      rw [noteSupp_entropyAverage_blockBias (Nat.one_le_pow _ _ (by norm_num)),
        blockFrequency_pow]
      have : (0 : ℝ) < 1 / (3 * 4 ^ j) := by positivity
      nlinarith
  · refine noteSupp_upperProbRate_eq_of_tracks (ν₁ := productBernoulli (blockBias p))
      (ν₂ := productBernoulli (blockBiasSwap p)) (w₁ := ENNReal.ofReal t)
      (w₂ := ENNReal.ofReal (1 - t)) (g := noteSupp_segRate p t q) hg h₁ h₂ (fun ε hε ↦ ?_)
      (Or.inl ⟨hw₁, ?_⟩)
    · filter_upwards [hsmall ε hε, eventually_ge_atTop 1] with n hn hn1
      have hm : 1 ≤ n + q := by omega
      obtain ⟨hf1, hf2⟩ := hf _ hm
      rw [hA₁ n hm, hA₂ n hm]
      have hpos : 0 < ((n + q : ℕ) : ℝ) := by exact_mod_cast hm
      have : (1 - a) * (1 / (3 * ((n + q : ℕ) : ℝ))) = (1 - a) / (3 * ((n + q : ℕ) : ℝ)) := by
        ring
      constructor <;> nlinarith
    · intro ε hε
      refine noteSupp_frequently_shift (φ := fun j ↦ 2 * 4 ^ j)
        (tendsto_atTop_mono (fun j ↦ (Nat.lt_pow_self (by norm_num)).le.trans
          (Nat.le_mul_of_pos_left _ two_pos)) tendsto_id) q
        (u := fun m ↦ entropyAverage (blockBias p) m) (P := fun y ↦ (2 + a) / 3 - ε < y) ?_
      have hlim : Tendsto (fun j : ℕ ↦ a + (1 - a) * blockFrequency (2 * 4 ^ j)) atTop
          (𝓝 (a + (1 - a) * (2 / 3))) :=
        tendsto_const_nhds.add (tendsto_blockFrequency_two_mul_pow.const_mul _)
      have hlt : (2 + a) / 3 - ε < a + (1 - a) * (2 / 3) := by linarith
      filter_upwards [hlim.eventually (lt_mem_nhds hlt)] with j hj
      rw [noteSupp_entropyAverage_blockBias (Nat.one_le_iff_ne_zero.2 (by positivity))]
      exact hj

/-- Example 6.8 and §6.2, the rates in probability as `ε → 0`:
`sup_q H̲^p_{μ_t}(σ, 2^{-q}) = (1+2a)/3` and `sup_q H̄^p_{μ_t}(σ, 2^{-q}) = (2+a)/3` for
`0 < t < 1`, independently of `t`. Blueprint node `meas:probability-rate`. -/
theorem noteSupp_iSup_probRates_antiPhaseSegment (hp0 : 0 < (p : ℝ)) (hp : (p : ℝ) < 1 / 2)
    {t : I} (ht0 : 0 < (t : ℝ)) (ht1 : (t : ℝ) < 1) :
    ⨆ q : ℕ, lowerProbRate (antiPhaseSegment p t)
        (fun n x ↦ localEntropyRate (antiPhaseSegment p t) shiftMap x n (dyadicRadius q)) =
      ENNReal.ofReal ((1 + 2 * bitEntropy p) / 3) ∧
    ⨆ q : ℕ, upperProbRate (antiPhaseSegment p t)
        (fun n x ↦ localEntropyRate (antiPhaseSegment p t) shiftMap x n (dyadicRadius q)) =
      ENNReal.ofReal ((2 + bitEntropy p) / 3) := by
  simp only [fun q ↦ (noteSupp_probRates_antiPhaseSegment hp0 hp ht0 ht1 q).1,
    fun q ↦ (noteSupp_probRates_antiPhaseSegment hp0 hp ht0 ht1 q).2, iSup_const, and_self]

end rates

/-! ### §4.4: every inequality of the chain can be strict -/

section chain

open scoped NNReal

/-- The binary entropy in bits, real version, is nonnegative on `[0, 1]`. -/
lemma noteSupp_bitEntropy_nonneg {r : ℝ} (h0 : 0 ≤ r) (h1 : r ≤ 1) : 0 ≤ bitEntropy r :=
  div_nonneg (Real.binEntropy_nonneg h0 h1) (Real.log_nonneg one_le_two)

/-- The binary entropy in bits as `ofReal` of the real one. -/
lemma noteSupp_binEntropyBits_eq (r : ℝ) : binEntropyBits r = ENNReal.ofReal (bitEntropy r) :=
  rfl

/-- The mean of two binary entropies, as `ofReal` of the real mean. -/
lemma noteSupp_binEntropyBits_mean {r s : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (hs0 : 0 ≤ s)
    (hs1 : s ≤ 1) :
    (binEntropyBits r + binEntropyBits s) / 2 =
      ENNReal.ofReal ((bitEntropy r + bitEntropy s) / 2) := by
  have h₁ := noteSupp_bitEntropy_nonneg hr0 hr1
  have h₂ := noteSupp_bitEntropy_nonneg hs0 hs1
  rw [ENNReal.ofReal_div_of_pos two_pos, ENNReal.ofReal_add h₁ h₂, ENNReal.ofReal_ofNat]
  rfl

variable {p : I} {r s : ℝ≥0} (hr : r ≤ 1) (hs : s ≤ 1)

/-- §4.4, "every inequality can be strict (Section 5)" and "`ess sup h̲_μ` and `H̄_μ` are not
comparable in general: Example 5.2 has the first smaller and Example 5.3 the second", for the
concrete measures of Section 5 on the binary shift: with `μ₃ = ½(ν_r + ν_s)` (Example 5.3,
`H(r) < H(s)`), `μ₁ = ⨂ Bernoulli(blockBias p)` (Example 5.1) and `μ₂ = ½(μ₁ + μ₁')`
(Example 5.2, `0 < p < 1/2`), in the chain
`ess inf h̲ ≤ h̲(σ) ≤ H̲ ≤ H̄ ≤ h̄(σ) ≤ ess sup h̄`:
* `ess inf h̲_{μ₃} < h̲_{μ₃}(σ)`, `h̲_{μ₂}(σ) < H̲_{μ₂}`, `H̲_{μ₁} < H̄_{μ₁}`,
  `H̄_{μ₂} < h̄_{μ₂}(σ)`, `h̄_{μ₃}(σ) < ess sup h̄_{μ₃}`;
* `ess sup h̲_{μ₂} < H̄_{μ₂}` and `H̄_{μ₃} < ess sup h̲_{μ₃}`.
Blueprint node `meas:chain`. -/
theorem noteSupp_entropy_chain_strict (hp0 : 0 < (p : ℝ)) (hp : (p : ℝ) < 1 / 2)
    (hr0 : 0 < r) (hr1 : r < 1) (hs0 : 0 < s) (hs1 : s < 1)
    (hrs : binEntropyBits r < binEntropyBits s) :
    essInf (fun x ↦ (localEntropy (bernoulliMixture r hr s hs) shiftMap x).1)
        (bernoulliMixture r hr s hs) < (measureEntropy (bernoulliMixture r hr s hs) shiftMap).1 ∧
      (measureEntropy (antiPhaseMixture p) shiftMap).1 <
        (informationRate (antiPhaseMixture p) shiftMap).1 ∧
      (informationRate (productBernoulli (blockBias p)) shiftMap).1 <
        (informationRate (productBernoulli (blockBias p)) shiftMap).2 ∧
      (informationRate (antiPhaseMixture p) shiftMap).2 <
        (measureEntropy (antiPhaseMixture p) shiftMap).2 ∧
      (measureEntropy (bernoulliMixture r hr s hs) shiftMap).2 <
        essSup (fun x ↦ (localEntropy (bernoulliMixture r hr s hs) shiftMap x).2)
          (bernoulliMixture r hr s hs) ∧
      essSup (fun x ↦ (localEntropy (antiPhaseMixture p) shiftMap x).1) (antiPhaseMixture p) <
        (informationRate (antiPhaseMixture p) shiftMap).2 ∧
      (informationRate (bernoulliMixture r hr s hs) shiftMap).2 <
        essSup (fun x ↦ (localEntropy (bernoulliMixture r hr s hs) shiftMap x).1)
          (bernoulliMixture r hr s hs) := by
  have hb := essInf_essSup_bernoulliMixture r hr s hs hr0 hr1 hs0 hs1 hrs.le
  have hm := measureEntropy_bernoulliMixture r hr s hs hr0 hr1 hs0 hs1
  have hi := informationRate_bernoulliMixture r hr s hs hr0 hr1 hs0 hs1
  have hr₁ : (r : ℝ) ≤ 1 := by exact_mod_cast hr
  have hs₁ : (s : ℝ) ≤ 1 := by exact_mod_cast hs
  have hmean := noteSupp_binEntropyBits_mean (NNReal.coe_nonneg r) hr₁ (NNReal.coe_nonneg s) hs₁
  have hr' := noteSupp_bitEntropy_nonneg (NNReal.coe_nonneg r) hr₁
  have hs' := noteSupp_bitEntropy_nonneg (NNReal.coe_nonneg s) hs₁
  have hrs' : bitEntropy (r : ℝ) < bitEntropy (s : ℝ) := by
    rw [binEntropyBits, binEntropyBits, ENNReal.ofReal_lt_ofReal_iff'] at hrs
    exact hrs.1
  have hlt₁ : binEntropyBits r < (binEntropyBits r + binEntropyBits s) / 2 := by
    rw [hmean, binEntropyBits, ENNReal.ofReal_lt_ofReal_iff']
    refine ⟨?_, ?_⟩
    · change bitEntropy (r : ℝ) < (bitEntropy (r : ℝ) + bitEntropy (s : ℝ)) / 2
      linarith
    · linarith
  have hlt₂ : (binEntropyBits r + binEntropyBits s) / 2 < binEntropyBits s := by
    rw [hmean, binEntropyBits, ENNReal.ofReal_lt_ofReal_iff']
    refine ⟨?_, ?_⟩
    · change (bitEntropy (r : ℝ) + bitEntropy (s : ℝ)) / 2 < bitEntropy (s : ℝ)
      linarith
    · change 0 < bitEntropy (s : ℝ)
      linarith
  have ha := bitEntropy_lt_one (p := (p : ℝ)) (by intro h; rw [h] at hp; norm_num at hp)
  have ha0 := bitEntropy_nonneg p
  obtain ⟨hs1', -, hs3'⟩ := antiPhaseMixture_strict hp0 hp
  refine ⟨?_, hs1', ?_, hs3', ?_, ?_, ?_⟩
  · rw [hb.1.1, hm]; exact hlt₁
  · rw [informationRate_blockBias hp0 hp, ENNReal.ofReal_lt_ofReal_iff (by linarith)]
    linarith
  · rw [hm, hb.2.2]; exact hlt₂
  · rw [(entropyLaw_antiPhaseMixture hp0 hp).2.2.1.2, informationRate_antiPhaseMixture hp0 hp,
      ENNReal.ofReal_lt_ofReal_iff (by linarith)]
    linarith
  · rw [hi, hb.2.1]; exact hlt₂

/-- §4.4 in existential form: each of the five inequalities of the chain is strict for some
probability measure on the binary shift, and `ess sup h̲_μ` and `H̄_μ` are not comparable
(either may be the smaller). Blueprint node `meas:chain`. -/
theorem noteSupp_exists_entropy_chain_strict :
    (∃ μ : Measure (ℕ → Bool), IsProbabilityMeasure μ ∧
      essInf (fun x ↦ (localEntropy μ shiftMap x).1) μ < (measureEntropy μ shiftMap).1) ∧
    (∃ μ : Measure (ℕ → Bool), IsProbabilityMeasure μ ∧
      (measureEntropy μ shiftMap).1 < (informationRate μ shiftMap).1) ∧
    (∃ μ : Measure (ℕ → Bool), IsProbabilityMeasure μ ∧
      (informationRate μ shiftMap).1 < (informationRate μ shiftMap).2) ∧
    (∃ μ : Measure (ℕ → Bool), IsProbabilityMeasure μ ∧
      (informationRate μ shiftMap).2 < (measureEntropy μ shiftMap).2) ∧
    (∃ μ : Measure (ℕ → Bool), IsProbabilityMeasure μ ∧
      (measureEntropy μ shiftMap).2 < essSup (fun x ↦ (localEntropy μ shiftMap x).2) μ) ∧
    (∃ μ : Measure (ℕ → Bool), IsProbabilityMeasure μ ∧
      essSup (fun x ↦ (localEntropy μ shiftMap x).1) μ < (informationRate μ shiftMap).2) ∧
    ∃ μ : Measure (ℕ → Bool), IsProbabilityMeasure μ ∧
      (informationRate μ shiftMap).2 < essSup (fun x ↦ (localEntropy μ shiftMap x).1) μ := by
  set p : I := ⟨1 / 4, by norm_num, by norm_num⟩ with hpdef
  have hp0 : 0 < (p : ℝ) := by norm_num [p]
  have hp : (p : ℝ) < 1 / 2 := by norm_num [p]
  have hr : (4⁻¹ : ℝ≥0) ≤ 1 := inv_le_one_of_one_le₀ (by norm_num)
  have hs : (2⁻¹ : ℝ≥0) ≤ 1 := inv_le_one_of_one_le₀ (by norm_num)
  have hrs : binEntropyBits ((4⁻¹ : ℝ≥0) : ℝ) < binEntropyBits ((2⁻¹ : ℝ≥0) : ℝ) := by
    have h1 : bitEntropy ((4⁻¹ : ℝ≥0) : ℝ) < 1 := bitEntropy_lt_one (by norm_num)
    have h2 : bitEntropy ((2⁻¹ : ℝ≥0) : ℝ) = 1 := by
      rw [NNReal.coe_inv, NNReal.coe_ofNat, bitEntropy, Real.binEntropy_two_inv,
        div_self (Real.log_pos one_lt_two).ne']
    rw [noteSupp_binEntropyBits_eq, noteSupp_binEntropyBits_eq, h2,
      ENNReal.ofReal_lt_ofReal_iff one_pos]
    exact h1
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := noteSupp_entropy_chain_strict hr hs hp0 hp
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hrs
  exact ⟨⟨_, inferInstance, h1⟩, ⟨_, inferInstance, h2⟩, ⟨_, inferInstance, h3⟩,
    ⟨_, inferInstance, h4⟩, ⟨_, inferInstance, h5⟩, ⟨_, inferInstance, h6⟩,
    ⟨_, inferInstance, h7⟩⟩

end chain

/-! ### Example 5.2, algorithmic sentence -/

section randomPoints

variable {p : I}

/-- `ofReal t + ofReal (1 - t) = 1` for `t ∈ [0, 1]`. -/
lemma noteSupp_ofReal_add_ofReal_one_sub (t : I) :
    ENNReal.ofReal t + ENNReal.ofReal (1 - t) = 1 := by
  rw [← ENNReal.ofReal_add t.2.1 (sub_nonneg.2 t.2.2)]
  simp

/-- Example 5.2 (and every `μ_t` of Example 6.8), "every `μ`-random point is `μ₁`-random or
`μ₂`-random", for every presentation of Cantor space with an `A`-computable metric table (no
computability of `p` or `t` is needed). Blueprint node `meas:examples`. -/
theorem noteSupp_randomPoints_antiPhaseSegment_subset (P : Presentation (ℕ → Bool))
    (A : Set ℕ) (hP : ComputablePresentationIn P A) (t : I) :
    randomPoints P A (antiPhaseSegment p t) ⊆
      randomPoints P A (productBernoulli (blockBias p)) ∪
        randomPoints P A (productBernoulli (blockBiasSwap p)) :=
  noteSupp_randomPoints_add_subset P A hP _ _ (noteSupp_ofReal_add_ofReal_one_sub t).le

/-- Example 5.2, reduction of the algorithmic sentence to the components: if `A` is admissible
for both `μ₁` and `μ₂`, then at every `μ_t`-random point `x` the orbit complexities relative to
`A` are the local entropies `Φ_{μ_i}(x)` of a component for which `x` is random (Theorem 3.3
applied to `μ_i`). What is missing for the note's sentence at such an oracle is the value
`Φ_{μ_i}(x) = ((1+2a)/3, (2+a)/3)` at every `μ_i`-random point (it is known `μ_i`-a.e.,
`ae_localEntropy_blockBias`). Blueprint node `meas:examples`. -/
theorem noteSupp_orbitComplexities_antiPhaseSegment_of_mem_randomPoints
    (P : Presentation (ℕ → Bool)) (A : Set ℕ) (t : I)
    (h₁ : IsMeasureAdmissible P shiftMap (productBernoulli (blockBias p)) A)
    (h₂ : IsMeasureAdmissible P shiftMap (productBernoulli (blockBiasSwap p)) A)
    {x : ℕ → Bool} (hx : x ∈ randomPoints P A (antiPhaseSegment p t)) :
    (x ∈ randomPoints P A (productBernoulli (blockBias p)) ∧
        orbitComplexities P shiftMap A x =
          localEntropy (productBernoulli (blockBias p)) shiftMap x) ∨
      (x ∈ randomPoints P A (productBernoulli (blockBiasSwap p)) ∧
        orbitComplexities P shiftMap A x =
          localEntropy (productBernoulli (blockBiasSwap p)) shiftMap x) := by
  rcases noteSupp_randomPoints_antiPhaseSegment_subset P A h₁.1 t hx with h | h
  · exact Or.inl ⟨h, orbitComplexities_eq_localEntropy P shiftMap continuous_shiftMap_cantor A _
      h₁ h⟩
  · exact Or.inr ⟨h, orbitComplexities_eq_localEntropy P shiftMap continuous_shiftMap_cantor A _
      h₂ h⟩

/-- Example 5.2, lower complexity at every random point, for every admissible oracle: at every
`μ_t`-random point `K̲^A(x, σ) ≤ (1+2a)/3` (Theorem 4.3(a)). Blueprint node `meas:examples`. -/
theorem noteSupp_orbitComplexities_fst_antiPhaseSegment_le (hp0 : 0 < (p : ℝ))
    (hp : (p : ℝ) < 1 / 2) (P : Presentation (ℕ → Bool)) (A : Set ℕ) (t : I)
    (hA : IsMeasureAdmissible P shiftMap (antiPhaseSegment p t) A) {x : ℕ → Bool}
    (hx : x ∈ randomPoints P A (antiPhaseSegment p t)) :
    (orbitComplexities P shiftMap A x).1 ≤ ENNReal.ofReal ((1 + 2 * bitEntropy p) / 3) :=
  noteSupp_orbitComplexities_fst_le_of_ae P shiftMap continuous_shiftMap_cantor A _ hA
    ((ae_localEntropy_antiPhaseSegment hp0 hp t).mono fun _ h ↦ by rw [h]) hx

/-- Example 5.2, the algorithmic sentence on a cone of oracles: for every presentation of Cantor
space there is an oracle `C` such that for every `B ≥_T C` (admissible for `μ_t`) every
`μ_t`-random point relative to `B` is `μ₁`- or `μ₂`-random and has orbit complexities
`K̲^B(x, σ) = (1+2a)/3 < K̄^B(x, σ) = (2+a)/3`. The note claims this for every admissible
oracle; see `noteSupp_orbitComplexities_antiPhaseSegment_of_mem_randomPoints` for what is
missing. Blueprint node `meas:examples`. -/
theorem noteSupp_exists_cone_orbitComplexities_antiPhaseSegment (hp0 : 0 < (p : ℝ))
    (hp : (p : ℝ) < 1 / 2) (P : Presentation (ℕ → Bool)) (t : I) :
    ∃ C : Set ℕ, ∀ B : Set ℕ, charOracle C ≤ᵀ charOracle B →
      IsMeasureAdmissible P shiftMap (antiPhaseSegment p t) B ∧
        ∀ x ∈ randomPoints P B (antiPhaseSegment p t),
          (x ∈ randomPoints P B (productBernoulli (blockBias p)) ∪
            randomPoints P B (productBernoulli (blockBiasSwap p))) ∧
          orbitComplexities P shiftMap B x = (ENNReal.ofReal ((1 + 2 * bitEntropy p) / 3),
            ENNReal.ofReal ((2 + bitEntropy p) / 3)) := by
  obtain ⟨C, hC⟩ := noteSupp_exists_cone_orbitComplexities_eq P shiftMap
    continuous_shiftMap_cantor _ (ae_localEntropy_antiPhaseSegment hp0 hp t)
  refine ⟨C, fun B hB ↦ ⟨(hC B hB).1, fun x hx ↦ ⟨?_, (hC B hB).2 x hx⟩⟩⟩
  exact noteSupp_randomPoints_antiPhaseSegment_subset P B (hC B hB).1.1 t hx

/-- Example 5.2 in the note's words, on a cone of oracles and for the standard presentation:
"`K(x↾n)/n` oscillates between `(1+2a)/3` and `(2+a)/3`" at every `μ_t`-random point relative to
`B`: `liminf_n K^B(x↾n)/n ≤ (1+2a)/3 < (2+a)/3 ≤ limsup_n K^B(x↾n)/n` (from the translations
`liminf_wordComplexity_le_orbitComplexities_fst`, `orbitComplexities_snd_le_limsup_wordComplexity`
between orbit and prefix complexity). Blueprint node `meas:examples`. -/
theorem noteSupp_exists_cone_wordComplexity_antiPhaseSegment (hp0 : 0 < (p : ℝ))
    (hp : (p : ℝ) < 1 / 2) (t : I) :
    ∃ C : Set ℕ, ∀ B : Set ℕ, charOracle C ≤ᵀ charOracle B →
      ∀ x ∈ randomPoints cantorPresentation B (antiPhaseSegment p t),
        liminf (fun n : ℕ ↦ (wordComplexity B x n : ℝ≥0∞) / n) atTop ≤
            ENNReal.ofReal ((1 + 2 * bitEntropy p) / 3) ∧
          ENNReal.ofReal ((1 + 2 * bitEntropy p) / 3) <
            ENNReal.ofReal ((2 + bitEntropy p) / 3) ∧
          ENNReal.ofReal ((2 + bitEntropy p) / 3) ≤
            limsup (fun n : ℕ ↦ (wordComplexity B x n : ℝ≥0∞) / n) atTop := by
  have hd : ∀ x y : ℕ → Bool, x ≠ y → dist x y = (1 / 2 : ℝ) ^ PiNat.firstDiff x y :=
    fun _ _ ↦ cantorMetricSpace_dist_eq
  obtain ⟨C, hC⟩ := noteSupp_exists_cone_orbitComplexities_antiPhaseSegment hp0 hp
    cantorPresentation t
  refine ⟨C, fun B hB x hx ↦ ?_⟩
  have h := ((hC B hB).2 x hx).2
  have ha := bitEntropy_lt_one (p := (p : ℝ)) (by intro h; rw [h] at hp; norm_num at hp)
  have ha0 := bitEntropy_nonneg p
  refine ⟨?_, (ENNReal.ofReal_lt_ofReal_iff (by linarith)).2 (by linarith), ?_⟩
  · have := liminf_wordComplexity_le_orbitComplexities_fst (by norm_num) (by norm_num) hd
      cantorPresentation B (cantorPres_computableIn_symbols B) x
    rwa [h] at this
  · have := orbitComplexities_snd_le_limsup_wordComplexity (by norm_num) (by norm_num) hd
      cantorPresentation B (cantorPres_computableIn_symbols B) x
    rwa [h] at this

/-- Example 5.2, "the expected complexity rate `(1/n) ∫ K(x↾n) dμ` converges to `(1+a)/2`", in
Bowen-ball form: for every oracle admissible for `μ = ½(μ₁ + μ₂)` the lower and upper growth
rates of the expected orbit complexity `∫ K_n^A(x, σ, 2^{-q}) dμ`, as `q → ∞`, are both
`(1+a)/2` (Proposition 4.6 and `informationRate_antiPhaseMixture`). Blueprint node
`meas:examples`. -/
theorem noteSupp_expectedOrbitComplexity_rate_antiPhaseMixture (hp0 : 0 < (p : ℝ))
    (hp : (p : ℝ) < 1 / 2) (P : Presentation (ℕ → Bool)) (A : Set ℕ)
    (hA : IsMeasureAdmissible P shiftMap (antiPhaseMixture p) A) :
    (⨆ q : ℕ, liminf (fun n : ℕ ↦
        expectedOrbitComplexity P shiftMap A (antiPhaseMixture p) n (dyadicRadius q) / n) atTop,
      ⨆ q : ℕ, limsup (fun n : ℕ ↦
        expectedOrbitComplexity P shiftMap A (antiPhaseMixture p) n (dyadicRadius q) / n) atTop) =
      (ENNReal.ofReal ((1 + bitEntropy p) / 2), ENNReal.ofReal ((1 + bitEntropy p) / 2)) := by
  rw [← informationRate_eq_expectedOrbitComplexity_rate P shiftMap continuous_shiftMap_cantor A _
    hA, informationRate_antiPhaseMixture hp0 hp]

end randomPoints

end Kolmogorov.PointToSet
