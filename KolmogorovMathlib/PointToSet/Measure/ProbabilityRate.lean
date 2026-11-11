/-
Copyright (c) 2026 Emma Dinowitz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emma Dinowitz
-/
import KolmogorovMathlib.PointToSet.Measure.InformationRate
import Mathlib.MeasureTheory.Function.EssSup
import Mathlib.MeasureTheory.Integral.Indicator

/-!
# Rates in probability (§6.2, Proposition 6.10)

For a sequence of functions `g_n` on a probability space the lower and upper rates in
probability are

`sup {α : μ{g_n < α} → 0}` and `inf {β : μ{g_n > β} → 0}`

(`lowerProbRate`, `upperProbRate`). For `g_n = f_n^ε = -(1/n) log₂ μ(B_n(x, T, ε))` these are
the rates `H̲^p_μ(T, ε)`, `H̄^p_μ(T, ε)` of E. Dinowitz, *Entropy of non-invariant measures and
orbit complexity of random points*, §6.2; on a shift they are the spectral inf- and
sup-entropy rates of the information-spectrum method.

* Proposition 6.10: `ess inf h̲_μ(T, ·, ε) ≤ H̲^p_μ(T, ε) ≤ H̲_μ(T, ε)` and
  `H̄^p_μ(T, ε) ≤ ess sup h̄_μ(T, ·, ε)`; on a compact space `H̄_μ(T, ε) ≤ H̄^p_μ(T, ε)`
  (`essInf_localEntropyAt_le_lowerProbRate`, `lowerProbRate_le_informationRateAt`,
  `upperProbRate_le_essSup_localEntropyAt`, `informationRateAt_le_upperProbRate`).
* `iSup_lowerProbRate_orbitComplexity`, `iSup_upperProbRate_orbitComplexity`: in the limit
  `ε → 0` the rates in probability of `K_n^A(x, T, ε) / n` equal those of `f_n^ε`, for every
  admissible oracle.

The comparison of rates in probability goes through domination at all thresholds outside sets
of vanishing measure (`ProbDominated`); the two dominations used are the coding bound
`K_n^A(x, T, 6ε) / n ≲ f_n^ε(x)` and Lemma 3.2 in integrated form,
`f_n^{2ε}(x) ≤ K_n^A(x, T, ε) / n + o(1)` outside the sets where the test function exceeds
`2^{⌊log₂ n⌋}` (Markov's inequality).

Blueprint node `meas:probability-rate`.
-/

namespace Kolmogorov.PointToSet

open Filter Set MeasureTheory
open scoped Topology ENNReal Computability

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

/-- The lower rate in probability `sup {α : μ{g_n < α} → 0}` of a sequence of functions.
Blueprint node `meas:probability-rate`. -/
noncomputable def lowerProbRate (μ : Measure X) (g : ℕ → X → ℝ≥0∞) : ℝ≥0∞ :=
  sSup {α : ℝ≥0∞ | Tendsto (fun n ↦ μ {x | g n x < α}) atTop (𝓝 0)}

/-- The upper rate in probability `inf {β : μ{g_n > β} → 0}` of a sequence of functions.
Blueprint node `meas:probability-rate`. -/
noncomputable def upperProbRate (μ : Measure X) (g : ℕ → X → ℝ≥0∞) : ℝ≥0∞ :=
  sInf {β : ℝ≥0∞ | Tendsto (fun n ↦ μ {x | β < g n x}) atTop (𝓝 0)}

/-! ### Generalities -/

omit [MetricSpace X] [BorelSpace X] in
/-- If almost every point eventually leaves the measurable sets `s n`, then their measures tend
to `0` (finite measure). -/
private theorem tendsto_measure_zero_of_ae_eventually {μ : Measure X} [IsFiniteMeasure μ]
    {s : ℕ → Set X} (hs : ∀ n, MeasurableSet (s n)) (h : ∀ᵐ x ∂μ, ∀ᶠ n in atTop, x ∉ s n) :
    Tendsto (fun n ↦ μ (s n)) atTop (𝓝 0) := by
  have := tendsto_measure_of_ae_tendsto_indicator (μ := μ) atTop MeasurableSet.empty hs
    MeasurableSet.univ (measure_ne_top μ _) (.of_forall fun _ ↦ subset_univ _)
    (h.mono fun x hx ↦ hx.mono fun n hn ↦ by simp [hn])
  simpa using this

omit [MetricSpace X] [BorelSpace X] in
/-- If eventually `s n ⊆ t n ∪ E n` and the measures of `t n` and `E n` tend to `0`, so do
those of `s n`. -/
private theorem tendsto_measure_of_subset_union {μ : Measure X} {s t E : ℕ → Set X}
    (ht : Tendsto (fun n ↦ μ (t n)) atTop (𝓝 0)) (hE : Tendsto (fun n ↦ μ (E n)) atTop (𝓝 0))
    (h : ∀ᶠ n in atTop, s n ⊆ t n ∪ E n) : Tendsto (fun n ↦ μ (s n)) atTop (𝓝 0) := by
  have h0 : Tendsto (fun n ↦ μ (t n) + μ (E n)) atTop (𝓝 0) := by simpa using ht.add hE
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h0
    (.of_forall fun _ ↦ zero_le)
    (h.mono fun n hn ↦ (measure_mono hn).trans (measure_union_le _ _))

/-- Domination in probability at all thresholds: for all levels `a < c`, outside sets of
vanishing measure, eventually `h n x ≤ a` forces `g n x ≤ c`. -/
private def ProbDominated (μ : Measure X) (g h : ℕ → X → ℝ≥0∞) : Prop :=
  ∀ a c : ℝ≥0∞, a < c → ∃ E : ℕ → Set X, Tendsto (fun n ↦ μ (E n)) atTop (𝓝 0) ∧
    ∀ᶠ n in atTop, ∀ x, x ∉ E n → h n x ≤ a → g n x ≤ c

omit [MetricSpace X] [BorelSpace X] in
/-- Domination in probability compares the lower rates in probability. -/
private theorem ProbDominated.lowerProbRate_le {μ : Measure X} {g h : ℕ → X → ℝ≥0∞}
    (hgh : ProbDominated μ g h) : lowerProbRate μ g ≤ lowerProbRate μ h := by
  refine sSup_le fun α hα ↦ le_of_forall_lt_imp_le_of_dense fun a ha ↦ le_sSup ?_
  obtain ⟨c, hac, hcα⟩ := exists_between ha
  obtain ⟨E, hE, hev⟩ := hgh a c hac
  refine tendsto_measure_of_subset_union (t := fun n ↦ {x | g n x < α}) hα hE
    (hev.mono fun n hn x hx ↦ ?_)
  by_contra hx'
  simp only [mem_union, mem_ofPred_eq, not_or, not_lt] at hx' hx
  exact lt_irrefl _ (((hn x hx'.2 hx.le).trans_lt hcα).trans_le hx'.1)

omit [MetricSpace X] [BorelSpace X] in
/-- Domination in probability compares the upper rates in probability. -/
private theorem ProbDominated.upperProbRate_le {μ : Measure X} {g h : ℕ → X → ℝ≥0∞}
    (hgh : ProbDominated μ g h) : upperProbRate μ g ≤ upperProbRate μ h := by
  refine le_sInf fun β hβ ↦ le_of_forall_gt_imp_ge_of_dense fun c hc ↦ sInf_le ?_
  obtain ⟨E, hE, hev⟩ := hgh β c hc
  refine tendsto_measure_of_subset_union (t := fun n ↦ {x | β < h n x}) hβ hE
    (hev.mono fun n hn x hx ↦ ?_)
  by_contra hx'
  simp only [mem_union, mem_ofPred_eq, not_or, not_lt] at hx' hx
  exact (hn x hx'.2 hx'.1).not_gt hx

omit [MetricSpace X] [BorelSpace X] in
/-- Pointwise domination is domination in probability. -/
private theorem probDominated_of_le {μ : Measure X} {g h : ℕ → X → ℝ≥0∞}
    (hle : ∀ n x, g n x ≤ h n x) : ProbDominated μ g h :=
  fun _ _ hac ↦ ⟨fun _ ↦ ∅, by simp, .of_forall fun n x _ hx ↦ (hle n x).trans (hx.trans hac.le)⟩

omit [MetricSpace X] [BorelSpace X] in
/-- Domination up to a vanishing additive error outside sets of vanishing measure is
domination in probability. -/
private theorem probDominated_of_le_add {μ : Measure X} {g h : ℕ → X → ℝ≥0∞}
    {E : ℕ → Set X} {d : ℕ → ℝ≥0∞} (hE : Tendsto (fun n ↦ μ (E n)) atTop (𝓝 0))
    (hd : Tendsto d atTop (𝓝 0)) (hle : ∀ᶠ n in atTop, ∀ x, x ∉ E n → g n x ≤ h n x + d n) :
    ProbDominated μ g h := by
  intro a c hac
  refine ⟨E, hE, ?_⟩
  filter_upwards [hle, (tendsto_order.1 hd).2 _ (tsub_pos_of_lt hac)] with n hn hdn x hx hxa
  calc g n x ≤ h n x + d n := hn x hx
    _ ≤ a + (c - a) := add_le_add hxa hdn.le
    _ = c := add_tsub_cancel_of_le hac.le

/-! ### Error terms -/

/-- `log₂ n / n → 0`. -/
private theorem tendsto_logb_div_nat :
    Tendsto (fun n : ℕ ↦ Real.logb 2 n / n) atTop (𝓝 0) := by
  have h := (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp
    tendsto_natCast_atTop_atTop
  have h2 := h.div_const (Real.log 2)
  simp only [zero_div] at h2
  refine h2.congr fun n ↦ ?_
  simp [Real.logb]
  ring

/-- An error term `(C + D log₂ n) / n` tends to zero. -/
private theorem tendsto_ofReal_err (C D : ℝ) :
    Tendsto (fun n : ℕ ↦ ENNReal.ofReal ((C + D * Real.logb 2 n) / n)) atTop (𝓝 0) := by
  rw [← ENNReal.ofReal_zero]
  refine ENNReal.tendsto_ofReal ?_
  have h1 := tendsto_const_div_atTop_nhds_zero_nat C
  have h2 := tendsto_logb_div_nat.const_mul D
  rw [mul_zero] at h2
  simpa [add_div, mul_div_assoc] using h1.add h2

/-- A natural number divided by a positive natural number, as an extended real. -/
private theorem natCast_div_natCast_eq_ofReal (K : ℕ) {n : ℕ} (hn : 1 ≤ n) :
    (K : ℝ≥0∞) / n = ENNReal.ofReal ((K : ℝ) / n) := by
  rw [ENNReal.ofReal_div_of_pos (by exact_mod_cast hn), ENNReal.ofReal_natCast,
    ENNReal.ofReal_natCast]

/-- `2^{-(j + 2 log₂ n)} = 2^{-j} / n²` for `n ≥ 1`. -/
private theorem ofReal_two_rpow_neg_eq (j : ℕ) {n : ℕ} (hn : 1 ≤ n) :
    ENNReal.ofReal ((2 : ℝ) ^ (-((j : ℝ) + 2 * Real.logb 2 n))) =
      (2 : ℝ≥0∞)⁻¹ ^ j / (n : ℝ≥0∞) ^ 2 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have h2 : (2 : ℝ) ^ ((j : ℝ) + 2 * Real.logb 2 n) = 2 ^ j * (n : ℝ) ^ 2 := by
    rw [Real.rpow_add two_pos, Real.rpow_natCast, mul_comm (2 : ℝ), Real.rpow_mul zero_le_two,
      Real.rpow_logb two_pos (by norm_num) hn0, Real.rpow_two]
  rw [Real.rpow_neg zero_le_two, h2, ENNReal.ofReal_inv_of_pos (by positivity),
    ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow zero_le_two, ENNReal.ofReal_pow hn0.le,
    ENNReal.ofReal_ofNat, ENNReal.ofReal_natCast, div_eq_mul_inv, ENNReal.inv_pow,
    ENNReal.mul_inv (Or.inl (by simp)) (Or.inl (by simp))]
  simp only [ENNReal.inv_pow]

/-! ### The two dominations -/

/-- The test function of Lemma 3.2 is a Borel function: a countable sum of constants times
indicators of open sets. -/
private theorem measurable_testFunction' (P : Presentation X) {T : X → X} (hT : Continuous T)
    (A : Set ℕ) (μ : Measure X) (ε : ℝ) : Measurable (testFunction P T A μ ε) := by
  refine Measurable.tsum fun n ↦ Measurable.tsum fun i ↦ ?_
  by_cases hn : n = 0
  · simp only [hn, ↓reduceIte]
    exact measurable_const
  · simp only [hn, ↓reduceIte]
    exact measurable_const.mul ((measurable_const.indicator
      (bowen_ball_dense_open T hT n _ ε).measurableSet).div_const _)

/-- The coding bound in probability: `K_n^A(x, T, 6ε) / n` is dominated by
`f_n^ε(x) = -(1/n) log₂ μ(B_n(x, T, ε))` at all thresholds, for rational `ε > 0`. -/
private theorem probDominated_orbitComplexity_localEntropyRate (P : Presentation X) (T : X → X)
    (hT : Continuous T) (A : Set ℕ) (μ : Measure X) [IsProbabilityMeasure μ]
    (hA : IsMeasureAdmissible P T μ A) (ε : ℚ) (hε : 0 < ε) :
    ProbDominated μ (fun n x ↦ finiteScaleBSCost P T (fun _ ↦ 1) A x n (6 * (ε : ℝ)))
      (fun n x ↦ localEntropyRate μ T x n ε) := by
  obtain ⟨c, hc⟩ := coding_by_measure P T hT A μ prob_le_one hA ε hε
  have hε' : (0 : ℝ) < ε := by exact_mod_cast hε
  intro a b hab
  obtain ⟨s, -, has, hsb⟩ := ENNReal.lt_iff_exists_real_btwn.1 hab
  have hs : 0 < s := ENNReal.ofReal_pos.1 (zero_le.trans_lt has)
  set d : ℕ → ℝ≥0∞ := fun n ↦
    ENNReal.ofReal ((1 + c + 2 * Real.logb 2 (s + 2) + 4 * Real.logb 2 n) / n) with hd_def
  have hd : Tendsto d atTop (𝓝 0) := tendsto_ofReal_err _ _
  refine ⟨fun _ ↦ ∅, by simp, ?_⟩
  filter_upwards [eventually_ge_atTop 1, (tendsto_order.1 hd).2 _ (tsub_pos_of_lt hsb)]
    with n hn hdn x _ hxa
  have hlt : localEntropyRate μ T x n ε < ENNReal.ofReal s := hxa.trans_lt has
  set I := infoBits (μ (bowenBall T n x ε)) with hI
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hnE : (n : ℝ≥0∞) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  have hlt' : I < ENNReal.ofReal (s * n) := by
    rw [localEntropyRate, ENNReal.div_lt_iff (Or.inl hnE) (Or.inl (ENNReal.natCast_ne_top n))]
      at hlt
    rwa [ENNReal.ofReal_mul hs.le, ENNReal.ofReal_natCast]
  have hItop : I ≠ ⊤ := (hlt'.trans ENNReal.ofReal_lt_top).ne
  have hIr : I.toReal < s * n := (ENNReal.lt_ofReal_iff_toReal_lt hItop).1 hlt'
  set k := ⌊I.toReal⌋₊ + 1 with hk
  have hIk : I < k := by
    rw [← ENNReal.ofReal_toReal hItop, ← ENNReal.ofReal_natCast]
    refine (ENNReal.ofReal_lt_ofReal_iff (by positivity)).2 ?_
    push_cast [hk]
    exact Nat.lt_floor_add_one _
  have hK := hc x n k hn (two_inv_pow_lt_of_infoBits_lt hIk)
  have hkr : (k : ℝ) ≤ s * n + 1 := by
    have := Nat.floor_le (ENNReal.toReal_nonneg (a := I))
    push_cast [hk]
    linarith
  have hk1 : (k : ℝ) + 1 ≤ (s + 2) * n := by
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    nlinarith
  have hlog : Real.logb 2 ((k : ℝ) + 1) ≤ Real.logb 2 (s + 2) + Real.logb 2 n := by
    rw [← Real.logb_mul (by positivity) hn0.ne']
    exact Real.logb_le_logb_of_le one_lt_two (by positivity) hk1
  have hKr : (orbitComplexityNat P T A x n (6 * ε) : ℝ) ≤
      s * n + (1 + c + 2 * Real.logb 2 (s + 2) + 4 * Real.logb 2 n) := by
    linarith
  have key : finiteScaleBSCost P T (fun _ ↦ 1) A x n (6 * (ε : ℝ)) ≤ ENNReal.ofReal s + d n := by
    rw [entropiesAndOrbitComplexities_rate P T hT A x n hn _ (by positivity),
      natCast_div_natCast_eq_ofReal _ hn]
    calc ENNReal.ofReal ((orbitComplexityNat P T A x n (6 * ε) : ℝ) / n)
        ≤ ENNReal.ofReal (s + (1 + c + 2 * Real.logb 2 (s + 2) + 4 * Real.logb 2 n) / n) := by
          refine ENNReal.ofReal_le_ofReal ?_
          rw [div_le_iff₀ hn0, add_mul, div_mul_cancel₀ _ hn0.ne']
          linarith
      _ ≤ _ := ENNReal.ofReal_add_le
  calc finiteScaleBSCost P T (fun _ ↦ 1) A x n (6 * (ε : ℝ)) ≤ ENNReal.ofReal s + d n := key
    _ ≤ ENNReal.ofReal s + (b - ENNReal.ofReal s) := add_le_add le_rfl hdn.le
    _ = b := add_tsub_cancel_of_le hsb.le

/-- Lemma 3.2 in probability: `f_n^{2ε}(x) = -(1/n) log₂ μ(B_n(x, T, 2ε))` is dominated by
`K_n^A(x, T, ε) / n` at all thresholds, for every oracle and every `ε > 0`. -/
private theorem probDominated_localEntropyRate_orbitComplexity (P : Presentation X) (T : X → X)
    (hT : Continuous T) (A : Set ℕ) (μ : Measure X) [IsProbabilityMeasure μ] {ε : ℝ}
    (hε : 0 < ε) :
    ProbDominated μ (fun n x ↦ localEntropyRate μ T x n (2 * ε))
      (fun n x ↦ finiteScaleBSCost P T (fun _ ↦ 1) A x n ε) := by
  set t := testFunction P T A μ ε with ht
  set j : ℕ → ℕ := fun n ↦ ⌊Real.logb 2 n⌋₊ with hj_def
  have hj : Tendsto j atTop atTop := tendsto_nat_floor_atTop.comp
    ((Real.tendsto_logb_atTop one_lt_two).comp tendsto_natCast_atTop_atTop)
  set E : ℕ → Set X := fun n ↦ {x | (2 : ℝ≥0∞) ^ j n ≤ t x} with hE_def
  have hE : Tendsto (fun n ↦ μ (E n)) atTop (𝓝 0) := by
    have hmark : ∀ n, μ (E n) ≤ 2 * (2 : ℝ≥0∞)⁻¹ ^ j n := fun n ↦ by
      have h1 := mul_meas_ge_le_lintegral₀ (μ := μ)
        (measurable_testFunction' P hT A μ ε).aemeasurable ((2 : ℝ≥0∞) ^ j n)
      have h2 := h1.trans (lintegral_testFunction_lt_two P T hT A μ ε).le
      calc μ (E n) ≤ 2 / 2 ^ j n :=
            (ENNReal.le_div_iff_mul_le (Or.inl (by simp)) (Or.inl (by simp))).2
              (by rwa [mul_comm])
        _ = 2 * (2 : ℝ≥0∞)⁻¹ ^ j n := by rw [div_eq_mul_inv, ENNReal.inv_pow]
    have h0 : Tendsto (fun n ↦ 2 * (2 : ℝ≥0∞)⁻¹ ^ j n) atTop (𝓝 0) := by
      simpa using ENNReal.Tendsto.const_mul
        ((ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num)).comp hj)
        (Or.inr (by simp))
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h0
      (fun _ ↦ zero_le) hmark
  set d : ℕ → ℝ≥0∞ := fun n ↦ ENNReal.ofReal ((j n + 2 * Real.logb 2 n) / n) with hd_def
  have hd : Tendsto d atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds (tendsto_ofReal_err 0 3)
      (.of_forall fun _ ↦ zero_le) ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    refine ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg _))
    have := Nat.floor_le (Real.logb_nonneg one_lt_two (by exact_mod_cast hn : (1 : ℝ) ≤ n))
    simp only [hj_def]
    linarith
  refine probDominated_of_le_add hE hd ?_
  filter_upwards [eventually_ge_atTop 1] with n hn x hx
  simp only [hE_def, mem_ofPred_eq, not_le] at hx
  have htop : t x ≠ ⊤ := (hx.trans (ENNReal.pow_lt_top (by simp))).ne
  have hlem := testFunction_mul_measure_bowenBall_ge P T hT A μ hε x htop hn
  rw [← ht] at hlem
  set K := orbitComplexityNat P T A x n ε with hK
  set q := μ (bowenBall T n x (2 * ε)) with hq
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hL : 0 ≤ Real.logb 2 n := Real.logb_nonneg one_lt_two (by exact_mod_cast hn)
  have hqb : (2 : ℝ≥0∞)⁻¹ ^ (K + j n) / (n : ℝ≥0∞) ^ 2 ≤ q := by
    calc (2 : ℝ≥0∞)⁻¹ ^ (K + j n) / (n : ℝ≥0∞) ^ 2
        = (2 : ℝ≥0∞)⁻¹ ^ j n * ((2 : ℝ≥0∞)⁻¹ ^ K / (n : ℝ≥0∞) ^ 2) := by
          rw [pow_add, mul_comm ((2 : ℝ≥0∞)⁻¹ ^ K), mul_div_assoc]
      _ ≤ (2 : ℝ≥0∞)⁻¹ ^ j n * (t x * q) := by gcongr
      _ ≤ (2 : ℝ≥0∞)⁻¹ ^ j n * ((2 : ℝ≥0∞) ^ j n * q) := by gcongr
      _ = q := by
          rw [← mul_assoc, ← mul_pow, ENNReal.inv_mul_cancel (by simp) (by simp), one_pow,
            one_mul]
  have hinfo : infoBits q ≤ ENNReal.ofReal (((K + j n : ℕ) : ℝ) + 2 * Real.logb 2 n) := by
    refine infoBits_le_of_rpow_le (add_nonneg (Nat.cast_nonneg _) (by linarith)) ?_
    rw [ofReal_two_rpow_neg_eq _ hn]
    exact hqb
  change localEntropyRate μ T x n (2 * ε) ≤ finiteScaleBSCost P T (fun _ ↦ 1) A x n ε + d n
  rw [localEntropyRate, entropiesAndOrbitComplexities_rate P T hT A x n hn _ hε,
    natCast_div_natCast_eq_ofReal _ hn]
  calc infoBits q / n
      ≤ ENNReal.ofReal (((K + j n : ℕ) : ℝ) + 2 * Real.logb 2 n) / n := by gcongr
    _ = ENNReal.ofReal ((K : ℝ) / n + (j n + 2 * Real.logb 2 n) / n) := by
        rw [← ENNReal.ofReal_natCast n, ← ENNReal.ofReal_div_of_pos hn0]
        congr 1
        push_cast
        ring
    _ ≤ _ := ENNReal.ofReal_add_le

/-! ### Proposition 6.10 -/

/-- The normalized mean information is the mean of the finite-time local entropy rates. -/
theorem bowenInformation_div_eq_lintegral {T : X → X} (hT : Continuous T) (μ : Measure X)
    (n : ℕ) (ε : ℝ) :
    bowenInformation μ T n ε / n = ∫⁻ x, localEntropyRate μ T x n ε ∂μ := by
  simp only [localEntropyRate, bowenInformation, div_eq_mul_inv]
  have hm : Measurable fun x ↦ infoBits (μ (bowenBall T n x ε)) :=
    infoBits_antitone.measurable.comp (measurable_measure_bowenBall μ hT n ε)
  exact (lintegral_mul_const _ hm).symm

/-- Proposition 6.10: `ess inf h̲_μ(T, ·, ε) ≤ H̲^p_μ(T, ε)`.
Blueprint node `meas:probability-rate`. -/
theorem essInf_localEntropyAt_le_lowerProbRate {T : X → X} (hT : Continuous T) (μ : Measure X)
    [IsProbabilityMeasure μ] (ε : ℝ) :
    essInf (fun x ↦ (localEntropyAt μ T x ε).1) μ ≤
      lowerProbRate μ fun n x ↦ localEntropyRate μ T x n ε := by
  refine le_of_forall_lt_imp_le_of_dense fun α hα ↦ le_sSup ?_
  have hae := ae_lt_of_lt_essInf hα
  refine tendsto_measure_zero_of_ae_eventually
    (fun n ↦ measurableSet_lt (measurable_localEntropyRate μ hT n ε) measurable_const) ?_
  filter_upwards [hae] with x hx
  exact (eventually_lt_of_lt_liminf hx).mono fun n hn ↦ not_lt.2 hn.le

/-- Proposition 6.10: `H̲^p_μ(T, ε) ≤ H̲_μ(T, ε)` (Markov's inequality).
Blueprint node `meas:probability-rate`. -/
theorem lowerProbRate_le_informationRateAt {T : X → X} (hT : Continuous T) (μ : Measure X)
    [IsProbabilityMeasure μ] (ε : ℝ) :
    (lowerProbRate μ fun n x ↦ localEntropyRate μ T x n ε) ≤ (informationRateAt μ T ε).1 := by
  refine sSup_le fun α hα ↦ ?_
  have hα' : Tendsto (fun n ↦ μ {x | localEntropyRate μ T x n ε < α}) atTop (𝓝 0) := hα
  have hmeas : ∀ n, Measurable fun x ↦ localEntropyRate μ T x n ε :=
    fun n ↦ measurable_localEntropyRate μ hT n ε
  have hcompl : ∀ n, μ {x | α ≤ localEntropyRate μ T x n ε} =
      1 - μ {x | localEntropyRate μ T x n ε < α} := fun n ↦ by
    rw [← prob_compl_eq_one_sub (measurableSet_lt (hmeas n) measurable_const)]
    congr 1
    ext x
    simp
  have h1 : Tendsto (fun n ↦ μ {x | α ≤ localEntropyRate μ T x n ε}) atTop (𝓝 1) := by
    simp_rw [hcompl]
    simpa using ENNReal.Tendsto.sub tendsto_const_nhds hα' (Or.inl ENNReal.one_ne_top)
  have hlim : Tendsto (fun n ↦ α * μ {x | α ≤ localEntropyRate μ T x n ε}) atTop (𝓝 α) := by
    simpa using ENNReal.Tendsto.const_mul h1 (Or.inl one_ne_zero)
  rw [← hlim.liminf_eq]
  refine liminf_le_liminf (Eventually.of_forall fun n ↦ ?_)
  rw [bowenInformation_div_eq_lintegral hT]
  exact mul_meas_ge_le_lintegral₀ (hmeas n).aemeasurable α

/-- Proposition 6.10: `H̄^p_μ(T, ε) ≤ ess sup h̄_μ(T, ·, ε)`.
Blueprint node `meas:probability-rate`. -/
theorem upperProbRate_le_essSup_localEntropyAt {T : X → X} (hT : Continuous T) (μ : Measure X)
    [IsProbabilityMeasure μ] (ε : ℝ) :
    (upperProbRate μ fun n x ↦ localEntropyRate μ T x n ε) ≤
      essSup (fun x ↦ (localEntropyAt μ T x ε).2) μ := by
  refine le_of_forall_gt_imp_ge_of_dense fun β hβ ↦ sInf_le ?_
  have hae := ae_lt_of_essSup_lt hβ
  refine tendsto_measure_zero_of_ae_eventually
    (fun n ↦ measurableSet_lt measurable_const (measurable_localEntropyRate μ hT n ε)) ?_
  filter_upwards [hae] with x hx
  exact (eventually_lt_of_limsup_lt hx).mono fun n hn ↦ not_lt.2 hn.le

/-- Proposition 6.10: on a compact space `H̄_μ(T, ε) ≤ H̄^p_μ(T, ε)` (uniform integrability).
Blueprint node `meas:probability-rate`. -/
theorem informationRateAt_le_upperProbRate [CompactSpace X] {T : X → X} (hT : Continuous T)
    (μ : Measure X) [IsProbabilityMeasure μ] {ε : ℝ} (hε : 0 < ε) :
    (informationRateAt μ T ε).2 ≤ upperProbRate μ fun n x ↦ localEntropyRate μ T x n ε := by
  refine le_sInf fun β hβ ↦ ?_
  have hβ' : Tendsto (fun n ↦ μ {x | β < localEntropyRate μ T x n ε}) atTop (𝓝 0) := hβ
  rcases eq_or_ne β ⊤ with rfl | hβt
  · exact le_top
  obtain ⟨b, -, hb⟩ := exists_setLIntegral_localEntropyRate_le hT μ hε
  set M : ℝ := max b β.toReal + 1 with hM
  have hMb : b < M := by linarith [le_max_left b β.toReal]
  have hβM : β ≤ ENNReal.ofReal M := by
    rw [← ENNReal.ofReal_toReal hβt]
    exact ENNReal.ofReal_le_ofReal (by linarith [le_max_right b β.toReal])
  set d : ℕ → ℝ≥0∞ := fun n ↦ ENNReal.ofReal M * μ {x | β < localEntropyRate μ T x n ε} +
    ENNReal.ofReal ((M + 1) * (2 : ℝ) ^ (-(M - b) * n)) with hd_def
  have hd : Tendsto d atTop (𝓝 0) := by
    have h1 : Tendsto (fun n ↦ ENNReal.ofReal M * μ {x | β < localEntropyRate μ T x n ε})
        atTop (𝓝 0) := by
      simpa using ENNReal.Tendsto.const_mul hβ' (Or.inr ENNReal.ofReal_ne_top)
    have h2 : Tendsto (fun n : ℕ ↦ ENNReal.ofReal ((M + 1) * (2 : ℝ) ^ (-(M - b) * n))) atTop
        (𝓝 0) := by
      rw [← ENNReal.ofReal_zero]
      refine ENNReal.tendsto_ofReal ?_
      have hr : (2 : ℝ) ^ (-(M - b)) < 1 :=
        Real.rpow_lt_one_of_one_lt_of_neg one_lt_two (by linarith)
      have := (tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) hr).const_mul (M + 1)
      rw [mul_zero] at this
      refine this.congr fun n ↦ ?_
      rw [← Real.rpow_natCast, ← Real.rpow_mul zero_le_two]
    rw [hd_def]
    simpa using h1.add h2
  have hbound : ∀ n : ℕ, 1 ≤ n → bowenInformation μ T n ε / n ≤ β + d n := by
    intro n hn
    set f := fun x ↦ localEntropyRate μ T x n ε with hf
    have hfm : Measurable f := measurable_localEntropyRate μ hT n ε
    set S1 := {x | β < f x} with hS1
    set S2 := {x | ENNReal.ofReal M < f x} with hS2
    have hS1m : MeasurableSet S1 := measurableSet_lt measurable_const hfm
    have hS2m : MeasurableSet S2 := measurableSet_lt measurable_const hfm
    have hpt : ∀ x, f x ≤ β + S1.indicator (fun _ ↦ ENNReal.ofReal M) x + S2.indicator f x := by
      intro x
      by_cases h1 : f x ≤ β
      · exact h1.trans (le_self_add.trans le_self_add)
      by_cases h2 : f x ≤ ENNReal.ofReal M
      · have hx1 : x ∈ S1 := not_le.1 h1
        rw [indicator_of_mem hx1]
        exact h2.trans (le_add_self.trans le_self_add)
      · have hx2 : x ∈ S2 := not_le.1 h2
        rw [indicator_of_mem hx2]
        exact le_add_self
    rw [bowenInformation_div_eq_lintegral hT]
    calc ∫⁻ x, f x ∂μ
        ≤ ∫⁻ x, β + S1.indicator (fun _ ↦ ENNReal.ofReal M) x + S2.indicator f x ∂μ :=
          lintegral_mono hpt
      _ = β + ENNReal.ofReal M * μ S1 + ∫⁻ x in S2, f x ∂μ := by
          rw [lintegral_add_left (f := fun x ↦ β + S1.indicator (fun _ ↦ ENNReal.ofReal M) x)
              (measurable_const.add (measurable_const.indicator hS1m)),
            lintegral_add_left (f := fun _ ↦ β) measurable_const, lintegral_const, measure_univ,
            mul_one, lintegral_indicator_const hS1m, lintegral_indicator hS2m]
      _ ≤ β + ENNReal.ofReal M * μ S1 + ENNReal.ofReal ((M + 1) * (2 : ℝ) ^ (-(M - b) * n)) := by
          gcongr
          exact hb M hMb n hn
      _ = β + d n := by rw [add_assoc]
  exact (limsup_le_limsup_of_le_add_tendsto_zero (b := fun _ ↦ β)
    ((eventually_ge_atTop 1).mono hbound) hd).trans (limsup_const β).le

/-! ### Rates in probability of the orbit complexity -/

/-- `6 · 2^{-(p + 3)} ≤ 2^{-p}`. -/
private theorem six_mul_le_dyadicRadius (p : ℕ) :
    6 * (((2 : ℚ)⁻¹ ^ (p + 3) : ℚ) : ℝ) ≤ dyadicRadius p := by
  have h0 : (0 : ℝ) ≤ (2 : ℝ)⁻¹ ^ p := by positivity
  rw [dyadicRadius]
  push_cast
  rw [pow_add]
  norm_num
  linarith

/-- `2 · 2^{-(p + 1)} = 2^{-p}`. -/
private theorem two_mul_dyadicRadius_succ (p : ℕ) : 2 * dyadicRadius (p + 1) = dyadicRadius p := by
  simp only [dyadicRadius, pow_succ]
  ring

/-- The rational dyadic radius `2^{-p}` cast to the reals. -/
private theorem cast_dyadic (p : ℕ) : (((2 : ℚ)⁻¹ ^ p : ℚ) : ℝ) = dyadicRadius p := by
  simp [dyadicRadius]

/-- Proposition 6.10, last statement, lower rates: in the limit `ε → 0` the lower rate in
probability of `K_n^A(x, T, ε) / n` equals that of `f_n^ε`, for every admissible oracle.
Blueprint node `meas:probability-rate`. -/
theorem iSup_lowerProbRate_orbitComplexity (P : Presentation X) (T : X → X)
    (hT : Continuous T) (A : Set ℕ) (μ : Measure X) [IsProbabilityMeasure μ]
    (hA : IsMeasureAdmissible P T μ A) :
    ⨆ p : ℕ, lowerProbRate μ (fun n x ↦
        finiteScaleBSCost P T (fun _ ↦ 1) A x n (dyadicRadius p)) =
      ⨆ p : ℕ, lowerProbRate μ fun n x ↦ localEntropyRate μ T x n (dyadicRadius p) := by
  apply le_antisymm
  · refine iSup_le fun p ↦ ?_
    have hε : (0 : ℚ) < (2 : ℚ)⁻¹ ^ (p + 3) := by positivity
    calc lowerProbRate μ (fun n x ↦ finiteScaleBSCost P T (fun _ ↦ 1) A x n (dyadicRadius p))
        ≤ lowerProbRate μ (fun n x ↦ finiteScaleBSCost P T (fun _ ↦ 1) A x n
            (6 * (((2 : ℚ)⁻¹ ^ (p + 3) : ℚ) : ℝ))) :=
          (probDominated_of_le fun n x ↦ pointwiseBSDimension_antitone_radius P T _ A x n
            (six_mul_le_dyadicRadius p)).lowerProbRate_le
      _ ≤ lowerProbRate μ (fun n x ↦ localEntropyRate μ T x n
            (((2 : ℚ)⁻¹ ^ (p + 3) : ℚ) : ℝ)) :=
          (probDominated_orbitComplexity_localEntropyRate P T hT A μ hA _ hε).lowerProbRate_le
      _ = lowerProbRate μ (fun n x ↦ localEntropyRate μ T x n (dyadicRadius (p + 3))) := by
          rw [cast_dyadic]
      _ ≤ ⨆ q : ℕ, lowerProbRate μ fun n x ↦ localEntropyRate μ T x n (dyadicRadius q) :=
          le_iSup (fun q ↦ lowerProbRate μ fun n x ↦ localEntropyRate μ T x n (dyadicRadius q))
            (p + 3)
  · refine iSup_le fun p ↦ ?_
    calc lowerProbRate μ (fun n x ↦ localEntropyRate μ T x n (dyadicRadius p))
        = lowerProbRate μ (fun n x ↦ localEntropyRate μ T x n (2 * dyadicRadius (p + 1))) := by
          rw [two_mul_dyadicRadius_succ]
      _ ≤ lowerProbRate μ (fun n x ↦
            finiteScaleBSCost P T (fun _ ↦ 1) A x n (dyadicRadius (p + 1))) :=
          (probDominated_localEntropyRate_orbitComplexity P T hT A μ
            (dyadicRadius_pos (p + 1))).lowerProbRate_le
      _ ≤ _ := le_iSup (fun q ↦ lowerProbRate μ (fun n x ↦
            finiteScaleBSCost P T (fun _ ↦ 1) A x n (dyadicRadius q))) (p + 1)

/-- Proposition 6.10, last statement, upper rates: in the limit `ε → 0` the upper rate in
probability of `K_n^A(x, T, ε) / n` equals that of `f_n^ε`, for every admissible oracle.
Blueprint node `meas:probability-rate`. -/
theorem iSup_upperProbRate_orbitComplexity (P : Presentation X) (T : X → X)
    (hT : Continuous T) (A : Set ℕ) (μ : Measure X) [IsProbabilityMeasure μ]
    (hA : IsMeasureAdmissible P T μ A) :
    ⨆ p : ℕ, upperProbRate μ (fun n x ↦
        finiteScaleBSCost P T (fun _ ↦ 1) A x n (dyadicRadius p)) =
      ⨆ p : ℕ, upperProbRate μ fun n x ↦ localEntropyRate μ T x n (dyadicRadius p) := by
  apply le_antisymm
  · refine iSup_le fun p ↦ ?_
    have hε : (0 : ℚ) < (2 : ℚ)⁻¹ ^ (p + 3) := by positivity
    calc upperProbRate μ (fun n x ↦ finiteScaleBSCost P T (fun _ ↦ 1) A x n (dyadicRadius p))
        ≤ upperProbRate μ (fun n x ↦ finiteScaleBSCost P T (fun _ ↦ 1) A x n
            (6 * (((2 : ℚ)⁻¹ ^ (p + 3) : ℚ) : ℝ))) :=
          (probDominated_of_le fun n x ↦ pointwiseBSDimension_antitone_radius P T _ A x n
            (six_mul_le_dyadicRadius p)).upperProbRate_le
      _ ≤ upperProbRate μ (fun n x ↦ localEntropyRate μ T x n
            (((2 : ℚ)⁻¹ ^ (p + 3) : ℚ) : ℝ)) :=
          (probDominated_orbitComplexity_localEntropyRate P T hT A μ hA _ hε).upperProbRate_le
      _ = upperProbRate μ (fun n x ↦ localEntropyRate μ T x n (dyadicRadius (p + 3))) := by
          rw [cast_dyadic]
      _ ≤ ⨆ q : ℕ, upperProbRate μ fun n x ↦ localEntropyRate μ T x n (dyadicRadius q) :=
          le_iSup (fun q ↦ upperProbRate μ fun n x ↦ localEntropyRate μ T x n (dyadicRadius q))
            (p + 3)
  · refine iSup_le fun p ↦ ?_
    calc upperProbRate μ (fun n x ↦ localEntropyRate μ T x n (dyadicRadius p))
        = upperProbRate μ (fun n x ↦ localEntropyRate μ T x n (2 * dyadicRadius (p + 1))) := by
          rw [two_mul_dyadicRadius_succ]
      _ ≤ upperProbRate μ (fun n x ↦
            finiteScaleBSCost P T (fun _ ↦ 1) A x n (dyadicRadius (p + 1))) :=
          (probDominated_localEntropyRate_orbitComplexity P T hT A μ
            (dyadicRadius_pos (p + 1))).upperProbRate_le
      _ ≤ _ := le_iSup (fun q ↦ upperProbRate μ (fun n x ↦
            finiteScaleBSCost P T (fun _ ↦ 1) A x n (dyadicRadius q))) (p + 1)

end Kolmogorov.PointToSet
