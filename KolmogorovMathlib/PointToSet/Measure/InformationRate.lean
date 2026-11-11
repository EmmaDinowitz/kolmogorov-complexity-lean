/-
Copyright (c) 2026 Emma Dinowitz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emma Dinowitz
-/
import KolmogorovMathlib.PointToSet.Measure.Pointwise
import KolmogorovMathlib.PointToSet.Measure.Decomposition

/-!
# Information rates along Bowen balls (§4.3, Proposition 6.16)

The Bowen-ball analogue of the Shannon entropy of the `n`-th refinement of a partition is the
mean information `I_n(μ, ε) = ∫ -log₂ μ(B_n(x, T, ε)) dμ(x)` (`bowenInformation`). Its lower
and upper growth rates `H̲_μ(T, ε)`, `H̄_μ(T, ε)` (`informationRateAt`) and their limits
`H̲_μ(T)`, `H̄_μ(T)` as `ε → 0` (`informationRate`) are the information rates of the measure
(E. Dinowitz, *Entropy of non-invariant measures and orbit complexity of random points*, §4.3).

* `bowenInformation_le_expectedOrbitComplexity`,
  `expectedOrbitComplexity_le_bowenInformation` (Proposition 4.6): the mean information and the
  expected orbit complexity `∫ K_n^A(x, T, ε) dμ` agree up to logarithmic terms and a change of
  scale; `informationRate_eq_expectedOrbitComplexity_rate`: hence the information rates are the
  rates of the expected orbit complexity.
* `measureEntropy_fst_le_informationRate_fst`, `informationRate_fst_le_snd`,
  `informationRate_snd_le_measureEntropy_snd` (Proposition 4.7):
  `h̲_μ(T) ≤ H̲_μ(T) ≤ H̄_μ(T)`, and `H̄_μ(T) ≤ h̄_μ(T)` on a compact space.
* `expectedOrbitComplexity_sum`, `bowenInformation_sum_le`, `sum_bowenInformation_le`
  (Proposition 6.16): on a countable convex combination the expected orbit complexity is
  affine, and the mean information is affine up to the entropy of the weights, a logarithmic
  term and a change of scale.

Auxiliary results: `measurable_testFunction`, `orbitComplexityNat_antitone_radius`,
`expectedOrbitComplexity_antitone_radius`, `lintegral_localEntropyRate` (`∫ f_n dμ = I_n / n`),
`exists_measure_setOf_measure_bowenBall_lt_le` (counting Bowen balls on a compact space) and
`infoBits_mul_le_add` (subadditivity of the information on products).

Blueprint nodes `meas:information-rate`, `meas:expected-complexity`, `meas:comparison`,
`meas:finite-time-affinity`.
-/

namespace Kolmogorov.PointToSet

open Filter Set MeasureTheory
open scoped Topology ENNReal Computability

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

/-- The mean information `I_n(μ, ε) = ∫ -log₂ μ(B_n(x, T, ε)) dμ(x)` of Bowen balls.
Blueprint node `meas:information-rate`. -/
noncomputable def bowenInformation (μ : Measure X) (T : X → X) (n : ℕ) (ε : ℝ) : ℝ≥0∞ :=
  ∫⁻ x, infoBits (μ (bowenBall T n x ε)) ∂μ

/-- The lower and upper information rates `H̲_μ(T, ε)`, `H̄_μ(T, ε)` at the scale `ε`.
Blueprint node `meas:information-rate`. -/
noncomputable def informationRateAt (μ : Measure X) (T : X → X) (ε : ℝ) : ℝ≥0∞ × ℝ≥0∞ :=
  (liminf (fun n : ℕ ↦ bowenInformation μ T n ε / n) atTop,
    limsup (fun n : ℕ ↦ bowenInformation μ T n ε / n) atTop)

/-- The lower and upper information rates `H̲_μ(T)`, `H̄_μ(T)`, as suprema over the dyadic
scales. Blueprint node `meas:information-rate`. -/
noncomputable def informationRate (μ : Measure X) (T : X → X) : ℝ≥0∞ × ℝ≥0∞ :=
  (⨆ p : ℕ, (informationRateAt μ T (dyadicRadius p)).1,
    ⨆ p : ℕ, (informationRateAt μ T (dyadicRadius p)).2)

/-- The expected orbit complexity `∫ K_n^A(x, T, ε) dμ(x)`.
Blueprint node `meas:expected-complexity`. -/
noncomputable def expectedOrbitComplexity (P : Presentation X) (T : X → X) (A : Set ℕ)
    (μ : Measure X) (n : ℕ) (ε : ℝ) : ℝ≥0∞ :=
  ∫⁻ x, (orbitComplexityNat P T A x n ε : ℝ≥0∞) ∂μ

/-- The sets `{K_n^A(·, T, ε) ≤ m}` are open, so the orbit complexity at a finite time is a
Borel function of the point. Blueprint node `meas:expected-complexity`. -/
theorem measurable_orbitComplexityNat (P : Presentation X) {T : X → X} (hT : Continuous T)
    (A : Set ℕ) (n : ℕ) (ε : ℝ) : Measurable fun x ↦ orbitComplexityNat P T A x n ε := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp only [orbitComplexityNat, orbitComplexity, bowen_ball_dense_zero, mem_univ]
    exact measurable_const
  rcases le_or_gt ε 0 with hε | hε
  · have hempty : ∀ x, bowenBall T n x ε = ∅ := fun x ↦ eq_empty_iff_forall_notMem.2 fun y hy ↦
      (dist_nonneg.trans_lt (mem_bowenBall_iff.1 hy 0 hn)).not_ge hε
    simp only [orbitComplexityNat, orbitComplexity, hempty, mem_empty_iff_false]
    exact measurable_const
  refine measurable_of_Iic fun m ↦ ?_
  have hset : (fun x ↦ orbitComplexityNat P T A x n ε) ⁻¹' Iic m =
      ⋃ i ∈ {i | oracleNatComplexity A i ≤ m}, bowenBall T n (P.ι i) ε := by
    ext x
    simp only [mem_preimage, mem_Iic, mem_iUnion, mem_ofPred_eq, exists_prop]
    constructor
    · intro hx
      obtain ⟨i, hi, hK⟩ := entropiesAndOrbitComplexities_attained P T hT A x n hn ε hε
      refine ⟨i, ?_, mem_bowenBall_symm hi⟩
      rwa [orbitComplexityNat, hK, ENat.toNat_natCast] at hx
    · rintro ⟨i, hi, hx⟩
      exact (orbitComplexityNat_le_of_mem P T A (mem_bowenBall_symm hx)).trans hi
  rw [hset]
  exact (isOpen_biUnion fun i _ ↦ bowen_ball_dense_open T hT n _ ε).measurableSet

/-- The pair of orbit complexities `Ψ^A` is a Borel map.
Blueprint node `meas:expected-complexity`. -/
theorem measurable_orbitComplexities (P : Presentation X) {T : X → X} (hT : Continuous T)
    (A : Set ℕ) : Measurable fun x ↦ orbitComplexities P T A x := by
  have hcost : ∀ p n : ℕ,
      Measurable fun x ↦ finiteScaleBSCost P T (fun _ ↦ 1) A x n (dyadicRadius p) := by
    intro p n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp only [finiteScaleBSCost, ↓reduceIte]
      exact measurable_const
    simp only [entropiesAndOrbitComplexities_rate P T hT A _ n hn _ (dyadicRadius_pos p)]
    exact (measurable_from_nat.comp (measurable_orbitComplexityNat P hT A n _)).div_const _
  exact (Measurable.iSup fun p ↦ Measurable.liminf fun n ↦ hcost p n).prodMk
    (Measurable.iSup fun p ↦ Measurable.limsup fun n ↦ hcost p n)

omit [BorelSpace X] in
/-- The mean information is antitone in the scale. -/
theorem bowenInformation_antitone (μ : Measure X) (T : X → X) (n : ℕ) :
    Antitone (bowenInformation μ T n) := fun _ _ h ↦
  lintegral_mono fun _ ↦ infoBits_antitone (measure_mono (bowenBall_subset_of_le T n _ h))

omit [BorelSpace X] in
/-- The information rates at a fixed scale are antitone in the scale. -/
theorem informationRateAt_antitone (μ : Measure X) (T : X → X) {ε ε' : ℝ} (h : ε ≤ ε') :
    (informationRateAt μ T ε').1 ≤ (informationRateAt μ T ε).1 ∧
      (informationRateAt μ T ε').2 ≤ (informationRateAt μ T ε).2 :=
  ⟨liminf_le_liminf (Eventually.of_forall fun n ↦
      ENNReal.div_le_div_right (bowenInformation_antitone μ T n h) _),
    limsup_le_limsup (Eventually.of_forall fun n ↦
      ENNReal.div_le_div_right (bowenInformation_antitone μ T n h) _)⟩

omit [BorelSpace X] in
/-- The information rate at any positive scale is at most the information rate. -/
theorem informationRateAt_le_informationRate (μ : Measure X) (T : X → X) {ε : ℝ}
    (hε : 0 < ε) :
    (informationRateAt μ T ε).1 ≤ (informationRate μ T).1 ∧
      (informationRateAt μ T ε).2 ≤ (informationRate μ T).2 := by
  obtain ⟨p, hp⟩ := exists_dyadicRadius_lt hε
  have h := informationRateAt_antitone μ T hp.le
  exact ⟨h.1.trans (le_iSup (fun p ↦ (informationRateAt μ T (dyadicRadius p)).1) p),
    h.2.trans (le_iSup (fun p ↦ (informationRateAt μ T (dyadicRadius p)).2) p)⟩

/-! ### Expected orbit complexity (Proposition 4.6) -/

/-- The test function of Lemma 3.2 is a Borel function: a countable sum of constants times
indicators of open sets. -/
theorem measurable_testFunction (P : Presentation X) {T : X → X} (hT : Continuous T)
    (A : Set ℕ) (μ : Measure X) (ε : ℝ) : Measurable (testFunction P T A μ ε) := by
  refine Measurable.tsum fun n ↦ Measurable.tsum fun i ↦ ?_
  by_cases hn : n = 0
  · simp only [hn, ↓reduceIte]
    exact measurable_const
  · simp only [hn, ↓reduceIte]
    exact measurable_const.mul ((measurable_const.indicator
      (bowen_ball_dense_open T hT n _ ε).measurableSet).div_const _)

/-- Tangent line of the concave binary logarithm at `c > 0`:
`log₂ y ≤ log₂ c + (y - c) / (c ln 2)`. -/
private theorem logb_le_tangent {c y : ℝ} (hc : 0 < c) (hy : 0 < y) :
    Real.logb 2 y ≤ Real.logb 2 c + (y - c) / (c * Real.log 2) := by
  have hl : 0 < Real.log 2 := Real.log_pos one_lt_two
  have h := Real.log_le_sub_one_of_pos (div_pos hy hc)
  rw [Real.log_div hy.ne' hc.ne'] at h
  simp only [Real.logb]
  rw [← sub_le_iff_le_add', ← sub_div, div_le_div_iff₀ hl (mul_pos hc hl)]
  have : y / c - 1 = (y - c) / c := by field_simp
  rw [this] at h
  have h2 : (Real.log y - Real.log c) * c ≤ y - c := by
    rwa [le_div_iff₀ hc] at h
  nlinarith

omit [BorelSpace X] in
/-- Pointwise form of Lemma 3.2 combined with the tangent line of `log₂` at `2`:
`-log₂ μ(B_n(x, 2ε)) + (1/ln 2 - 1) ≤ K_n(x, ε) + 2 log₂ n + t(x) / (2 ln 2)`, where `t` is the
test function, at every point where it is finite. -/
private theorem infoBits_add_le_of_testFunction (P : Presentation X) (T : X → X)
    (hT : Continuous T) (A : Set ℕ) (μ : Measure X) [IsProbabilityMeasure μ] {ε : ℝ}
    (hε : 0 < ε) {n : ℕ} (hn : 1 ≤ n) (x : X) (hx : testFunction P T A μ ε x ≠ ⊤) :
    infoBits (μ (bowenBall T n x (2 * ε))) + ENNReal.ofReal (1 / Real.log 2 - 1) ≤
      (orbitComplexityNat P T A x n ε : ℝ≥0∞) + ENNReal.ofReal (2 * Real.logb 2 n) +
        ENNReal.ofReal (1 / (2 * Real.log 2)) * testFunction P T A μ ε x := by
  set t := testFunction P T A μ ε x with ht
  set q := μ (bowenBall T n x (2 * ε)) with hq
  set K := orbitComplexityNat P T A x n ε with hK
  have h := testFunction_mul_measure_bowenBall_ge P T hT A μ hε x hx hn
  rw [← ht, ← hq, ← hK] at h
  have hl : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hl1 : Real.log 2 < 1 := by
    have := Real.log_lt_sub_one_of_pos two_pos (by norm_num)
    linarith
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hqt : q ≠ ⊤ := measure_ne_top μ _
  have hpos : (0 : ℝ≥0∞) < (2 : ℝ≥0∞)⁻¹ ^ K / (n : ℝ≥0∞) ^ 2 :=
    ENNReal.div_pos (by simp) (by simp)
  have hq0 : q ≠ 0 := by
    rintro h0
    rw [h0, mul_zero] at h
    exact hpos.ne' (le_antisymm h bot_le)
  have ht0 : t ≠ 0 := (testFunction_pos P T hT A μ hε x).ne'
  have htr : 0 < t.toReal := ENNReal.toReal_pos ht0 hx
  have hqr : 0 < q.toReal := ENNReal.toReal_pos hq0 hqt
  -- the real form of Lemma 3.2
  have hreal : (2 : ℝ)⁻¹ ^ K / (n : ℝ) ^ 2 ≤ t.toReal * q.toReal := by
    have := ENNReal.toReal_mono (ENNReal.mul_ne_top hx hqt) h
    simpa [ENNReal.toReal_div, ENNReal.toReal_mul] using this
  have hlog : -Real.logb 2 q.toReal ≤ K + 2 * Real.logb 2 n + Real.logb 2 t.toReal := by
    have h1 := Real.logb_le_logb_of_le one_lt_two (by positivity) hreal
    rw [Real.logb_mul htr.ne' hqr.ne', Real.logb_div (by positivity) (by positivity),
      Real.logb_pow, Real.logb_pow, Real.logb_inv, Real.logb_self_eq_one one_lt_two] at h1
    push_cast at h1
    linarith
  have htan := logb_le_tangent two_pos htr
  rw [Real.logb_self_eq_one one_lt_two] at htan
  have hd : 0 ≤ 1 / Real.log 2 - 1 := by
    rw [sub_nonneg, le_div_iff₀ hl]
    linarith
  have hL : 0 ≤ Real.logb 2 n := Real.logb_nonneg one_lt_two (by exact_mod_cast hn)
  have hI0 : 0 ≤ -Real.logb 2 q.toReal := by
    have hq1 : q.toReal ≤ 1 := by
      have := ENNReal.toReal_mono ENNReal.one_ne_top (prob_le_one (μ := μ) (s := bowenBall T n x
        (2 * ε)))
      rwa [ENNReal.toReal_one] at this
    linarith [Real.logb_nonpos one_lt_two hqr.le hq1]
  rw [infoBits_of_ne hq0, ← ENNReal.ofReal_add hI0 hd, ← ENNReal.ofReal_toReal hx,
    ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_natCast,
    ← ENNReal.ofReal_add (by positivity) (by positivity),
    ← ENNReal.ofReal_add (by positivity) (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  have : (t.toReal - 2) / (2 * Real.log 2) = 1 / (2 * Real.log 2) * t.toReal - 1 / Real.log 2 := by
    field_simp
  linarith

/-- Proposition 4.6, first inequality, for every oracle and every Borel probability measure:
`I_n(μ, 2ε) ≤ ∫ K_n^A(x, T, ε) dμ + 2 log₂ n + 1`. Blueprint node `meas:expected-complexity`. -/
theorem bowenInformation_le_expectedOrbitComplexity (P : Presentation X) (T : X → X)
    (hT : Continuous T) (A : Set ℕ) (μ : Measure X) [IsProbabilityMeasure μ] {ε : ℝ}
    (hε : 0 < ε) {n : ℕ} (hn : 1 ≤ n) :
    bowenInformation μ T n (2 * ε) ≤
      expectedOrbitComplexity P T A μ n ε + ENNReal.ofReal (2 * Real.logb 2 n + 1) := by
  set D := ENNReal.ofReal (1 / Real.log 2 - 1) with hD
  set E := ENNReal.ofReal (2 * Real.logb 2 n) with hE
  set b := ENNReal.ofReal (1 / (2 * Real.log 2)) with hb
  have hl : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hL : 0 ≤ Real.logb 2 n := Real.logb_nonneg one_lt_two (by exact_mod_cast hn)
  have htm := measurable_testFunction P hT A μ ε
  have htint := lintegral_testFunction_lt_two P T hT A μ ε
  have hae : ∀ᵐ x ∂μ, testFunction P T A μ ε x < ⊤ := ae_lt_top htm (htint.trans_le le_top).ne
  have hKm : Measurable fun x ↦ (orbitComplexityNat P T A x n ε : ℝ≥0∞) :=
    measurable_from_nat.comp (measurable_orbitComplexityNat P hT A n ε)
  have hint : bowenInformation μ T n (2 * ε) + D ≤
      expectedOrbitComplexity P T A μ n ε + E + b * 2 := by
    calc bowenInformation μ T n (2 * ε) + D
        = ∫⁻ x, infoBits (μ (bowenBall T n x (2 * ε))) + D ∂μ := by
          rw [lintegral_add_right _ measurable_const, lintegral_const, measure_univ, mul_one,
            bowenInformation]
      _ ≤ ∫⁻ x, (orbitComplexityNat P T A x n ε : ℝ≥0∞) + E +
            b * testFunction P T A μ ε x ∂μ :=
          lintegral_mono_ae (hae.mono fun x hx ↦
            infoBits_add_le_of_testFunction P T hT A μ hε hn x hx.ne)
      _ = expectedOrbitComplexity P T A μ n ε + E + b * ∫⁻ x, testFunction P T A μ ε x ∂μ := by
          have hKE : Measurable fun x ↦ (orbitComplexityNat P T A x n ε : ℝ≥0∞) + E :=
            hKm.add measurable_const
          rw [lintegral_add_left hKE, lintegral_add_left hKm,
            lintegral_const, measure_univ, mul_one, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
            expectedOrbitComplexity]
      _ ≤ expectedOrbitComplexity P T A μ n ε + E + b * 2 := by gcongr
  have hb2 : b * 2 = D + 1 := by
    rw [hb, hD, ← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_one, ← ENNReal.ofReal_add _ zero_le_one]
    · congr 1
      field_simp
      ring
    · rw [sub_nonneg, le_div_iff₀ hl]
      linarith [Real.log_lt_sub_one_of_pos two_pos (by norm_num : (2 : ℝ) ≠ 1)]
  rw [hb2, show expectedOrbitComplexity P T A μ n ε + E + (D + 1) =
    expectedOrbitComplexity P T A μ n ε + E + 1 + D by ring,
    ENNReal.add_le_add_iff_right ENNReal.ofReal_ne_top, add_assoc] at hint
  rwa [ENNReal.ofReal_add (by positivity) zero_le_one, ENNReal.ofReal_one]

/-- Pointwise form of coding by measure combined with the tangent line of `log₂` at
`C = Ī + 2`: with `I_x = -log₂ μ(B_n(x, ε))` and `a = 2 / (C ln 2)`,
`K_n(x, 6ε) + a Ī ≤ I_x + 2 log₂ n + 2 log₂ C + c + a I_x`. -/
private theorem orbitComplexityNat_add_le_of_coding {K I E : ℝ} {c : ℕ} (hI : 0 ≤ I)
    (hK : K ≤ I + E + 2 * Real.logb 2 (I + 2) + c) (Ib : ℝ) (hIb : 0 ≤ Ib) :
    K + 2 / ((Ib + 2) * Real.log 2) * Ib ≤
      I + E + 2 * Real.logb 2 (Ib + 2) + c + 2 / ((Ib + 2) * Real.log 2) * I := by
  have htan := logb_le_tangent (c := Ib + 2) (y := I + 2) (by positivity) (by positivity)
  have : (I + 2 - (Ib + 2)) / ((Ib + 2) * Real.log 2) =
      1 / ((Ib + 2) * Real.log 2) * I - 1 / ((Ib + 2) * Real.log 2) * Ib := by ring
  have h2 : 2 / ((Ib + 2) * Real.log 2) = 2 * (1 / ((Ib + 2) * Real.log 2)) := by ring
  rw [h2]
  linarith

/-- Proposition 4.6, second inequality: for `A` admissible for `(X, d, T, μ)` and rational
`ε > 0` there is `c` with
`∫ K_n^A(x, T, 6ε) dμ ≤ I_n(μ, ε) + 2 log₂ n + 2 log₂ (I_n(μ, ε) + 2) + c` for all `n ≥ 1`.
Blueprint node `meas:expected-complexity`. -/
theorem expectedOrbitComplexity_le_bowenInformation (P : Presentation X) (T : X → X)
    (hT : Continuous T) (A : Set ℕ) (μ : Measure X) [IsProbabilityMeasure μ]
    (hA : IsMeasureAdmissible P T μ A) (ε : ℚ) (hε : 0 < ε) :
    ∃ c : ℕ, ∀ n : ℕ, 1 ≤ n →
      expectedOrbitComplexity P T A μ n (6 * (ε : ℝ)) ≤
        bowenInformation μ T n ε + ENNReal.ofReal (2 * Real.logb 2 n) +
          ENNReal.ofReal (2 * Real.logb 2 ((bowenInformation μ T n ε).toReal + 2)) + c := by
  obtain ⟨c, hc⟩ := coding_by_measure_info P T hT A μ prob_le_one hA ε hε
  refine ⟨c, fun n hn ↦ ?_⟩
  set I := bowenInformation μ T n ε with hIdef
  rcases eq_or_ne I ⊤ with hItop | hItop
  · simp [hItop]
  set Ib := I.toReal with hIb
  have hIb0 : 0 ≤ Ib := ENNReal.toReal_nonneg
  have hl : 0 < Real.log 2 := Real.log_pos one_lt_two
  set a : ℝ := 2 / ((Ib + 2) * Real.log 2) with ha
  have ha0 : 0 ≤ a := by positivity
  have hL : 0 ≤ Real.logb 2 n := Real.logb_nonneg one_lt_two (by exact_mod_cast hn)
  have hC : 0 ≤ Real.logb 2 (Ib + 2) := Real.logb_nonneg one_lt_two (by linarith)
  set E := ENNReal.ofReal (2 * Real.logb 2 n) with hE
  set F := ENNReal.ofReal (2 * Real.logb 2 (Ib + 2)) with hF
  set f : X → ℝ≥0∞ := fun x ↦ infoBits (μ (bowenBall T n x (ε : ℝ))) with hfdef
  have hf : Measurable f :=
    infoBits_antitone.measurable.comp (measurable_measure_bowenBall μ hT n _)
  have hKm : Measurable fun x ↦ (orbitComplexityNat P T A x n (6 * (ε : ℝ)) : ℝ≥0∞) :=
    measurable_from_nat.comp (measurable_orbitComplexityNat P hT A n _)
  have hpt : ∀ x, (orbitComplexityNat P T A x n (6 * (ε : ℝ)) : ℝ≥0∞) + ENNReal.ofReal (a * Ib) ≤
      f x + E + F + c + ENNReal.ofReal a * f x := by
    intro x
    rcases eq_or_ne (μ (bowenBall T n x (ε : ℝ))) 0 with h0 | h0
    · simp [hfdef, h0]
    have hqr : 0 < (μ (bowenBall T n x (ε : ℝ))).toReal :=
      ENNReal.toReal_pos h0 (measure_ne_top _ _)
    have hq1 : (μ (bowenBall T n x (ε : ℝ))).toReal ≤ 1 := by
      have := ENNReal.toReal_mono ENNReal.one_ne_top
        (prob_le_one (μ := μ) (s := bowenBall T n x (ε : ℝ)))
      rwa [ENNReal.toReal_one] at this
    have hI0 : 0 ≤ -Real.logb 2 (μ (bowenBall T n x (ε : ℝ))).toReal := by
      linarith [Real.logb_nonpos one_lt_two hqr.le hq1]
    have key := orbitComplexityNat_add_le_of_coding hI0 (hc x n hn h0) Ib hIb0
    simp only [hfdef, infoBits_of_ne h0]
    rw [← ENNReal.ofReal_mul ha0, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_natCast c,
      ← ENNReal.ofReal_add (by positivity) (by positivity),
      ← ENNReal.ofReal_add (by positivity) (by positivity),
      ← ENNReal.ofReal_add (by positivity) (by positivity),
      ← ENNReal.ofReal_add (by positivity) (by positivity),
      ← ENNReal.ofReal_add (by positivity) (by positivity)]
    exact ENNReal.ofReal_le_ofReal key
  have hint : expectedOrbitComplexity P T A μ n (6 * (ε : ℝ)) + ENNReal.ofReal (a * Ib) ≤
      I + E + F + c + ENNReal.ofReal (a * Ib) := by
    calc expectedOrbitComplexity P T A μ n (6 * (ε : ℝ)) + ENNReal.ofReal (a * Ib)
        = ∫⁻ x, (orbitComplexityNat P T A x n (6 * (ε : ℝ)) : ℝ≥0∞) +
            ENNReal.ofReal (a * Ib) ∂μ := by
          rw [lintegral_add_right _ measurable_const, lintegral_const, measure_univ, mul_one,
            expectedOrbitComplexity]
      _ ≤ ∫⁻ x, f x + E + F + c + ENNReal.ofReal a * f x ∂μ := lintegral_mono hpt
      _ = I + E + F + c + ENNReal.ofReal a * I := by
          rw [lintegral_add_right _ (hf.const_mul _), lintegral_add_right _ measurable_const,
            lintegral_add_right _ measurable_const, lintegral_add_right _ measurable_const,
            lintegral_const_mul _ hf]
          simp only [lintegral_const, measure_univ, mul_one, hIdef, bowenInformation, hfdef]
      _ = I + E + F + c + ENNReal.ofReal (a * Ib) := by
          rw [ENNReal.ofReal_mul ha0, hIb, ENNReal.ofReal_toReal hItop]
  exact (ENNReal.add_le_add_iff_right ENNReal.ofReal_ne_top).1 hint

/-! ### Comparison lemmas for limits inferior and superior -/

/-- If `a n ≤ b n + d n` eventually with `d n → 0`, then `liminf a ≤ liminf b` and
`limsup a ≤ limsup b`. -/
private theorem liminf_limsup_le_of_le_add' {a b d : ℕ → ℝ≥0∞} (hd : Tendsto d atTop (𝓝 0))
    (h : ∀ᶠ n in atTop, a n ≤ b n + d n) :
    liminf a atTop ≤ liminf b atTop ∧ limsup a atTop ≤ limsup b atTop :=
  ⟨liminf_le_liminf_of_le_add_tendsto_zero h hd, limsup_le_limsup_of_le_add_tendsto_zero h hd⟩

/-- Threshold comparison: if for every real `s > 0` there is an error `d → 0` such that
eventually `a n < s` implies `b n ≤ s + d n`, then `liminf b ≤ liminf a` and
`limsup b ≤ limsup a`. -/
private theorem liminf_limsup_le_of_forall_lt' {a b : ℕ → ℝ≥0∞}
    (h : ∀ s : ℝ, 0 < s → ∃ d : ℕ → ℝ≥0∞, Tendsto d atTop (𝓝 0) ∧
      ∀ᶠ n in atTop, a n < ENNReal.ofReal s → b n ≤ ENNReal.ofReal s + d n) :
    liminf b atTop ≤ liminf a atTop ∧ limsup b atTop ≤ limsup a atTop := by
  have key : ∀ (t : ℝ≥0∞) (η : NNReal), 0 < η → t < ⊤ →
      ∃ s : ℝ, 0 < s ∧ t < ENNReal.ofReal s ∧ ∃ d : ℕ → ℝ≥0∞, (∀ᶠ n in atTop, d n < η / 2) ∧
        (ENNReal.ofReal s + η / 2 = t + η) ∧
        ∀ᶠ n in atTop, a n < ENNReal.ofReal s → b n ≤ ENNReal.ofReal s + d n := by
    intro t η hη ht
    have hη2 : (0 : ℝ) < (η : ℝ) / 2 := by positivity
    refine ⟨t.toReal + η / 2, by positivity, ?_, ?_⟩
    · rw [ENNReal.lt_ofReal_iff_toReal_lt ht.ne]
      linarith
    obtain ⟨d, hd, hev⟩ := h (t.toReal + η / 2) (by positivity)
    have hpos : (0 : ℝ≥0∞) < (η : ℝ≥0∞) / 2 :=
      ENNReal.div_pos (by exact_mod_cast hη.ne') (by norm_num)
    refine ⟨d, (tendsto_order.1 hd).2 _ hpos, ?_, hev⟩
    rw [ENNReal.ofReal_add ENNReal.toReal_nonneg hη2.le, ENNReal.ofReal_toReal ht.ne, add_assoc]
    congr 1
    rw [ENNReal.ofReal_div_of_pos two_pos, ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_ofNat,
      ENNReal.add_halves]
  constructor
  · refine ENNReal.le_of_forall_pos_le_add fun η hη ht ↦ ?_
    obtain ⟨s, -, hs, d, hd, heq, hev⟩ := key _ η hη ht
    rw [← heq]
    refine liminf_le_of_frequently_le' ?_
    have hfr := frequently_lt_of_liminf_lt (by isBoundedDefault) hs
    refine (hfr.and_eventually (hd.and hev)).mono fun n ⟨han, hdn, himp⟩ ↦ ?_
    exact (himp han).trans (by gcongr)
  · refine ENNReal.le_of_forall_pos_le_add fun η hη ht ↦ ?_
    obtain ⟨s, -, hs, d, hd, heq, hev⟩ := key _ η hη ht
    rw [← heq]
    refine limsup_le_of_le (by isBoundedDefault) ?_
    have hfr := eventually_lt_of_limsup_lt hs (by isBoundedDefault)
    filter_upwards [hfr, hd, hev] with n han hdn himp
    exact (himp han).trans (by gcongr)

/-- `log₂ n / n → 0`. -/
private theorem tendsto_logb_div_nat' :
    Tendsto (fun n : ℕ ↦ Real.logb 2 n / n) atTop (𝓝 0) := by
  have h := (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp
    tendsto_natCast_atTop_atTop
  have h2 := h.div_const (Real.log 2)
  simp only [zero_div] at h2
  refine h2.congr fun n ↦ ?_
  simp [Real.logb]
  ring

/-- An error term `(C + D log₂ n) / n` tends to zero. -/
private theorem tendsto_ofReal_err' (C D : ℝ) :
    Tendsto (fun n : ℕ ↦ ENNReal.ofReal ((C + D * Real.logb 2 n) / n)) atTop (𝓝 0) := by
  rw [← ENNReal.ofReal_zero]
  refine ENNReal.tendsto_ofReal ?_
  have h1 := tendsto_const_div_atTop_nhds_zero_nat C
  have h2 := tendsto_logb_div_nat'.const_mul D
  rw [mul_zero] at h2
  simpa [add_div, mul_div_assoc] using h1.add h2

/-- `ofReal r / n = ofReal (r / n)` for `n ≥ 1`. -/
private theorem ofReal_div_natCast {r : ℝ} {n : ℕ} (hn : 1 ≤ n) :
    ENNReal.ofReal r / n = ENNReal.ofReal (r / n) := by
  rw [ENNReal.ofReal_div_of_pos (by exact_mod_cast hn), ENNReal.ofReal_natCast]

omit [MeasurableSpace X] [BorelSpace X] in
/-- At positive radii, the natural orbit complexity is antitone in the radius. -/
theorem orbitComplexityNat_antitone_radius (P : Presentation X) {T : X → X}
    (hT : Continuous T) (A : Set ℕ) (x : X) (n : ℕ) {r r' : ℝ} (hr : 0 < r) (h : r ≤ r') :
    orbitComplexityNat P T A x n r' ≤ orbitComplexityNat P T A x n r := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [orbitComplexityNat, orbitComplexity, bowen_ball_dense_zero]
  obtain ⟨i, hi, hK⟩ := entropiesAndOrbitComplexities_attained P T hT A x n hn r hr
  calc orbitComplexityNat P T A x n r' ≤ oracleNatComplexity A i :=
        orbitComplexityNat_le_of_mem P T A (bowenBall_subset_of_le T n x h hi)
    _ = orbitComplexityNat P T A x n r := by rw [orbitComplexityNat, hK, ENat.toNat_natCast]

omit [BorelSpace X] in
/-- At positive radii, the expected orbit complexity is antitone in the radius. -/
theorem expectedOrbitComplexity_antitone_radius (P : Presentation X) {T : X → X}
    (hT : Continuous T) (A : Set ℕ) (μ : Measure X) (n : ℕ) {r r' : ℝ} (hr : 0 < r)
    (h : r ≤ r') :
    expectedOrbitComplexity P T A μ n r' ≤ expectedOrbitComplexity P T A μ n r :=
  lintegral_mono fun x ↦ Nat.cast_le.2 (orbitComplexityNat_antitone_radius P hT A x n hr h)

/-- Proposition 4.6, consequence: the information rates are the growth rates of the expected
orbit complexity relative to any admissible oracle.
Blueprint node `meas:expected-complexity`. -/
theorem informationRate_eq_expectedOrbitComplexity_rate (P : Presentation X) (T : X → X)
    (hT : Continuous T) (A : Set ℕ) (μ : Measure X) [IsProbabilityMeasure μ]
    (hA : IsMeasureAdmissible P T μ A) :
    informationRate μ T =
      (⨆ p : ℕ, liminf (fun n : ℕ ↦
          expectedOrbitComplexity P T A μ n (dyadicRadius p) / n) atTop,
        ⨆ p : ℕ, limsup (fun n : ℕ ↦
          expectedOrbitComplexity P T A μ n (dyadicRadius p) / n) atTop) := by
  set Er : ℕ → ℝ≥0∞ × ℝ≥0∞ := fun p ↦
    (liminf (fun n : ℕ ↦ expectedOrbitComplexity P T A μ n (dyadicRadius p) / n) atTop,
      limsup (fun n : ℕ ↦ expectedOrbitComplexity P T A μ n (dyadicRadius p) / n) atTop)
    with hEr
  -- the information rate at scale `2^{-p}` is at most the complexity rate at `2^{-(p+1)}`
  have hA1 : ∀ p : ℕ, (informationRateAt μ T (dyadicRadius p)).1 ≤ (Er (p + 1)).1 ∧
      (informationRateAt μ T (dyadicRadius p)).2 ≤ (Er (p + 1)).2 := by
    intro p
    have heq : dyadicRadius p = 2 * dyadicRadius (p + 1) := by
      rw [dyadicRadius, dyadicRadius, pow_succ]
      ring
    refine liminf_limsup_le_of_le_add' (tendsto_ofReal_err' 1 2) ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    have h := bowenInformation_le_expectedOrbitComplexity P T hT A μ (dyadicRadius_pos (p + 1)) hn
    rw [← heq] at h
    calc bowenInformation μ T n (dyadicRadius p) / n
        ≤ (expectedOrbitComplexity P T A μ n (dyadicRadius (p + 1)) +
            ENNReal.ofReal (2 * Real.logb 2 n + 1)) / n := by gcongr
      _ = _ := by
          rw [ENNReal.add_div, ofReal_div_natCast hn]
          ring_nf
  -- the complexity rate at scale `2^{-p}` is at most the information rate at `2^{-(p+3)}`
  have hA2 : ∀ p : ℕ, (Er p).1 ≤ (informationRate μ T).1 ∧ (Er p).2 ≤ (informationRate μ T).2 := by
    intro p
    set ε : ℚ := (2 : ℚ)⁻¹ ^ (p + 3) with hεdef
    have hε : 0 < ε := by positivity
    have hε' : (0 : ℝ) < ε := by exact_mod_cast hε
    have h6 : 6 * (ε : ℝ) ≤ dyadicRadius p := by
      have h0 : (0 : ℝ) ≤ (2 : ℝ)⁻¹ ^ p := by positivity
      rw [hεdef, dyadicRadius]
      push_cast
      rw [pow_add]
      norm_num
      linarith
    obtain ⟨c, hc⟩ := expectedOrbitComplexity_le_bowenInformation P T hT A μ hA ε hε
    have hle := liminf_limsup_le_of_forall_lt'
      (a := fun n : ℕ ↦ bowenInformation μ T n ε / n)
      (b := fun n : ℕ ↦ expectedOrbitComplexity P T A μ n (dyadicRadius p) / n) ?_
    · have h3 := informationRateAt_le_informationRate μ T hε'
      exact ⟨hle.1.trans h3.1, hle.2.trans h3.2⟩
    intro s hs
    refine ⟨fun n ↦ ENNReal.ofReal ((c + 2 * Real.logb 2 (s + 2) + 4 * Real.logb 2 n) / n),
      tendsto_ofReal_err' _ _, ?_⟩
    filter_upwards [eventually_ge_atTop 1] with n hn hlt
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    have hnE : (n : ℝ≥0∞) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
    set I := bowenInformation μ T n ε with hI
    have hlt' : I < ENNReal.ofReal (s * n) := by
      rw [ENNReal.div_lt_iff (Or.inl hnE) (Or.inl (ENNReal.natCast_ne_top n))] at hlt
      rwa [ENNReal.ofReal_mul hs.le, ENNReal.ofReal_natCast]
    have hItop : I ≠ ⊤ := (hlt'.trans ENNReal.ofReal_lt_top).ne
    have hIr : I.toReal < s * n := (ENNReal.lt_ofReal_iff_toReal_lt hItop).1 hlt'
    have hI0 : 0 ≤ I.toReal := ENNReal.toReal_nonneg
    have hL : 0 ≤ Real.logb 2 n := Real.logb_nonneg one_lt_two (by exact_mod_cast hn)
    have hlog : Real.logb 2 (I.toReal + 2) ≤ Real.logb 2 (s + 2) + Real.logb 2 n := by
      rw [← Real.logb_mul (by positivity) hn0.ne']
      refine Real.logb_le_logb_of_le one_lt_two (by positivity) ?_
      have : (1 : ℝ) ≤ n := by exact_mod_cast hn
      nlinarith
    have hlog0 : 0 ≤ Real.logb 2 (I.toReal + 2) := Real.logb_nonneg one_lt_two (by linarith)
    have hE := (expectedOrbitComplexity_antitone_radius P hT A μ n (by positivity) h6).trans
      (hc n hn)
    rw [← hI] at hE
    have hE' : expectedOrbitComplexity P T A μ n (dyadicRadius p) ≤
        ENNReal.ofReal (s * n + (c + 2 * Real.logb 2 (s + 2) + 4 * Real.logb 2 n)) := by
      have heq : I + ENNReal.ofReal (2 * Real.logb 2 n) +
          ENNReal.ofReal (2 * Real.logb 2 (I.toReal + 2)) + c = ENNReal.ofReal
            (I.toReal + 2 * Real.logb 2 n + 2 * Real.logb 2 (I.toReal + 2) + c) := by
        rw [ENNReal.ofReal_add (by linarith) (by positivity),
          ENNReal.ofReal_add (by linarith) (by linarith),
          ENNReal.ofReal_add hI0 (by linarith), ENNReal.ofReal_toReal hItop,
          ENNReal.ofReal_natCast]
      rw [heq] at hE
      refine hE.trans (ENNReal.ofReal_le_ofReal ?_)
      linarith
    calc expectedOrbitComplexity P T A μ n (dyadicRadius p) / n
        ≤ ENNReal.ofReal (s * n + (c + 2 * Real.logb 2 (s + 2) + 4 * Real.logb 2 n)) / n := by
          gcongr
      _ = ENNReal.ofReal (s + (c + 2 * Real.logb 2 (s + 2) + 4 * Real.logb 2 n) / n) := by
          rw [ofReal_div_natCast hn]
          congr 1
          field_simp
      _ ≤ _ := ENNReal.ofReal_add_le
  refine Prod.ext (le_antisymm ?_ ?_) (le_antisymm ?_ ?_)
  · exact iSup_le fun p ↦ (hA1 p).1.trans (le_iSup (fun q ↦ (Er q).1) (p + 1))
  · exact iSup_le fun p ↦ (hA2 p).1
  · exact iSup_le fun p ↦ (hA1 p).2.trans (le_iSup (fun q ↦ (Er q).2) (p + 1))
  · exact iSup_le fun p ↦ (hA2 p).2

/-! ### Comparison with the Feng–Huang entropies (Proposition 4.7) -/

/-- The mean of the finite-time local entropy rate is the normalized mean information:
`∫ f_n dμ = I_n(μ, ε) / n`. -/
theorem lintegral_localEntropyRate {T : X → X} (hT : Continuous T) (μ : Measure X) (n : ℕ)
    (ε : ℝ) : ∫⁻ x, localEntropyRate μ T x n ε ∂μ = bowenInformation μ T n ε / n := by
  simp only [localEntropyRate, div_eq_mul_inv]
  exact lintegral_mul_const _
    (infoBits_antitone.measurable.comp (measurable_measure_bowenBall μ hT n ε))

/-- Proposition 4.7: `h̲_μ(T) ≤ H̲_μ(T)` (Fatou's lemma and monotone convergence in the
scale). Blueprint node `meas:comparison`. -/
theorem measureEntropy_fst_le_informationRate_fst {T : X → X} (hT : Continuous T)
    (μ : Measure X) : (measureEntropy μ T).1 ≤ (informationRate μ T).1 := by
  have hmono : Monotone fun p x ↦ (localEntropyAt μ T x (dyadicRadius p)).1 :=
    fun p q hpq x ↦ (localEntropyAt_antitone μ T x (dyadicRadius_antitone hpq)).1
  simp only [measureEntropy, localEntropy, informationRate]
  rw [lintegral_iSup (fun p ↦ (measurable_localEntropyAt μ hT (dyadicRadius p)).fst) hmono]
  refine iSup_mono fun p ↦ ?_
  calc ∫⁻ x, (localEntropyAt μ T x (dyadicRadius p)).1 ∂μ
      ≤ liminf (fun n ↦ ∫⁻ x, localEntropyRate μ T x n (dyadicRadius p) ∂μ) atTop :=
        lintegral_liminf_le fun n ↦ measurable_localEntropyRate μ hT n _
    _ = (informationRateAt μ T (dyadicRadius p)).1 := by
        simp only [lintegral_localEntropyRate hT, informationRateAt]

omit [BorelSpace X] in
/-- Proposition 4.7: `H̲_μ(T) ≤ H̄_μ(T)`. Blueprint node `meas:comparison`. -/
theorem informationRate_fst_le_snd (μ : Measure X) (T : X → X) :
    (informationRate μ T).1 ≤ (informationRate μ T).2 :=
  iSup_mono fun _ ↦ liminf_le_limsup

omit [BorelSpace X] in
/-- Counting Bowen balls on a compact space: there is `N` such that for every `n` and every
threshold `q`, the set of points whose Bowen ball `B_n(x, T, ε)` has measure less than `q` has
measure at most `N^n q`. (Cover `X` by `N` open balls of radius `ε/2`; the itinerary cells of
this cover have Bowen diameter less than `ε`, so a cell meeting the set has measure less than
`q`.) -/
theorem exists_measure_setOf_measure_bowenBall_lt_le [CompactSpace X] (T : X → X)
    (μ : Measure X) {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ (n : ℕ) (q : ℝ≥0∞),
      μ {x | μ (bowenBall T n x ε) < q} ≤ ((N ^ n : ℕ) : ℝ≥0∞) * q := by
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover (fun z : X ↦ Metric.ball z (ε / 2))
    (fun _ ↦ Metric.isOpen_ball) fun x _ ↦ mem_iUnion.2 ⟨x, Metric.mem_ball_self (by linarith)⟩
  have hcov : ∀ y : X, ∃ c : s, y ∈ Metric.ball (c : X) (ε / 2) := fun y ↦ by
    have := hs (mem_univ y)
    simp only [mem_iUnion, exists_prop] at this
    obtain ⟨c, hc, hy⟩ := this
    exact ⟨⟨c, hc⟩, hy⟩
  refine ⟨s.card, fun n q ↦ ?_⟩
  set C : (Fin n → s) → Set X := fun w ↦ {x | ∀ k : Fin n, T^[k] x ∈ Metric.ball (w k : X) (ε / 2)}
    with hC
  have hmem : ∀ x, x ∈ C (fun k ↦ (hcov (T^[k] x)).choose) := fun x k ↦
    (hcov (T^[k] x)).choose_spec
  have hsub : ∀ w x, x ∈ C w → C w ⊆ bowenBall T n x ε := by
    intro w x hx y hy
    refine mem_bowenBall_iff.2 fun k hk ↦ ?_
    have h1 := hx ⟨k, hk⟩
    have h2 := hy ⟨k, hk⟩
    simp only [Metric.mem_ball] at h1 h2
    calc dist (T^[k] x) (T^[k] y) ≤ dist (T^[k] x) (w ⟨k, hk⟩) + dist (T^[k] y) (w ⟨k, hk⟩) :=
          dist_triangle_right _ _ _
      _ < ε / 2 + ε / 2 := add_lt_add h1 h2
      _ = ε := by ring
  have hU : {x | μ (bowenBall T n x ε) < q} ⊆ ⋃ w, ⋃ (_ : μ (C w) < q), C w := by
    intro x hx
    refine mem_iUnion.2 ⟨_, mem_iUnion.2 ⟨?_, hmem x⟩⟩
    exact (measure_mono (hsub _ x (hmem x))).trans_lt hx
  calc μ {x | μ (bowenBall T n x ε) < q}
      ≤ ∑ w, μ (⋃ (_ : μ (C w) < q), C w) := (measure_mono hU).trans (measure_iUnion_fintype_le _ _)
    _ ≤ ∑ _w : Fin n → s, q := by
        refine Finset.sum_le_sum fun w _ ↦ ?_
        by_cases hw : μ (C w) < q
        · simpa [hw] using hw.le
        · simp [hw]
    _ = ((s.card ^ n : ℕ) : ℝ≥0∞) * q := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
          Fintype.card_coe, nsmul_eq_mul]

/-- Uniform integrability on a compact space: for every `ε > 0` there is `b` such that for
all `M > b` and `n ≥ 1` the part of the mean of `f_n^ε = -(1/n) log₂ μ(B_n(x, T, ε))` above
the level `M` is at most `(M + 1) 2^{-(M - b) n}`. Blueprint node `meas:comparison`. -/
theorem exists_setLIntegral_localEntropyRate_le [CompactSpace X] {T : X → X}
    (hT : Continuous T) (μ : Measure X) [IsProbabilityMeasure μ] {ε : ℝ} (hε : 0 < ε) :
    ∃ b : ℝ, 0 ≤ b ∧ ∀ (M : ℝ), b < M → ∀ n : ℕ, 1 ≤ n →
      ∫⁻ x in {x | ENNReal.ofReal M < localEntropyRate μ T x n ε},
          localEntropyRate μ T x n ε ∂μ ≤
        ENNReal.ofReal ((M + 1) * (2 : ℝ) ^ (-(M - b) * n)) := by
  obtain ⟨N, hN⟩ := exists_measure_setOf_measure_bowenBall_lt_le T μ hε
  set L : ℝ := N + 1 with hL
  have hL0 : 0 < L := by positivity
  have hL1 : 1 ≤ L := by simp [hL]
  refine ⟨Real.logb 2 L + 1, by
    linarith [Real.logb_nonneg one_lt_two hL1], fun M hM n hn ↦ ?_⟩
  have hlogL := Real.logb_nonneg one_lt_two hL1
  have hM0 : 0 ≤ M := by linarith
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  set f : X → ℝ≥0∞ := fun x ↦ localEntropyRate μ T x n ε with hfdef
  have hf : Measurable f := measurable_localEntropyRate μ hT n ε
  -- the tail bound `μ {f > r} ≤ N^n 2^{-rn}`
  have htail : ∀ r : ℝ, 0 ≤ r → μ {x | ENNReal.ofReal r < f x} ≤
      ((N ^ n : ℕ) : ℝ≥0∞) * ENNReal.ofReal ((2 : ℝ) ^ (-(r * n))) := by
    intro r hr
    refine (measure_mono fun x hx ↦ ?_).trans (hN n _)
    simp only [mem_ofPred_eq] at hx ⊢
    by_contra hge
    have h1 := infoBits_le_of_rpow_le (by positivity) (not_lt.1 hge)
    have h2 : f x ≤ ENNReal.ofReal r := by
      calc f x ≤ ENNReal.ofReal (r * n) / n := ENNReal.div_le_div_right h1 _
        _ = ENNReal.ofReal r := by
          rw [ofReal_div_natCast hn, mul_div_assoc, div_self hn0.ne', mul_one]
    exact (not_lt.2 h2) hx
  set S : Set X := {x | ENNReal.ofReal M < f x} with hS
  set Sj : ℕ → Set X := fun j ↦ {x | ENNReal.ofReal (M + j) < f x} with hSj
  have hSm : MeasurableSet S := measurableSet_lt measurable_const hf
  have hSjm : ∀ j, MeasurableSet (Sj j) := fun j ↦ measurableSet_lt measurable_const hf
  -- pointwise: `f ≤ M + ∑_j 1_{f > M + j}`
  have hpt : ∀ x, f x ≤ ENNReal.ofReal M + ∑' j, (Sj j).indicator 1 x := by
    intro x
    rcases eq_or_ne (f x) ⊤ with htop | htop
    · have : ∀ j, (Sj j).indicator (1 : X → ℝ≥0∞) x = 1 := fun j ↦ by
        simp [hSj, htop]
      simp only [this, ENNReal.tsum_const_eq_top_of_ne_zero one_ne_zero, add_top, le_top]
    set k := ⌈(f x).toReal - M⌉₊ with hk
    have hone : ∀ j ∈ Finset.range k, (Sj j).indicator (1 : X → ℝ≥0∞) x = 1 := by
      intro j hj
      have hj' : (j : ℝ) < (f x).toReal - M := Nat.lt_ceil.1 (Finset.mem_range.1 hj)
      have hx : x ∈ Sj j := by
        simp only [hSj, mem_ofPred_eq]
        rw [ENNReal.ofReal_lt_iff_lt_toReal (by positivity) htop]
        linarith
      simp [hx]
    have hsum : (k : ℝ≥0∞) ≤ ∑' j, (Sj j).indicator 1 x := by
      calc (k : ℝ≥0∞) = ∑ j ∈ Finset.range k, (Sj j).indicator (1 : X → ℝ≥0∞) x := by
            rw [Finset.sum_congr rfl hone]
            simp
        _ ≤ _ := ENNReal.sum_le_tsum _
    calc f x = ENNReal.ofReal ((f x).toReal) := (ENNReal.ofReal_toReal htop).symm
      _ ≤ ENNReal.ofReal (M + k) := by
          refine ENNReal.ofReal_le_ofReal ?_
          have := Nat.le_ceil ((f x).toReal - M)
          linarith
      _ = ENNReal.ofReal M + k := by
          rw [ENNReal.ofReal_add hM0 (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
      _ ≤ _ := by gcongr
  set Q : ℝ≥0∞ := ((N ^ n : ℕ) : ℝ≥0∞) * ENNReal.ofReal ((2 : ℝ) ^ (-(M * n))) with hQ
  have hSj_le : ∀ j : ℕ, μ (Sj j) ≤ Q * (2 : ℝ≥0∞)⁻¹ ^ j := by
    intro j
    refine (htail (M + j) (by positivity)).trans ?_
    rw [hQ, mul_assoc]
    gcongr
    rw [← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_inv_of_pos two_pos,
      ← ENNReal.ofReal_pow (by norm_num), ← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    have h1 : (2 : ℝ) ^ (-((M + j) * n)) = 2 ^ (-(M * n)) * 2 ^ (-((j : ℝ) * n)) := by
      rw [← Real.rpow_add two_pos]
      ring_nf
    have h2 : (2 : ℝ) ^ (-((j : ℝ) * n)) ≤ (2 : ℝ)⁻¹ ^ j := by
      rw [inv_pow, ← Real.rpow_natCast, ← Real.rpow_neg zero_le_two]
      refine Real.rpow_le_rpow_of_exponent_le one_le_two ?_
      have : (1 : ℝ) ≤ n := by exact_mod_cast hn
      have : (0 : ℝ) ≤ j := Nat.cast_nonneg j
      nlinarith
    rw [h1]
    exact mul_le_mul_of_nonneg_left h2 (by positivity)
  have hint : ∫⁻ x in S, f x ∂μ ≤ Q * (ENNReal.ofReal M + 2) := by
    calc ∫⁻ x in S, f x ∂μ ≤ ∫⁻ x in S, ENNReal.ofReal M + ∑' j, (Sj j).indicator 1 x ∂μ :=
          lintegral_mono fun x ↦ hpt x
      _ = ENNReal.ofReal M * μ S + ∑' j, μ.restrict S (Sj j) := by
          rw [lintegral_add_left measurable_const, lintegral_const, Measure.restrict_apply_univ,
            lintegral_tsum fun j ↦ (measurable_one.indicator (hSjm j)).aemeasurable]
          simp_rw [lintegral_indicator_one (hSjm _)]
      _ ≤ ENNReal.ofReal M * Q + ∑' j : ℕ, Q * (2 : ℝ≥0∞)⁻¹ ^ j := by
          gcongr with j
          · exact htail M hM0
          · exact (Measure.restrict_apply_le _ _).trans (hSj_le j)
      _ = Q * (ENNReal.ofReal M + 2) := by
          rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric_two]
          ring
  refine hint.trans ?_
  -- the arithmetic
  have hNL : ((N ^ n : ℕ) : ℝ≥0∞) ≤ ENNReal.ofReal (L ^ n) := by
    rw [← ENNReal.ofReal_natCast]
    refine ENNReal.ofReal_le_ofReal ?_
    push_cast
    exact pow_le_pow_left₀ (Nat.cast_nonneg _) (by simp [hL]) n
  have hpow : (2 : ℝ) ^ (-(M - (Real.logb 2 L + 1)) * n) =
      L ^ n * 2 ^ (-(M * n)) * 2 ^ n := by
    have e : -(M - (Real.logb 2 L + 1)) * n = Real.logb 2 L * n + -(M * n) + n := by ring
    rw [e, Real.rpow_add two_pos, Real.rpow_add two_pos, Real.rpow_mul zero_le_two,
      Real.rpow_logb two_pos (by norm_num) hL0, Real.rpow_natCast, Real.rpow_natCast]
  have h2n : (2 : ℝ) ≤ 2 ^ n := by
    calc (2 : ℝ) = 2 ^ 1 := (pow_one 2).symm
      _ ≤ 2 ^ n := pow_le_pow_right₀ one_le_two hn
  calc Q * (ENNReal.ofReal M + 2)
      ≤ ENNReal.ofReal (L ^ n) * ENNReal.ofReal ((2 : ℝ) ^ (-(M * n))) *
          ENNReal.ofReal (M + 2) := by
        rw [hQ, ENNReal.ofReal_add hM0 zero_le_two, ENNReal.ofReal_ofNat]
        gcongr
    _ = ENNReal.ofReal (L ^ n * 2 ^ (-(M * n)) * (M + 2)) := by
        rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity)]
    _ ≤ _ := by
        refine ENNReal.ofReal_le_ofReal ?_
        rw [hpow]
        have hA : 0 ≤ L ^ n * (2 : ℝ) ^ (-(M * n)) := by positivity
        have hM2 : M + 2 ≤ (M + 1) * 2 ^ n := by nlinarith
        have := mul_le_mul_of_nonneg_left hM2 hA
        linarith

/-- Proposition 4.7 at a fixed scale, on a compact space: `H̄_μ(T, ε) ≤ ∫ h̄_μ(T, x, ε) dμ`.
Blueprint node `meas:comparison`. -/
theorem informationRateAt_snd_le_lintegral_localEntropyAt [CompactSpace X] {T : X → X}
    (hT : Continuous T) (μ : Measure X) [IsProbabilityMeasure μ] {ε : ℝ} (hε : 0 < ε) :
    (informationRateAt μ T ε).2 ≤ ∫⁻ x, (localEntropyAt μ T x ε).2 ∂μ := by
  obtain ⟨b, -, hb⟩ := exists_setLIntegral_localEntropyRate_le hT μ hε
  set M : ℝ := b + 1 with hMdef
  set g : ℕ → X → ℝ≥0∞ := fun n x ↦ min (localEntropyRate μ T x n ε) (ENNReal.ofReal M)
    with hgdef
  have hg : ∀ n, Measurable (g n) := fun n ↦
    (measurable_localEntropyRate μ hT n ε).min measurable_const
  set d : ℕ → ℝ≥0∞ := fun n ↦ ENNReal.ofReal ((M + 1) * (2 : ℝ) ^ (-(M - b) * n)) with hd
  have hdlim : Tendsto d atTop (𝓝 0) := by
    have h : ∀ n : ℕ, (M + 1) * (2 : ℝ) ^ (-(M - b) * n) = (M + 1) * (2⁻¹ : ℝ) ^ n := by
      intro n
      rw [hMdef, show -(b + 1 - b) * (n : ℝ) = -(n : ℝ) by ring, Real.rpow_neg zero_le_two,
        Real.rpow_natCast, inv_pow]
    have h2 : Tendsto (fun n : ℕ ↦ (M + 1) * (2⁻¹ : ℝ) ^ n) atTop (𝓝 0) := by
      simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 2⁻¹)
        (by norm_num)).const_mul (M + 1)
    rw [← ENNReal.ofReal_zero]
    exact ENNReal.tendsto_ofReal (h2.congr fun n ↦ (h n).symm)
  have hle : ∀ᶠ n in atTop, bowenInformation μ T n ε / n ≤ ∫⁻ x, g n x ∂μ + d n := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    set S : Set X := {x | ENNReal.ofReal M < localEntropyRate μ T x n ε} with hS
    have hSm : MeasurableSet S := measurableSet_lt measurable_const
      (measurable_localEntropyRate μ hT n ε)
    rw [← lintegral_localEntropyRate hT]
    calc ∫⁻ x, localEntropyRate μ T x n ε ∂μ
        ≤ ∫⁻ x, g n x + S.indicator (fun x ↦ localEntropyRate μ T x n ε) x ∂μ := by
          refine lintegral_mono fun x ↦ ?_
          by_cases hx : x ∈ S
          · rw [indicator_of_mem hx]
            exact le_add_self
          · have : localEntropyRate μ T x n ε ≤ ENNReal.ofReal M := not_lt.1 hx
            simp [hgdef, min_eq_left this]
      _ = ∫⁻ x, g n x ∂μ + ∫⁻ x in S, localEntropyRate μ T x n ε ∂μ := by
          rw [lintegral_add_left (hg n), lintegral_indicator hSm]
      _ ≤ ∫⁻ x, g n x ∂μ + d n := by
          gcongr
          exact hb M (by linarith) n hn
  calc (informationRateAt μ T ε).2
      ≤ limsup (fun n ↦ ∫⁻ x, g n x ∂μ) atTop :=
        limsup_le_limsup_of_le_add_tendsto_zero hle hdlim
    _ ≤ ∫⁻ x, limsup (fun n ↦ g n x) atTop ∂μ :=
        limsup_lintegral_le (fun _ ↦ ENNReal.ofReal M) hg
          (fun n ↦ ae_of_all _ fun x ↦ min_le_right _ _)
          (by simp [lintegral_const])
    _ ≤ ∫⁻ x, (localEntropyAt μ T x ε).2 ∂μ :=
        lintegral_mono fun x ↦ limsup_le_limsup (Eventually.of_forall fun n ↦ min_le_left _ _)

/-- Proposition 4.7: on a compact space `H̄_μ(T) ≤ h̄_μ(T)`. Blueprint node `meas:comparison`. -/
theorem informationRate_snd_le_measureEntropy_snd [CompactSpace X] {T : X → X}
    (hT : Continuous T) (μ : Measure X) [IsProbabilityMeasure μ] :
    (informationRate μ T).2 ≤ (measureEntropy μ T).2 :=
  iSup_le fun p ↦ (informationRateAt_snd_le_lintegral_localEntropyAt hT μ
    (dyadicRadius_pos p)).trans (lintegral_mono fun x ↦
      le_iSup (fun p ↦ (localEntropyAt μ T x (dyadicRadius p)).2) p)

/-! ### Finite-time affinity (Proposition 6.16) -/

omit [BorelSpace X] in
/-- Proposition 6.16(i): the expected orbit complexity is affine on countable combinations.
Blueprint node `meas:finite-time-affinity`. -/
theorem expectedOrbitComplexity_sum (P : Presentation X) {T : X → X}
    (A : Set ℕ) {ι : Type*} [Countable ι] (t : ι → ℝ≥0∞) (μs : ι → Measure X) (n : ℕ)
    (ε : ℝ) :
    expectedOrbitComplexity P T A (Measure.sum fun j ↦ t j • μs j) n ε =
      ∑' j, t j * expectedOrbitComplexity P T A (μs j) n ε := by
  simp only [expectedOrbitComplexity, lintegral_sum_measure, lintegral_smul_measure, smul_eq_mul]

omit [MetricSpace X] [MeasurableSpace X] [BorelSpace X] in
/-- The information is subadditive on products of masses:
`-log₂ (a b) ≤ -log₂ a - log₂ b`, with the conventions of `infoBits`. -/
theorem infoBits_mul_le_add (a b : ℝ≥0∞) : infoBits (a * b) ≤ infoBits a + infoBits b := by
  rcases eq_or_ne a 0 with rfl | ha0
  · simp
  rcases eq_or_ne b 0 with rfl | hb0
  · simp
  rcases eq_or_ne a ⊤ with rfl | hat
  · simp [ENNReal.top_mul hb0]
  rcases eq_or_ne b ⊤ with rfl | hbt
  · simp [ENNReal.mul_top ha0]
  have har : 0 < a.toReal := ENNReal.toReal_pos ha0 hat
  have hbr : 0 < b.toReal := ENNReal.toReal_pos hb0 hbt
  rw [infoBits_of_ne (mul_ne_zero ha0 hb0), infoBits_of_ne ha0, infoBits_of_ne hb0,
    ENNReal.toReal_mul, Real.logb_mul har.ne' hbr.ne', neg_add]
  exact ENNReal.ofReal_add_le

omit [BorelSpace X] in
/-- Proposition 6.16(ii): `I_n(μ, ε) ≤ ∑_j t_j I_n(μ_j, ε) + H(t)` for a countable combination
`μ = ∑_j t_j μ_j`, where `H(t) = -∑_j t_j log₂ t_j`. Blueprint node `meas:finite-time-affinity`. -/
theorem bowenInformation_sum_le {T : X → X} {ι : Type*} [Countable ι]
    (t : ι → ℝ≥0∞) (μs : ι → Measure X) [∀ j, IsProbabilityMeasure (μs j)] (n : ℕ) (ε : ℝ) :
    bowenInformation (Measure.sum fun j ↦ t j • μs j) T n ε ≤
      ∑' j, t j * bowenInformation (μs j) T n ε + ∑' j, t j * infoBits (t j) := by
  set μ := Measure.sum fun j ↦ t j • μs j with hμ
  rw [← ENNReal.tsum_add, bowenInformation, lintegral_sum_measure]
  refine ENNReal.tsum_le_tsum fun j ↦ ?_
  rw [lintegral_smul_measure, smul_eq_mul, ← mul_add]
  gcongr
  calc ∫⁻ x, infoBits (μ (bowenBall T n x ε)) ∂μs j
      ≤ ∫⁻ x, infoBits (μs j (bowenBall T n x ε)) + infoBits (t j) ∂μs j := by
        refine lintegral_mono fun x ↦ ?_
        have hle : t j * μs j (bowenBall T n x ε) ≤ μ (bowenBall T n x ε) := by
          have := Measure.le_iff'.1 (Measure.le_sum (fun j ↦ t j • μs j) j)
            (bowenBall T n x ε)
          simpa using this
        calc infoBits (μ (bowenBall T n x ε))
            ≤ infoBits (t j * μs j (bowenBall T n x ε)) := infoBits_antitone hle
          _ ≤ _ := by rw [add_comm]; exact infoBits_mul_le_add _ _
    _ = bowenInformation (μs j) T n ε + infoBits (t j) := by
        rw [lintegral_add_right _ measurable_const, lintegral_const, measure_univ, mul_one,
          bowenInformation]

/-- Proposition 6.16(iii): for a countable convex combination `μ = ∑_j t_j μ_j` of Borel
probability measures, `A` admissible for `(X, d, T, μ)` and rational `ε > 0` there is `c` with
`∑_j t_j I_n(μ_j, 12ε) ≤ I_n(μ, ε) + 4 log₂ n + 2 log₂ (I_n(μ, ε) + 2) + c` for all `n ≥ 1`.
Blueprint node `meas:finite-time-affinity`. -/
theorem sum_bowenInformation_le (P : Presentation X) (T : X → X) (hT : Continuous T)
    (A : Set ℕ) {ι : Type*} [Countable ι] (t : ι → ℝ≥0∞) (μs : ι → Measure X)
    [∀ j, IsProbabilityMeasure (μs j)] (ht : ∑' j, t j = 1)
    (hA : IsMeasureAdmissible P T (Measure.sum fun j ↦ t j • μs j) A) (ε : ℚ) (hε : 0 < ε) :
    ∃ c : ℕ, ∀ n : ℕ, 1 ≤ n →
      ∑' j, t j * bowenInformation (μs j) T n (12 * (ε : ℝ)) ≤
        bowenInformation (Measure.sum fun j ↦ t j • μs j) T n ε +
          ENNReal.ofReal (4 * Real.logb 2 n) +
          ENNReal.ofReal (2 * Real.logb 2
            ((bowenInformation (Measure.sum fun j ↦ t j • μs j) T n ε).toReal + 2)) + c := by
  set μ := Measure.sum fun j ↦ t j • μs j with hμ
  have : IsProbabilityMeasure μ := ⟨by
    rw [hμ, Measure.sum_apply _ MeasurableSet.univ]
    simp [ht]⟩
  obtain ⟨c, hc⟩ := expectedOrbitComplexity_le_bowenInformation P T hT A μ hA ε hε
  refine ⟨c + 1, fun n hn ↦ ?_⟩
  have hε6 : (0 : ℝ) < 6 * ε := by
    have : (0 : ℝ) < ε := by exact_mod_cast hε
    linarith
  have hL : 0 ≤ Real.logb 2 n := Real.logb_nonneg one_lt_two (by exact_mod_cast hn)
  set E := ENNReal.ofReal (2 * Real.logb 2 n) with hE
  have e1 : ENNReal.ofReal (2 * Real.logb 2 n + 1) = E + 1 := by
    rw [ENNReal.ofReal_add (by positivity) zero_le_one, ENNReal.ofReal_one]
  have e2 : ENNReal.ofReal (4 * Real.logb 2 n) = E + E := by
    rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
    ring_nf
  calc ∑' j, t j * bowenInformation (μs j) T n (12 * (ε : ℝ))
      ≤ ∑' j, t j * (expectedOrbitComplexity P T A (μs j) n (6 * ε) +
          ENNReal.ofReal (2 * Real.logb 2 n + 1)) := by
        refine ENNReal.tsum_le_tsum fun j ↦ ?_
        gcongr
        have h := bowenInformation_le_expectedOrbitComplexity P T hT A (μs j) hε6 hn
        rwa [show 2 * (6 * (ε : ℝ)) = 12 * ε by ring] at h
    _ = expectedOrbitComplexity P T A μ n (6 * ε) + ENNReal.ofReal (2 * Real.logb 2 n + 1) := by
        rw [expectedOrbitComplexity_sum P A t μs n]
        simp_rw [mul_add]
        rw [ENNReal.tsum_add, ENNReal.tsum_mul_right, ht, one_mul]
    _ ≤ bowenInformation μ T n ε + E +
          ENNReal.ofReal (2 * Real.logb 2 ((bowenInformation μ T n ε).toReal + 2)) + c +
          ENNReal.ofReal (2 * Real.logb 2 n + 1) := by
        gcongr
        exact hc n hn
    _ = _ := by
        rw [e1, e2]
        push_cast
        ring

end Kolmogorov.PointToSet
