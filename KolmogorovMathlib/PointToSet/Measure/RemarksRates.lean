/-
Copyright (c) 2026 Emma Dinowitz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emma Dinowitz
-/
import KolmogorovMathlib.PointToSet.Measure.ShiftBernoulli
import KolmogorovMathlib.PointToSet.Measure.ShiftProduct
import KolmogorovMathlib.PointToSet.Measure.PressurePointwise
import KolmogorovMathlib.PointToSet.BowenEquation.PointwiseCriticalValue
import KolmogorovMathlib.PointToSet.Conformal.Distortion.PointwiseDimension

/-!
# Remarks 6.9, 6.17, 7.2 (Bernoulli sentence) and 8.5

Formal statements of four remarks of E. Dinowitz, *Entropy of non-invariant measures and orbit
complexity of random points* (pages 11, 13–14, 14 and 19). Blueprint node `meas:remarks`.

## Remark 6.17 (concavity and convexity of the rates)

* `informationRate_sum_eq`: for `μ = ∑_j t_j μ_j` (countably many components, weights of
  finite entropy) `H̲_μ = sup_ε liminf_n (1/n) ∑_j t_j I_n(μ_j, ε)` and the same for `H̄_μ` with
  `limsup` (Proposition 6.16(ii), (iii)); no finiteness of the rates is needed.
* `informationRate_fst_concave`, `informationRate_snd_convex`: on the simplex of mixing weights
  of finitely many measures, `t ↦ H̲` is concave and `t ↦ H̄` is convex.
* The sentence "on a shift the error in (iii) is 0 at equal scales" is the lower bound of
  `lintegral_infoBits_mixture_bounds` (Gibbs' inequality).

## Remark 6.9 (support-function form, on the shift)

* `lintegral_infoBits_mixture_bounds`:
  `∑_j t_j H_{μ_j}(ξ^n) ≤ H_μ(ξ^n) ≤ ∑_j t_j H_{μ_j}(ξ^n) + H(t)`.
* `informationRate_mixture_isLeast_isGreatest`: with `A_j(n) = (1/n) H_{μ_j}(ξ^n)`
  (`cylinderInfoRate`) and `C` the set of accumulation points of `(A_1(n), …, A_k(n))`,
  `H̲_μ(σ) = min_{c ∈ C} ⟨t, c⟩` and `H̄_μ(σ) = max_{c ∈ C} ⟨t, c⟩`; the general fact is
  `isLeast_isGreatest_image_mapClusterPt`, the bound `A_j(n) ≤ 1` is
  `lintegral_infoBits_cylinder_le_length`.
* `informationRate_mixture_fst_eq_snd_iff`: the two rates coincide for all mixing weights
  exactly when `C` is a point.

## Remark 7.2, last sentence (two Bernoulli measures)

* `crossEntropyBits` (`H(q‖p)`), `binEntropy_div_log_two_le_crossEntropyBits` (Gibbs:
  `H(q) ≤ H(q‖p)`);
* `ae_localEntropy_bernoulliMeasure_crossEntropy`: `ν_q`-a.e. `Φ_{ν_p}(x) = (H(q‖p), H(q‖p))`;
  `ae_localEntropy_bernoulliMeasure_le_crossEntropy`: `ν_q`-a.e.
  `Φ_{ν_q}(x) = (H(q), H(q)) ≤ Φ_{ν_p}(x)`;
* `localEntropy_bernoulliMeasure_le_of_mem_randomPoints`: `Φ_{ν_q} ≤ Φ_{ν_p}` at every
  `ν_q`-random point relative to an oracle admissible for both (Theorem 3.3 twice);
* `localEntropy_bernoulliMeasure_eq_crossEntropy_of_mem_randomPoints` (in
  `Ergodic/BernoulliRandom.lean`, from an effective strong law at every random point and the
  ergodicity of Bernoulli shifts): the values at every random point.

## Remark 8.5 (Bowen equation and conformal maps)

* "Corollary 8.4(a), (b) is a mass distribution principle": commentary, not stated.
* `localBowenEquation`: at a `μ`-random point with `0 < u̲(x) ≤ ū(x) < ∞` and finite local
  entropy, `d̲_μ(x, T, u)` (and `d̄_μ`) is finite and is the unique root of
  `P̲_μ(x, T, -s u) = 0` (resp. `P̄_μ`). It is proved from Theorem 8.3(ii)
  (`localPressure_smul_eq_pointwisePressure`, `pointwisePressure_zero_eq_localEntropy`,
  `birkhoffBoundedBelow_smul_of_averages`) and the library's pointwise Bowen equation, restated
  as `pointwiseBowenEquation_root`.
* `staticPointDimensions_eq_localBSDimension_conformal`: on the conformal locus of Theorem E, at
  `μ`-random points, the algorithmic dimensions are the local BS dimensions (from Theorem E,
  restated as `staticPointDimensions_eq_pointwiseBSDimension_conformal`, and Theorem 8.3(ii)).
* `localDimension` (round-ball local dimensions); the step the paper marks as unchecked,
  `localBSDimension_eq_localDimension_conformal`, is proved in
  `Ergodic/ConformalBallComparison.lean` (for every measure, from `ballInclusion` and
  `nonmonotoneScaleSampling`).

## Not stated

* Remark 6.9: "both depend only on the convex hull of `C`" (immediate from the support-function
  form), the description of `C` in Example 6.8 (a segment), and the affinity criteria ("the lower
  rate is affine in `t` exactly when `C` contains its coordinatewise minimum, the upper rate
  exactly when `C` contains its coordinatewise maximum"); these are elementary consequences of
  `informationRate_mixture_isLeast_isGreatest` that were not formalized.
* Remark 6.17: whether the logarithmic error and the factor 12 of Proposition 6.16(iii) can be
  removed in general is stated by the paper as an open question.
-/

namespace Kolmogorov.PointToSet

open Filter Set MeasureTheory
open scoped Topology ENNReal NNReal Computability

/-! ### Remark 6.17: concavity and convexity of the information rates -/

section concavity

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

/-- Remark 6.17 (first display): for a countable convex combination `μ = ∑_j t_j μ_j` of Borel
probability measures whose weights have finite entropy `H(t) = ∑_j t_j (-log₂ t_j)`,
`H̲_μ(T) = lim_{ε→0} liminf_n (1/n) ∑_j t_j I_n(μ_j, ε)` and
`H̄_μ(T) = lim_{ε→0} limsup_n (1/n) ∑_j t_j I_n(μ_j, ε)`, the limits in `ε` being suprema over
the dyadic scales `2^{-p}` (as in `informationRate`). Upper bound: Proposition 6.16(ii) (the
`H(t)` bits vanish after division by `n`); lower bound: Proposition 6.16(iii) with an oracle
admissible for `μ` (`exists_measureAdmissible_base`), the change of scale `12ε ↔ ε` being
absorbed by the supremum over scales. Divergences: the paper takes finitely many components
"with finite information rates"; neither finiteness hypothesis is needed (the logarithmic error
of 6.16(iii) is handled below every real level of the lower and upper limits), only the
finiteness of `H(t)`, automatic for finitely many components (`weightEntropy_ne_top`).
Blueprint node `meas:remarks`. -/
theorem informationRate_sum_eq (P : Presentation X) (T : X → X) (hT : Continuous T)
    {ι : Type*} [Countable ι] (t : ι → ℝ≥0∞) (μs : ι → Measure X)
    [∀ j, IsProbabilityMeasure (μs j)] (ht : ∑' j, t j = 1)
    (hH : ∑' j, t j * infoBits (t j) ≠ ⊤) :
    informationRate (Measure.sum fun j ↦ t j • μs j) T =
      (⨆ p : ℕ, liminf (fun n : ℕ ↦
          (∑' j, t j * bowenInformation (μs j) T n (dyadicRadius p)) / n) atTop,
        ⨆ p : ℕ, limsup (fun n : ℕ ↦
          (∑' j, t j * bowenInformation (μs j) T n (dyadicRadius p)) / n) atTop) := by
  set μ := Measure.sum fun j ↦ t j • μs j with hμ
  have : IsProbabilityMeasure μ := ⟨by
    rw [hμ, Measure.sum_apply _ MeasurableSet.univ]
    simp [ht]⟩
  set W : ℕ → ℕ → ℝ≥0∞ := fun p n ↦
    ∑' j, t j * bowenInformation (μs j) T n (dyadicRadius p) with hW
  set H := ∑' j, t j * infoBits (t j) with hHdef
  -- the mixture costs at most `H(t)` bits more than the average (Proposition 6.16(ii))
  have hup : ∀ p : ℕ,
      (informationRateAt μ T (dyadicRadius p)).1 ≤ liminf (fun n : ℕ ↦ W p n / n) atTop ∧
      (informationRateAt μ T (dyadicRadius p)).2 ≤ limsup (fun n : ℕ ↦ W p n / n) atTop := by
    intro p
    have hd : Tendsto (fun n : ℕ ↦ H / n) atTop (𝓝 0) := by
      have := ENNReal.Tendsto.const_mul ENNReal.tendsto_inv_nat_nhds_zero (Or.inr hH)
      simpa [div_eq_mul_inv] using this
    have h : ∀ᶠ n : ℕ in atTop,
        bowenInformation μ T n (dyadicRadius p) / n ≤ W p n / n + H / n :=
      Eventually.of_forall fun n ↦ by
        rw [← ENNReal.add_div]
        exact ENNReal.div_le_div_right (bowenInformation_sum_le t μs n _) _
    exact ⟨liminf_le_liminf_of_le_add_tendsto_zero h hd,
      limsup_le_limsup_of_le_add_tendsto_zero h hd⟩
  -- the average costs at most a logarithmic term more, at a finer scale
  -- (Proposition 6.16(iii), with an oracle admissible for the mixture)
  obtain ⟨C, hC⟩ := exists_measureAdmissible_base P T hT μ
  have hA := hC C (TuringReducible.refl _)
  have hlow : ∀ p : ℕ, liminf (fun n : ℕ ↦ W p n / n) atTop ≤ (informationRate μ T).1 ∧
      limsup (fun n : ℕ ↦ W p n / n) atTop ≤ (informationRate μ T).2 := by
    intro p
    set ε : ℚ := (2 : ℚ)⁻¹ ^ (p + 4) with hεdef
    have hε : 0 < ε := by positivity
    have hε' : (0 : ℝ) < ε := by exact_mod_cast hε
    have h12 : 12 * (ε : ℝ) ≤ dyadicRadius p := by
      have h0 : (0 : ℝ) ≤ (2 : ℝ)⁻¹ ^ p := by positivity
      rw [hεdef, dyadicRadius]
      push_cast
      rw [pow_add]
      norm_num
      linarith
    obtain ⟨c, hc⟩ := sum_bowenInformation_le P T hT C t μs ht hA ε hε
    have hle := liminf_limsup_le_of_forall_lt
      (a := fun n : ℕ ↦ bowenInformation μ T n ε / n) (b := fun n : ℕ ↦ W p n / n) ?_
    · have h3 := informationRateAt_le_informationRate μ T hε'
      exact ⟨hle.1.trans h3.1, hle.2.trans h3.2⟩
    intro s hs
    refine ⟨fun n ↦ ENNReal.ofReal ((c + 2 * Real.logb 2 (s + 2) + 6 * Real.logb 2 n) / n),
      ?_, ?_⟩
    · rw [← ENNReal.ofReal_zero]
      exact ENNReal.tendsto_ofReal (tendsto_add_mul_logb_div_nat _ _)
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
    have hWle : W p n ≤ ∑' j, t j * bowenInformation (μs j) T n (12 * (ε : ℝ)) :=
      ENNReal.tsum_le_tsum fun j ↦ by
        gcongr
        exact bowenInformation_antitone _ _ _ h12
    have hE := hWle.trans (hc n hn)
    rw [← hI] at hE
    have hE' : W p n ≤
        ENNReal.ofReal (s * n + (c + 2 * Real.logb 2 (s + 2) + 6 * Real.logb 2 n)) := by
      have heq : I + ENNReal.ofReal (4 * Real.logb 2 n) +
          ENNReal.ofReal (2 * Real.logb 2 (I.toReal + 2)) + c = ENNReal.ofReal
            (I.toReal + 4 * Real.logb 2 n + 2 * Real.logb 2 (I.toReal + 2) + c) := by
        rw [ENNReal.ofReal_add (by linarith) (by positivity),
          ENNReal.ofReal_add (by linarith) (by linarith),
          ENNReal.ofReal_add hI0 (by linarith), ENNReal.ofReal_toReal hItop,
          ENNReal.ofReal_natCast]
      rw [heq] at hE
      refine hE.trans (ENNReal.ofReal_le_ofReal ?_)
      linarith
    calc W p n / n
        ≤ ENNReal.ofReal (s * n + (c + 2 * Real.logb 2 (s + 2) + 6 * Real.logb 2 n)) / n := by
          gcongr
      _ = ENNReal.ofReal (s + (c + 2 * Real.logb 2 (s + 2) + 6 * Real.logb 2 n) / n) := by
          rw [ofReal_div_natCast hn]
          congr 1
          field_simp
      _ ≤ _ := ENNReal.ofReal_add_le
  refine Prod.ext (le_antisymm ?_ ?_) (le_antisymm ?_ ?_)
  · exact iSup_le fun p ↦ (hup p).1.trans
      (le_iSup (fun q ↦ liminf (fun n : ℕ ↦ W q n / n) atTop) p)
  · exact iSup_le fun p ↦ (hlow p).1
  · exact iSup_le fun p ↦ (hup p).2.trans
      (le_iSup (fun q ↦ limsup (fun n : ℕ ↦ W q n / n) atTop) p)
  · exact iSup_le fun p ↦ (hlow p).2

/-- In `ℝ≥0∞` the lower limit is superadditive. -/
private theorem le_liminf_add' (u v : ℕ → ℝ≥0∞) :
    liminf u atTop + liminf v atTop ≤ liminf (fun n ↦ u n + v n) atTop := by
  simp only [liminf_eq_iSup_iInf_of_nat]
  have hm : ∀ w : ℕ → ℝ≥0∞, Monotone fun N : ℕ ↦ ⨅ i ≥ N, w i := fun w _ _ h ↦
    le_iInf₂ fun i hi ↦ iInf₂_le i (h.trans hi)
  rw [ENNReal.iSup_add_iSup_of_monotone (hm u) (hm v)]
  exact iSup_mono fun N ↦ le_iInf₂ fun i hi ↦ add_le_add (iInf₂_le i hi) (iInf₂_le i hi)

/-- In `ℝ≥0∞` the upper limit is subadditive. -/
private theorem limsup_add_le' (u v : ℕ → ℝ≥0∞) :
    limsup (fun n ↦ u n + v n) atTop ≤ limsup u atTop + limsup v atTop := by
  simp only [limsup_eq_iInf_iSup_of_nat]
  rw [ENNReal.iInf_add]
  refine le_iInf fun N ↦ ?_
  rw [ENNReal.add_iInf]
  refine le_iInf fun M ↦ (iInf_le _ (max N M)).trans ?_
  exact iSup₂_le fun i hi ↦ add_le_add (le_iSup₂_of_le i ((le_max_left _ _).trans hi) le_rfl)
    (le_iSup₂_of_le i ((le_max_right _ _).trans hi) le_rfl)

/-- The entropy `H(t) = ∑_j t_j (-log₂ t_j)` of a finite probability vector is finite. -/
theorem weightEntropy_ne_top {ι : Type*} [Fintype ι] (t : ι → ℝ≥0∞) (ht : ∑ j, t j = 1) :
    ∑' j, t j * infoBits (t j) ≠ ⊤ := by
  rw [tsum_fintype]
  refine ENNReal.sum_ne_top.2 fun j _ ↦ ?_
  have hle : t j ≤ 1 := ht ▸ Finset.single_le_sum (fun _ _ ↦ bot_le) (Finset.mem_univ j)
  rcases eq_or_ne (t j) 0 with h | h
  · simp [h]
  exact ENNReal.mul_ne_top (ne_top_of_le_ne_top ENNReal.one_ne_top hle) (infoBits_lt_top h).ne

/-- The weights `a t + (1 - a) t'` of a mixture of two probability vectors add up to one. -/
private theorem sum_mix_eq_one {ι : Type*} [Fintype ι] {t t' : ι → ℝ≥0∞} (ht : ∑ j, t j = 1)
    (ht' : ∑ j, t' j = 1) {a : ℝ≥0∞} (ha : a ≤ 1) :
    ∑' j, (a * t j + (1 - a) * t' j) = 1 := by
  rw [tsum_fintype, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ht, ht',
    mul_one, mul_one, add_tsub_cancel_of_le ha]

/-- The averaged mean information is affine in the weights. -/
private theorem tsum_mix_div {ι : Type*} (t t' : ι → ℝ≥0∞) (a : ℝ≥0∞) (B : ι → ℝ≥0∞)
    (n : ℕ) :
    (∑' j, (a * t j + (1 - a) * t' j) * B j) / n =
      a * ((∑' j, t j * B j) / n) + (1 - a) * ((∑' j, t' j * B j) / n) := by
  simp_rw [add_mul, mul_assoc]
  rw [ENNReal.tsum_add, ENNReal.tsum_mul_left, ENNReal.tsum_mul_left, ENNReal.add_div,
    mul_div_assoc, mul_div_assoc]

omit [BorelSpace X] in
/-- The averaged mean information at the scale `2^{-p}` increases with `p`. -/
private theorem monotone_tsum_bowenInformation {ι : Type*} (T : X → X) (s : ι → ℝ≥0∞)
    (μs : ι → Measure X) (n : ℕ) :
    Monotone fun p : ℕ ↦ (∑' j, s j * bowenInformation (μs j) T n (dyadicRadius p)) / n :=
  fun _ _ h ↦ ENNReal.div_le_div_right (ENNReal.tsum_le_tsum fun _ ↦
    by gcongr; exact bowenInformation_antitone _ _ _ (dyadicRadius_antitone h)) _

/-- Remark 6.17, concavity: on the simplex of mixing weights of finitely many fixed Borel
probability measures `μ_j`, `t ↦ H̲_{∑_j t_j μ_j}(T)` is concave: for weight vectors `t`, `t'`
and `a ∈ [0, 1]`, `a H̲_{μ_t} + (1 - a) H̲_{μ_{t'}} ≤ H̲_{μ_{a t + (1 - a) t'}}` (values in
`[0, ∞]`). A lower limit of functions affine in `t` is concave, and so is the increasing limit
over the scales. Divergence: no finiteness of the rates is assumed. Blueprint node
`meas:remarks`. -/
theorem informationRate_fst_concave (P : Presentation X) (T : X → X) (hT : Continuous T)
    {ι : Type*} [Fintype ι] (μs : ι → Measure X) [∀ j, IsProbabilityMeasure (μs j)]
    (t t' : ι → ℝ≥0∞) (ht : ∑ j, t j = 1) (ht' : ∑ j, t' j = 1) {a : ℝ≥0∞} (ha : a ≤ 1) :
    a * (informationRate (Measure.sum fun j ↦ t j • μs j) T).1 +
        (1 - a) * (informationRate (Measure.sum fun j ↦ t' j • μs j) T).1 ≤
      (informationRate (Measure.sum fun j ↦ (a * t j + (1 - a) * t' j) • μs j) T).1 := by
  have hsum : ∀ s : ι → ℝ≥0∞, ∑ j, s j = 1 → ∑' j, s j = 1 := fun s hs ↦ by
    rw [tsum_fintype]; exact hs
  have hmix := sum_mix_eq_one ht ht' ha
  have hmix' : ∑ j, (a * t j + (1 - a) * t' j) = 1 := by rwa [tsum_fintype] at hmix
  rw [informationRate_sum_eq P T hT t μs (hsum t ht) (weightEntropy_ne_top t ht),
    informationRate_sum_eq P T hT t' μs (hsum t' ht') (weightEntropy_ne_top t' ht'),
    informationRate_sum_eq P T hT _ μs hmix (weightEntropy_ne_top _ hmix')]
  dsimp only
  have ha' : a ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top ha
  have hb' : 1 - a ≠ ⊤ := ENNReal.sub_ne_top ENNReal.one_ne_top
  have hm : ∀ s : ι → ℝ≥0∞, Monotone fun p : ℕ ↦ liminf (fun n : ℕ ↦
      (∑' j, s j * bowenInformation (μs j) T n (dyadicRadius p)) / n) atTop := fun s _ _ h ↦
    liminf_le_liminf (Eventually.of_forall fun n ↦ monotone_tsum_bowenInformation T s μs n h)
  rw [ENNReal.mul_iSup, ENNReal.mul_iSup,
    ENNReal.iSup_add_iSup_of_monotone (fun _ _ h ↦ by gcongr; exact hm t h)
      (fun _ _ h ↦ by gcongr; exact hm t' h)]
  refine iSup_mono fun p ↦ ?_
  simp_rw [tsum_mix_div]
  rw [← ENNReal.liminf_const_mul_of_ne_top ha', ← ENNReal.liminf_const_mul_of_ne_top hb']
  exact le_liminf_add' _ _

/-- Remark 6.17, convexity: `t ↦ H̄_{∑_j t_j μ_j}(T)` is convex on the simplex:
`H̄_{μ_{a t + (1 - a) t'}} ≤ a H̄_{μ_t} + (1 - a) H̄_{μ_{t'}}` (values in `[0, ∞]`). An upper
limit of affine functions is convex, and so is a supremum of convex functions. Divergence: no
finiteness of the rates is assumed. Blueprint node `meas:remarks`. -/
theorem informationRate_snd_convex (P : Presentation X) (T : X → X) (hT : Continuous T)
    {ι : Type*} [Fintype ι] (μs : ι → Measure X) [∀ j, IsProbabilityMeasure (μs j)]
    (t t' : ι → ℝ≥0∞) (ht : ∑ j, t j = 1) (ht' : ∑ j, t' j = 1) {a : ℝ≥0∞} (ha : a ≤ 1) :
    (informationRate (Measure.sum fun j ↦ (a * t j + (1 - a) * t' j) • μs j) T).2 ≤
      a * (informationRate (Measure.sum fun j ↦ t j • μs j) T).2 +
        (1 - a) * (informationRate (Measure.sum fun j ↦ t' j • μs j) T).2 := by
  have hsum : ∀ s : ι → ℝ≥0∞, ∑ j, s j = 1 → ∑' j, s j = 1 := fun s hs ↦ by
    rw [tsum_fintype]; exact hs
  have hmix := sum_mix_eq_one ht ht' ha
  have hmix' : ∑ j, (a * t j + (1 - a) * t' j) = 1 := by rwa [tsum_fintype] at hmix
  rw [informationRate_sum_eq P T hT t μs (hsum t ht) (weightEntropy_ne_top t ht),
    informationRate_sum_eq P T hT t' μs (hsum t' ht') (weightEntropy_ne_top t' ht'),
    informationRate_sum_eq P T hT _ μs hmix (weightEntropy_ne_top _ hmix')]
  dsimp only
  refine iSup_le fun p ↦ ?_
  simp_rw [tsum_mix_div]
  refine (limsup_add_le' _ _).trans ?_
  rw [ENNReal.limsup_const_mul_of_ne_top (ne_top_of_le_ne_top ENNReal.one_ne_top ha),
    ENNReal.limsup_const_mul_of_ne_top (ENNReal.sub_ne_top ENNReal.one_ne_top)]
  gcongr
  · exact le_iSup (fun q ↦ limsup (fun n : ℕ ↦
      (∑' j, t j * bowenInformation (μs j) T n (dyadicRadius q)) / n) atTop) p
  · exact le_iSup (fun q ↦ limsup (fun n : ℕ ↦
      (∑' j, t' j * bowenInformation (μs j) T n (dyadicRadius q)) / n) atTop) p

end concavity

/-! ### Remark 6.9 -/

section supportFunction

attribute [local instance] cantorMetricSpace

/-- The normalized mean cylinder information `A(n) = (1/n) H_ν(ξ^n)`,
`H_ν(ξ^n) = ∫ -log₂ ν[x↾n] dν`, as a real number (`ξ^n` is the partition into cylinders of
length `n`). Blueprint node `meas:remarks`. -/
noncomputable def cylinderInfoRate (ν : Measure (ℕ → Bool)) (n : ℕ) : ℝ :=
  ((∫⁻ x, infoBits (ν (PiNat.cylinder x n)) ∂ν) / n).toReal

/-- The mean information of the cylinders of length `n` is at most `n` bits (Gibbs' inequality
against the fair-coin measure): `∫ -log₂ ν[x↾n] dν ≤ n`, so `A(n) ≤ log₂ |{0, 1}| = 1`. -/
theorem lintegral_infoBits_cylinder_le_length (ν : Measure (ℕ → Bool)) [IsProbabilityMeasure ν]
    (n : ℕ) (hν : ∀ x, ν (PiNat.cylinder x n) ≠ 0) :
    ∫⁻ x, infoBits (ν (PiNat.cylinder x n)) ∂ν ≤ n := by
  refine (lintegral_infoBits_cylinder_le ν uniformMeasure n hν
    fun x ↦ by simp [uniformMeasure_cylinder]).trans_eq ?_
  have h : ∀ x : ℕ → Bool, infoBits (uniformMeasure (PiNat.cylinder x n)) = n := fun x ↦ by
    rw [uniformMeasure_cylinder, infoBits_of_ne (by simp), ENNReal.toReal_pow,
      ENNReal.toReal_inv, ENNReal.toReal_ofNat, Real.logb_pow, Real.logb_inv,
      Real.logb_self_eq_one one_lt_two]
    simp
  simp only [h, lintegral_const, measure_univ, mul_one]

/-- Remark 6.9 (and the shift case of the last paragraph of Remark 6.17), finite-time bounds:
for a finite mixture `μ = ∑_j t_j μ_j` of probability measures on Cantor space whose cylinders
all have positive mass, writing `H_ν(ξ^n) = ∫ -log₂ ν[x↾n] dν`,
`∑_j t_j H_{μ_j}(ξ^n) ≤ H_μ(ξ^n) ≤ ∑_j t_j H_{μ_j}(ξ^n) + H(t)` with
`H(t) = ∑_j t_j (-log₂ t_j)`. The lower bound is Gibbs' inequality on each component (the
paper: "on a shift the error in (iii) is 0 at equal scales, by concavity of Shannon entropy"),
the upper bound uses `μ ≥ t_j μ_j`. Divergence: the positivity of the cylinders is assumed
(it is the hypothesis of the available Gibbs inequality `lintegral_infoBits_cylinder_le`). -/
theorem lintegral_infoBits_mixture_bounds {ι : Type*} [Fintype ι] (t : ι → ℝ≥0)
    (ht : ∑ j, t j = 1) (μs : ι → Measure (ℕ → Bool)) [∀ j, IsProbabilityMeasure (μs j)]
    (hpos : ∀ j x n, μs j (PiNat.cylinder x n) ≠ 0) (n : ℕ) :
    ∑ j, (t j : ℝ≥0∞) * ∫⁻ x, infoBits (μs j (PiNat.cylinder x n)) ∂μs j ≤
        ∫⁻ x, infoBits ((Measure.sum fun j ↦ (t j : ℝ≥0∞) • μs j) (PiNat.cylinder x n))
          ∂(Measure.sum fun j ↦ (t j : ℝ≥0∞) • μs j) ∧
      ∫⁻ x, infoBits ((Measure.sum fun j ↦ (t j : ℝ≥0∞) • μs j) (PiNat.cylinder x n))
          ∂(Measure.sum fun j ↦ (t j : ℝ≥0∞) • μs j) ≤
        ∑ j, (t j : ℝ≥0∞) * ∫⁻ x, infoBits (μs j (PiNat.cylinder x n)) ∂μs j +
          ∑ j, (t j : ℝ≥0∞) * infoBits (t j) := by
  set μ := Measure.sum fun j ↦ (t j : ℝ≥0∞) • μs j with hμ
  have hsum : ∑ j, (t j : ℝ≥0∞) = 1 := by rw [← ENNReal.ofNNReal_finsetSum, ht, ENNReal.coe_one]
  have : IsProbabilityMeasure μ := ⟨by
    rw [hμ, Measure.sum_apply _ MeasurableSet.univ, tsum_fintype]
    simp [hsum]⟩
  have hlin : ∀ g : (ℕ → Bool) → ℝ≥0∞, ∫⁻ x, g x ∂μ = ∑ j, (t j : ℝ≥0∞) * ∫⁻ x, g x ∂μs j := by
    intro g
    rw [hμ, lintegral_sum_measure, tsum_fintype]
    simp_rw [lintegral_smul_measure, smul_eq_mul]
  have hle : ∀ j s, (t j : ℝ≥0∞) * μs j s ≤ μ s := fun j s ↦ by
    have := Measure.le_iff'.1 (Measure.le_sum (fun j ↦ (t j : ℝ≥0∞) • μs j) j) s
    rwa [Measure.smul_apply, smul_eq_mul] at this
  obtain ⟨j₀, hj₀⟩ : ∃ j, (t j : ℝ≥0∞) ≠ 0 := by
    by_contra h
    push Not at h
    simp [h] at hsum
  have hμpos : ∀ x, μ (PiNat.cylinder x n) ≠ 0 := fun x h ↦ by
    have := hle j₀ (PiNat.cylinder x n)
    rw [h, nonpos_iff_eq_zero, mul_eq_zero] at this
    exact this.elim hj₀ (hpos j₀ x n)
  rw [hlin]
  constructor
  · exact Finset.sum_le_sum fun j _ ↦ mul_le_mul_right
      (lintegral_infoBits_cylinder_le (μs j) μ n (hpos j · n) hμpos) _
  · rw [← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun j _ ↦ ?_
    rw [← mul_add]
    refine mul_le_mul_right ?_ _
    calc ∫⁻ x, infoBits (μ (PiNat.cylinder x n)) ∂μs j
        ≤ ∫⁻ x, (infoBits (μs j (PiNat.cylinder x n)) + infoBits (t j)) ∂μs j :=
          lintegral_mono fun x ↦ (infoBits_antitone (hle j _)).trans <| by
            rw [add_comm]; exact infoBits_mul_le_add _ _
      _ = _ := by
          rw [lintegral_add_right _ measurable_const, lintegral_const, measure_univ, mul_one]

/-- The lower and upper limits of `f(v_n)`, for a sequence `v_n` in a compact set and a
continuous real function `f`, are the least and the greatest values of `f` on the set of
accumulation points of `(v_n)`. -/
theorem isLeast_isGreatest_image_mapClusterPt {E : Type*} [TopologicalSpace E]
    [FirstCountableTopology E] {K : Set E} (hK : IsCompact K) {v : ℕ → E} (hv : ∀ n, v n ∈ K)
    {f : E → ℝ} (hf : Continuous f) :
    IsLeast (f '' {c | MapClusterPt c atTop v}) (liminf (f ∘ v) atTop) ∧
      IsGreatest (f '' {c | MapClusterPt c atTop v}) (limsup (f ∘ v) atTop) := by
  obtain ⟨B, hB⟩ := (hK.image hf).isBounded.exists_norm_le
  have hb : ∀ n, |f (v n)| ≤ B := fun n ↦ hB _ ⟨v n, hv n, rfl⟩
  have hbl : IsBoundedUnder (· ≥ ·) atTop (f ∘ v) := isBoundedUnder_of ⟨-B, fun n ↦ by
    have := hb n; simp only [Function.comp]; linarith [neg_abs_le (f (v n))]⟩
  have hbu : IsBoundedUnder (· ≤ ·) atTop (f ∘ v) := isBoundedUnder_of ⟨B, fun n ↦ by
    have := hb n; simp only [Function.comp]; linarith [le_abs_self (f (v n))]⟩
  -- a cluster value `L` of `f ∘ v` is the value of `f` at a cluster point of `v`
  have attain : ∀ L, MapClusterPt L atTop (f ∘ v) → L ∈ f '' {c | MapClusterPt c atTop v} := by
    intro L hL
    obtain ⟨ψ, hψ, hψL⟩ := hL.tendsto_subseq
    obtain ⟨c, -, φ, hφ, hc⟩ := hK.tendsto_subseq fun n ↦ hv (ψ n)
    refine ⟨c, MapClusterPt.of_comp ((hψ.comp hφ).tendsto_atTop) hc.mapClusterPt, ?_⟩
    exact tendsto_nhds_unique ((hf.tendsto c).comp hc) (hψL.comp hφ.tendsto_atTop)
  refine ⟨⟨attain _ (MapClusterPt.liminf hbu.isCoboundedUnder_ge hbl), ?_⟩,
    ⟨attain _ (MapClusterPt.limsup hbl.isCoboundedUnder_le hbu), ?_⟩⟩
  · rintro _ ⟨c, hc, rfl⟩
    exact (hc.continuousAt_comp hf.continuousAt).liminf_le hbl
  · rintro _ ⟨c, hc, rfl⟩
    exact (hc.continuousAt_comp hf.continuousAt).le_limsup hbu

/-- Remark 6.9 (support-function form). Let `μ = ∑_j t_j μ_j` be a finite mixture of
probability measures on Cantor space, `A_j(n) = (1/n) H_{μ_j}(ξ^n)` (`cylinderInfoRate`), and
`C ⊆ ℝ^k` the set of accumulation points of the vectors `(A_1(n), …, A_k(n))`. Then
`H̲_μ(σ) = min_{c ∈ C} ⟨t, c⟩` and `H̄_μ(σ) = max_{c ∈ C} ⟨t, c⟩` (both extrema are attained).
The vectors lie in the cube `[0, 1]^k` (`lintegral_infoBits_cylinder_le_length`), so `C` is
nonempty and compact; the proof combines `lintegral_infoBits_mixture_bounds` (the `O(1/n)`
error) with `isLeast_isGreatest_image_mapClusterPt`. Divergence: the positivity of the
cylinders of every component is assumed (needed for the Gibbs step). -/
theorem informationRate_mixture_isLeast_isGreatest {ι : Type*} [Fintype ι] (t : ι → ℝ≥0)
    (ht : ∑ j, t j = 1) (μs : ι → Measure (ℕ → Bool)) [∀ j, IsProbabilityMeasure (μs j)]
    (hpos : ∀ j x n, μs j (PiNat.cylinder x n) ≠ 0) :
    (∃ m : ℝ, IsLeast ((fun c : ι → ℝ ↦ ∑ j, (t j : ℝ) * c j) ''
          {c | MapClusterPt c atTop fun n j ↦ cylinderInfoRate (μs j) n}) m ∧
        (informationRate (Measure.sum fun j ↦ (t j : ℝ≥0∞) • μs j) shiftMap).1 =
          ENNReal.ofReal m) ∧
      ∃ M : ℝ, IsGreatest ((fun c : ι → ℝ ↦ ∑ j, (t j : ℝ) * c j) ''
          {c | MapClusterPt c atTop fun n j ↦ cylinderInfoRate (μs j) n}) M ∧
        (informationRate (Measure.sum fun j ↦ (t j : ℝ≥0∞) • μs j) shiftMap).2 =
          ENNReal.ofReal M := by
  set μ := Measure.sum fun j ↦ (t j : ℝ≥0∞) • μs j with hμ
  set a : ι → ℕ → ℝ≥0∞ := fun j n ↦ ∫⁻ x, infoBits (μs j (PiNat.cylinder x n)) ∂μs j with ha
  have hale : ∀ j n, a j n ≤ n := fun j n ↦
    lintegral_infoBits_cylinder_le_length (μs j) n (hpos j · n)
  have hat : ∀ j n, a j n ≠ ⊤ := fun j n ↦
    ne_top_of_le_ne_top (ENNReal.natCast_ne_top n) (hale j n)
  set v : ℕ → ι → ℝ := fun n j ↦ cylinderInfoRate (μs j) n with hv
  set f : (ι → ℝ) → ℝ := fun c ↦ ∑ j, (t j : ℝ) * c j with hf
  have hfc : Continuous f :=
    continuous_finsetSum _ fun j _ ↦ continuous_const.mul (continuous_apply j)
  have hvK : ∀ n, v n ∈ Set.pi univ fun _ : ι ↦ Icc (0 : ℝ) 1 := fun n j _ ↦
    ⟨ENNReal.toReal_nonneg, ENNReal.toReal_le_of_le_ofReal zero_le_one (by
      rw [ENNReal.ofReal_one]
      exact ENNReal.div_le_of_le_mul (by rw [one_mul]; exact hale j n))⟩
  obtain ⟨h1, h2⟩ := isLeast_isGreatest_image_mapClusterPt
    (isCompact_univ_pi fun _ ↦ isCompact_Icc) hvK hfc
  -- `f (v n) = S n / n` with `S n = ∑_j t_j H_{μ_j}(ξ^n)`
  set S : ℕ → ℝ := fun n ↦ ∑ j, (t j : ℝ) * (a j n).toReal with hS
  have hfv : ∀ n, f (v n) = S n / n := fun n ↦ by
    simp only [hf, hv, hS, ha, cylinderInfoRate, Finset.sum_div, ENNReal.toReal_div,
      ENNReal.toReal_natCast, mul_div_assoc]
  have hSa : ∀ n, (∑ j, (t j : ℝ≥0∞) * a j n).toReal = S n := fun n ↦ by
    rw [ENNReal.toReal_sum fun j _ ↦ ENNReal.mul_ne_top ENNReal.coe_ne_top (hat j n)]
    simp only [ENNReal.toReal_mul, ENNReal.coe_toReal, hS]
  -- the mean information of the mixture
  set J : ℕ → ℝ≥0∞ := fun n ↦ ∫⁻ x, infoBits (μ (PiNat.cylinder x n)) ∂μ
  set Ht := ∑ j, (t j : ℝ≥0∞) * infoBits (t j)
  have hHt : Ht ≠ ⊤ := by
    have hsum : ∑ j, (t j : ℝ≥0∞) = 1 := by
      rw [← ENNReal.ofNNReal_finsetSum, ht, ENNReal.coe_one]
    have := weightEntropy_ne_top (fun j ↦ (t j : ℝ≥0∞)) hsum
    rwa [tsum_fintype] at this
  have hb := fun n ↦ lintegral_infoBits_mixture_bounds t ht μs hpos n
  have hsumt : ∀ n, ∑ j, (t j : ℝ≥0∞) * a j n ≠ ⊤ := fun n ↦
    ENNReal.sum_ne_top.2 fun j _ ↦ ENNReal.mul_ne_top ENNReal.coe_ne_top (hat j n)
  have hfin : ∀ n, J n ≠ ⊤ := fun n ↦
    ne_top_of_le_ne_top (ENNReal.add_ne_top.2 ⟨hsumt n, hHt⟩) (hb n).2
  have hlo : ∀ n, S n ≤ (J n).toReal := fun n ↦ by
    rw [← hSa]; exact ENNReal.toReal_mono (hfin n) (hb n).1
  have hhi : ∀ n, (J n).toReal ≤ S n + Ht.toReal := fun n ↦ by
    rw [← hSa, ← ENNReal.toReal_add (hsumt n) hHt]
    exact ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hsumt n, hHt⟩) (hb n).2
  have h : (fun n : ℕ ↦ J n / n) =ᶠ[atTop] fun n ↦ ENNReal.ofReal ((J n).toReal / n) :=
    (eventually_ge_atTop 1).mono fun n hn ↦ by
      dsimp only
      rw [← ofReal_div_natCast hn, ENNReal.ofReal_toReal (hfin n)]
  have hd : Tendsto (fun n : ℕ ↦ (J n).toReal / n - (f ∘ v) n) atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ (tendsto_const_div_atTop_nhds_zero_nat Ht.toReal)
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    rw [Function.comp_apply, hfv, ← sub_div, Real.norm_eq_abs, abs_div, abs_of_pos hn',
      abs_of_nonneg (sub_nonneg.2 (hlo n))]
    exact div_le_div_of_nonneg_right (by linarith [hhi n]) hn'.le
  have hrate : informationRate μ shiftMap =
      (liminf (fun n ↦ ENNReal.ofReal ((f ∘ v) n)) atTop,
        limsup (fun n ↦ ENNReal.ofReal ((f ∘ v) n)) atTop) := by
    rw [informationRate_shiftMap (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num)
      (fun _ _ ↦ cantorMetricSpace_dist_eq)]
    change (liminf (fun n : ℕ ↦ J n / n) atTop, limsup (fun n : ℕ ↦ J n / n) atTop) = _
    rw [liminf_congr h, limsup_congr h, (liminf_limsup_ofReal_congr hd).1,
      (liminf_limsup_ofReal_congr hd).2]
  -- `f ∘ v` takes values in `[0, 1]`
  have hfv1 : ∀ n, |(f ∘ v) n| ≤ 1 := fun n ↦ by
    have h0 : 0 ≤ (f ∘ v) n := Finset.sum_nonneg fun j _ ↦ mul_nonneg (t j).2 (hvK n j trivial).1
    have h1 : (f ∘ v) n ≤ 1 := by
      calc (f ∘ v) n ≤ ∑ j, (t j : ℝ) * 1 :=
            Finset.sum_le_sum fun j _ ↦ mul_le_mul_of_nonneg_left (hvK n j trivial).2 (t j).2
        _ = 1 := by simp only [mul_one]; rw [← NNReal.coe_sum, ht, NNReal.coe_one]
    rw [abs_of_nonneg h0]; exact h1
  have hbl : IsBoundedUnder (· ≥ ·) atTop (f ∘ v) := isBoundedUnder_of ⟨-1, fun n ↦ by
    linarith [neg_abs_le ((f ∘ v) n), hfv1 n]⟩
  have hbu : IsBoundedUnder (· ≤ ·) atTop (f ∘ v) := isBoundedUnder_of ⟨1, fun n ↦ by
    linarith [le_abs_self ((f ∘ v) n), hfv1 n]⟩
  refine ⟨⟨_, h1, ?_⟩, ⟨_, h2, ?_⟩⟩
  · rw [hrate]
    exact (ENNReal.ofReal_mono.map_liminf_of_continuousAt _
      ENNReal.continuous_ofReal.continuousAt hbu.isCoboundedUnder_ge hbl).symm
  · rw [hrate]
    exact (ENNReal.ofReal_mono.map_limsup_of_continuousAt _
      ENNReal.continuous_ofReal.continuousAt hbu hbl.isCoboundedUnder_le).symm

/-- Remark 6.9, consequence: the lower and upper information rates of the mixture
`∑_j t_j μ_j` coincide for all mixing weights `t` in the simplex exactly when the set `C` of
accumulation points of `(A_1(n), …, A_k(n))` is a single point (`C` is nonempty, so
"subsingleton" is "point"). The weights at the vertices of the simplex suffice for the direct
implication. Same hypotheses as `informationRate_mixture_isLeast_isGreatest`.
Blueprint node `meas:remarks`. -/
theorem informationRate_mixture_fst_eq_snd_iff {ι : Type*} [Fintype ι]
    (μs : ι → Measure (ℕ → Bool)) [∀ j, IsProbabilityMeasure (μs j)]
    (hpos : ∀ j x n, μs j (PiNat.cylinder x n) ≠ 0) :
    (∀ t : ι → ℝ≥0, ∑ j, t j = 1 →
        (informationRate (Measure.sum fun j ↦ (t j : ℝ≥0∞) • μs j) shiftMap).1 =
          (informationRate (Measure.sum fun j ↦ (t j : ℝ≥0∞) • μs j) shiftMap).2) ↔
      {c : ι → ℝ | MapClusterPt c atTop fun n j ↦ cylinderInfoRate (μs j) n}.Subsingleton := by
  classical
  set C := {c : ι → ℝ | MapClusterPt c atTop fun n j ↦ cylinderInfoRate (μs j) n}
  -- the accumulation points have nonnegative coordinates
  have hC0 : ∀ c ∈ C, ∀ j, 0 ≤ c j := fun c hc j ↦
    (isClosed_le continuous_const (continuous_apply j)).mem_of_mapClusterPt hc
      (Eventually.of_forall fun _ ↦ ENNReal.toReal_nonneg)
  constructor
  · intro h c₁ hc₁ c₂ hc₂
    funext j
    have hsj : ∑ i, (Pi.single j 1 : ι → ℝ≥0) i = 1 := by simp
    obtain ⟨⟨m, hm, e1⟩, ⟨M, hM, e2⟩⟩ :=
      informationRate_mixture_isLeast_isGreatest _ hsj μs hpos
    have hval : ∀ c : ι → ℝ, ∑ i, ((Pi.single j 1 : ι → ℝ≥0) i : ℝ) * c i = c j := fun c ↦ by
      rw [Finset.sum_eq_single j (fun i _ hi ↦ by simp [hi]) (by simp)]
      simp
    obtain ⟨c₀, hc₀, rfl⟩ := hm.1
    have hm0 : 0 ≤ ∑ i, ((Pi.single j 1 : ι → ℝ≥0) i : ℝ) * c₀ i := by
      rw [hval]; exact hC0 c₀ hc₀ j
    have hmM : ∑ i, ((Pi.single j 1 : ι → ℝ≥0) i : ℝ) * c₀ i = M := by
      have := (h _ hsj).symm
      rw [e1, e2] at this
      exact le_antisymm (hM.2 ⟨c₀, hc₀, rfl⟩)
        ((ENNReal.ofReal_le_ofReal_iff hm0).1 this.le)
    have l1 := hm.2 ⟨c₁, hc₁, rfl⟩
    have l2 := hm.2 ⟨c₂, hc₂, rfl⟩
    have u1 := hM.2 ⟨c₁, hc₁, rfl⟩
    have u2 := hM.2 ⟨c₂, hc₂, rfl⟩
    simp only [hval] at l1 l2 u1 u2 hmM
    linarith
  · intro h t ht
    obtain ⟨⟨m, hm, e1⟩, ⟨M, hM, e2⟩⟩ := informationRate_mixture_isLeast_isGreatest t ht μs hpos
    obtain ⟨c₁, hc₁, rfl⟩ := hm.1
    obtain ⟨c₂, hc₂, rfl⟩ := hM.1
    rw [e1, e2, h hc₁ hc₂]

end supportFunction

/-! ### Remark 7.2: entropy and cross-entropy of Bernoulli measures -/

section crossEntropy

attribute [local instance] cantorMetricSpace

/-- The cross-entropy in bits `H(q‖p) = -q log₂ p - (1 - q) log₂ (1 - p)`: the mean, under the
Bernoulli law of parameter `q`, of the information `bitInfo p` of one symbol under the
Bernoulli law of parameter `p`. Blueprint node `meas:remarks`. -/
noncomputable def crossEntropyBits (q p : ℝ) : ℝ :=
  q * bitInfo p true + (1 - q) * bitInfo p false

/-- The cross-entropy of a law with itself is its entropy: `H(p‖p) = H(p)`. -/
theorem crossEntropyBits_self (p : ℝ) :
    crossEntropyBits p p = Real.binEntropy p / Real.log 2 :=
  mean_bitInfo p

/-- Gibbs' inequality for one symbol: `H(q) ≤ H(q‖p)` for `0 < p < 1` and `0 ≤ q ≤ 1`.
Blueprint node `meas:remarks`. -/
theorem binEntropy_div_log_two_le_crossEntropyBits {p q : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    Real.binEntropy q / Real.log 2 ≤ crossEntropyBits q p := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  -- `a (log₂ b - log₂ a) ≤ (b - a) / log 2` for `a ≥ 0`, `b > 0`
  have key : ∀ a b : ℝ, 0 ≤ a → 0 < b →
      a * (Real.logb 2 b - Real.logb 2 a) ≤ (b - a) / Real.log 2 := by
    intro a b ha hb
    rcases ha.eq_or_lt with rfl | ha
    · simp only [zero_mul, sub_zero]; positivity
    have h := Real.log_le_sub_one_of_pos (div_pos hb ha)
    rw [Real.log_div hb.ne' ha.ne'] at h
    rw [Real.logb, Real.logb, ← sub_div, mul_div_assoc', div_le_div_iff_of_pos_right hlog2]
    calc a * (Real.log b - Real.log a) ≤ a * (b / a - 1) := mul_le_mul_of_nonneg_left h ha.le
      _ = b - a := by field_simp
  have k1 := key q p hq0 hp0
  have k2 := key (1 - q) (1 - p) (by linarith) (by linarith)
  have h0 : (p - q) / Real.log 2 + ((1 - p) - (1 - q)) / Real.log 2 = 0 := by
    rw [← add_div, show (p - q) + ((1 - p) - (1 - q)) = 0 by ring, zero_div]
  rw [← mean_bitInfo q]
  simp only [crossEntropyBits, bitInfo, ite_true, Bool.false_eq_true, ite_false]
  nlinarith

/-- The strong law for the information of `ν_p` under `ν_q`: `ν_q`-a.e.
`(1/n) ∑_{i<n} Y_i^p(x) → H(q‖p)`, where `Y_i^p(x)` is `-log₂ p` or `-log₂ (1 - p)` according to
`x i` (`bitInfo p`). -/
theorem ae_tendsto_bitInfo_crossEntropy (p q : ℝ≥0) (hq : q ≤ 1) :
    ∀ᵐ x ∂bernoulliMeasure q hq, Tendsto (fun n : ℕ ↦ (∑ i ∈ Finset.range n,
      bitInfo p (x i)) / n) atTop (𝓝 (crossEntropyBits q p)) := by
  have hae := ProbabilityTheory.strong_law_ae_real (μ := bernoulliMeasure q hq)
    (fun (i : ℕ) (w : ℕ → Bool) ↦ bitVal (w i))
    (bernoulli_integrable_coord q hq)
    (fun i j hij ↦ (bernoulli_iIndepFun q hq).indepFun hij)
    (bernoulli_identDistrib q hq)
  rw [bernoulli_integral_coord q hq] at hae
  filter_upwards [hae] with x hx
  have hH : bitInfo p false + (bitInfo p true - bitInfo p false) * q =
      crossEntropyBits q p := by
    rw [crossEntropyBits]; ring
  have hlim : Tendsto (fun n : ℕ ↦ bitInfo p false + (bitInfo p true - bitInfo p false) *
      ((∑ i ∈ Finset.range n, bitVal (x i)) / n)) atTop (𝓝 (crossEntropyBits q p)) :=
    hH ▸ tendsto_const_nhds.add (hx.const_mul _)
  refine hlim.congr' ((eventually_ge_atTop 1).mono fun n hn ↦ ?_)
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.one_le_iff_ne_zero.1 hn)
  have hsum : ∑ i ∈ Finset.range n, bitInfo p (x i) =
      ∑ i ∈ Finset.range n, (bitInfo p false + (bitInfo p true - bitInfo p false) *
        bitVal (x i)) :=
    Finset.sum_congr rfl fun i _ ↦ by cases x i <;> simp [bitVal]
  dsimp only
  rw [hsum, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
    ← Finset.mul_sum]
  field_simp

/-- Remark 7.2, last sentence (almost-everywhere form): for Bernoulli measures `ν_p`, `ν_q`
on Cantor space with `0 < p < 1`, `ν_q`-almost every point has local entropies
`Φ_{ν_p}(x) = (H(q‖p), H(q‖p))` under the shift (strong law of large numbers under `ν_q`).
Divergence: the paper's "pointwise" (every `ν_q`-random point) is
`localEntropy_bernoulliMeasure_eq_crossEntropy_of_mem_randomPoints`. No hypothesis on `q`.
Blueprint node `meas:remarks`. -/
theorem ae_localEntropy_bernoulliMeasure_crossEntropy (p : ℝ≥0) (hp : p ≤ 1) (hp0 : 0 < p)
    (hp1 : p < 1) (q : ℝ≥0) (hq : q ≤ 1) :
    ∀ᵐ x ∂bernoulliMeasure q hq, localEntropy (bernoulliMeasure p hp) shiftMap x =
      (ENNReal.ofReal (crossEntropyBits q p), ENNReal.ofReal (crossEntropyBits q p)) := by
  filter_upwards [ae_tendsto_bitInfo_crossEntropy p q hq] with x hx
  rw [localEntropy_shiftMap (by norm_num) (by norm_num) (fun _ _ ↦ cantorMetricSpace_dist_eq)]
  simp only [infoBits_bernoulliMeasure_cylinder p hp hp0 hp1]
  have h' : Tendsto (fun n : ℕ ↦ ENNReal.ofReal (∑ i ∈ Finset.range n, bitInfo p (x i)) / n)
      atTop (𝓝 (ENNReal.ofReal (crossEntropyBits q p))) := by
    refine (ENNReal.tendsto_ofReal hx).congr' ((eventually_ge_atTop 1).mono fun n hn ↦ ?_)
    exact (ofReal_div_natCast hn).symm
  rw [h'.liminf_eq, h'.limsup_eq]

/-- Remark 7.2, last sentence (almost-everywhere form): for `0 < p, q < 1`, `ν_q`-almost
everywhere `Φ_{ν_q}(x) = (H(q), H(q)) ≤ (H(q‖p), H(q‖p)) = Φ_{ν_p}(x)` coordinatewise: the
inequality `Φ_{ν_q} ≤ Φ_{ν_p}` is the inequality between entropy and cross-entropy.
Blueprint node `meas:remarks`. -/
theorem ae_localEntropy_bernoulliMeasure_le_crossEntropy (p : ℝ≥0) (hp : p ≤ 1) (hp0 : 0 < p)
    (hp1 : p < 1) (q : ℝ≥0) (hq : q ≤ 1) (hq0 : 0 < q) (hq1 : q < 1) :
    ∀ᵐ x ∂bernoulliMeasure q hq,
      localEntropy (bernoulliMeasure q hq) shiftMap x = (binEntropyBits q, binEntropyBits q) ∧
      localEntropy (bernoulliMeasure p hp) shiftMap x =
        (ENNReal.ofReal (crossEntropyBits q p), ENNReal.ofReal (crossEntropyBits q p)) ∧
      binEntropyBits q ≤ ENNReal.ofReal (crossEntropyBits q p) := by
  filter_upwards [ae_localEntropy_bernoulliMeasure q hq hq0 hq1,
    ae_localEntropy_bernoulliMeasure_crossEntropy p hp hp0 hp1 q hq] with x h1 h2
  exact ⟨h1, h2, ENNReal.ofReal_le_ofReal (binEntropy_div_log_two_le_crossEntropyBits
    (by exact_mod_cast hp0) (by exact_mod_cast hp1) q.2 (by exact_mod_cast hq))⟩

/-- Remark 7.2, first sentence specialised to two Bernoulli measures: if the oracle `A` is
admissible for both `ν_p` and `ν_q`, then at every `ν_q`-random point (relative to `A`)
`Φ_{ν_q}(x) = Ψ^A(x) ≤ Φ_{ν_p}(x)` coordinatewise (Theorem 3.3 for both measures). No
hypothesis on `p`, `q`. Blueprint node `meas:remarks`. -/
theorem localEntropy_bernoulliMeasure_le_of_mem_randomPoints (P : Presentation (ℕ → Bool))
    (A : Set ℕ) (p : ℝ≥0) (hp : p ≤ 1) (q : ℝ≥0) (hq : q ≤ 1)
    (hAp : IsMeasureAdmissible P shiftMap (bernoulliMeasure p hp) A)
    (hAq : IsMeasureAdmissible P shiftMap (bernoulliMeasure q hq) A) {x : ℕ → Bool}
    (hx : x ∈ randomPoints P A (bernoulliMeasure q hq)) :
    (localEntropy (bernoulliMeasure q hq) shiftMap x).1 ≤
        (localEntropy (bernoulliMeasure p hp) shiftMap x).1 ∧
      (localEntropy (bernoulliMeasure q hq) shiftMap x).2 ≤
        (localEntropy (bernoulliMeasure p hp) shiftMap x).2 := by
  rw [← orbitComplexities_eq_localEntropy P shiftMap continuous_shiftMap_cantor A _ hAq hx]
  exact orbitComplexities_le_localEntropy P shiftMap continuous_shiftMap_cantor A _ prob_le_one
    hAp x

end crossEntropy

/-! ### Remark 8.5: the Bowen equation at random points and conformal maps -/

section bowenEquation

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

omit [MetricSpace X] [MeasurableSpace X] [BorelSpace X] in
/-- If `0 < u̲(x)` and `ū(x) < ∞`, the averages `S_n u(x) / n`, `n ≥ 1`, are bounded, so every
multiple `-s u` satisfies the hypothesis `inf_n S_n(-s u)(x) / n > -∞` of Theorem 8.3.
Blueprint node `meas:remarks`. -/
theorem birkhoffBoundedBelow_smul_of_averages (T : X → X) (u : X → ℝ) (x : X)
    (hpos : 0 < lowerBirkhoffAverage T u x) (hupper : upperBirkhoffAverage T u x < ⊤) (s : ℝ) :
    BirkhoffBoundedBelow T (fun y ↦ -s * u y) x := by
  obtain ⟨M, hM, -⟩ := EReal.lt_iff_exists_real_btwn.1 hupper
  have h1 : ∀ᶠ n : ℕ in atTop, ((birkhoffSum T u n x / n : ℝ) : EReal) < M :=
    eventually_lt_of_limsup_lt hM
  have h2 : ∀ᶠ n : ℕ in atTop, (0 : EReal) < ((birkhoffSum T u n x / n : ℝ) : EReal) :=
    eventually_lt_of_lt_liminf hpos
  obtain ⟨N, hN⟩ := eventually_atTop.1 (h1.and h2)
  set B := |M| + ∑ k ∈ Finset.range N, |birkhoffSum T u k x / k|
  have hB : ∀ n : ℕ, |birkhoffSum T u n x / n| ≤ B := by
    intro n
    have hs : 0 ≤ ∑ k ∈ Finset.range N, |birkhoffSum T u k x / k| :=
      Finset.sum_nonneg fun _ _ ↦ abs_nonneg _
    rcases lt_or_ge n N with hn | hn
    · have := Finset.single_le_sum (f := fun k : ℕ ↦ |birkhoffSum T u k x / k|)
        (fun _ _ ↦ abs_nonneg _) (Finset.mem_range.2 hn)
      linarith [abs_nonneg M]
    · obtain ⟨h1, h2⟩ := hN n hn
      have h1' : birkhoffSum T u n x / n < M := EReal.coe_lt_coe_iff.1 h1
      have h2' : 0 < birkhoffSum T u n x / n := EReal.coe_pos.1 h2
      rw [abs_of_pos h2']
      linarith [le_abs_self M]
  refine ⟨-(|s| * B), fun n _ ↦ ?_⟩
  have hS : birkhoffSum T (fun y ↦ -s * u y) n x = -s * birkhoffSum T u n x := by
    simp only [birkhoffSum, Finset.mul_sum]
  rw [hS, mul_div_assoc]
  have h : |-s * (birkhoffSum T u n x / n)| ≤ |s| * B := by
    rw [abs_mul, abs_neg]; exact mul_le_mul_of_nonneg_left (hB n) (abs_nonneg s)
  linarith [neg_abs_le (-s * (birkhoffSum T u n x / n))]

/-- Theorem 8.3(ii) for the potentials `-s u`: at a `μ`-random point with `0 < u̲(x)` and
`ū(x) < ∞`, the local pressures of `-s u` are the pointwise pressures, for every real `s`.
Blueprint node `meas:remarks`. -/
theorem localPressure_smul_eq_pointwisePressure (P : Presentation X) (T : X → X)
    (hT : Continuous T) (u : X → ℝ) (hu : UniformContinuous u) (A : Set ℕ) (μ : Measure X)
    [IsProbabilityMeasure μ] (hA : IsMeasureAdmissible P T μ A) {x : X}
    (hxr : x ∈ randomPoints P A μ) (hpos : 0 < lowerBirkhoffAverage T u x)
    (hupper : upperBirkhoffAverage T u x < ⊤) (s : ℝ) :
    localPressure μ T (fun y ↦ -s * u y) x = pointwisePressure P T (fun y ↦ -s * u y) A x :=
  (pointwisePressure_eq_localPressure P T hT _ (hu.const_smul (-s)) A μ hA hxr
    (birkhoffBoundedBelow_smul_of_averages T u x hpos hupper s)).symm

/-- At a `μ`-random point the pointwise pressures of the zero potential (the orbit
complexities `K̲^A(x, T)`, `K̄^A(x, T)`) are the local entropies of `μ`.
Blueprint node `meas:remarks`. -/
theorem pointwisePressure_zero_eq_localEntropy (P : Presentation X) (T : X → X)
    (hT : Continuous T) (A : Set ℕ) (μ : Measure X) [IsProbabilityMeasure μ]
    (hA : IsMeasureAdmissible P T μ A) {x : X} (hxr : x ∈ randomPoints P A μ) :
    pointwisePressure P T (fun _ ↦ 0) A x =
      (((localEntropy μ T x).1 : EReal), ((localEntropy μ T x).2 : EReal)) := by
  rw [pointwisePressure_eq_localPressure P T hT _ uniformContinuous_const A μ hA hxr
    ⟨0, fun n _ ↦ by simp [birkhoffSum]⟩, localPressure_zero μ prob_le_one T x]

omit [MeasurableSpace X] [BorelSpace X] in
/-- The pointwise Bowen equation [Din, Thm. C] in the form used by Remark 8.5: if
`0 < u̲(x)`, `ū(x) < ∞` and the relevant pointwise pressure of the zero potential is finite,
then the pointwise BS dimension `d = dim^A_BS(x, T, u)` (lower or upper according to `σ`) is
finite and is the unique real root `s` of `P^A(x, T, -s u) = 0`.

This is `pointwiseBowenEquation_finite` together with `pointwiseBowenEquation_unique`
(`PointToSet/BowenEquation/`). Blueprint node `meas:remarks`. -/
theorem pointwiseBowenEquation_root (P : Presentation X) (T : X → X) (hT : Continuous T)
    (u : X → ℝ) (hu : UniformContinuous u) (A : Set ℕ) (x : X)
    (hpos : 0 < lowerBirkhoffAverage T u x) (hupper : upperBirkhoffAverage T u x < ⊤)
    (σ : LimitSide) (hfinite : σ.choose (pointwisePressure P T (fun _ ↦ 0) A x) < ⊤) :
    σ.choose (pointwiseBSDimension P T u A x) < ⊤ ∧
      ∀ s : ℝ, σ.choose (pointwisePressure P T (fun y ↦ -s * u y) A x) = 0 ↔
        s = (σ.choose (pointwiseBSDimension P T u A x)).toReal := by
  exact ⟨pointwiseBowenEquation_finite P T u hu A x hpos hupper σ hfinite,
    pointwiseBowenEquation_unique P T hT u hu A x hpos hupper σ hfinite⟩

/-- Remark 8.5 (Bowen equation at random points): let `A` be admissible for `(X, d, T, μ)`,
`x` a `μ`-random point with `0 < u̲(x) ≤ ū(x) < ∞` and finite lower (for `σ = lower`) or upper
(for `σ = upper`) local entropy. Then the local BS dimension `d̲_μ(x, T, u)` (resp.
`d̄_μ(x, T, u)`) is finite and is the unique real root `s` of `P̲_μ(x, T, -s u) = 0` (resp.
`P̄_μ(x, T, -s u) = 0`). Divergences: the paper states the lower case only; the hypothesis
`K̲^A(x, T) < ∞` is replaced by the equivalent (at random points, Theorem 3.3) `h̲_μ(x, T) < ∞`;
`u` is uniformly continuous (as in Theorem 8.3). The proof transfers the pointwise Bowen
equation `pointwiseBowenEquation_root` through Theorem 8.3(ii). Blueprint node
`meas:remarks`. -/
theorem localBowenEquation (P : Presentation X) (T : X → X) (hT : Continuous T) (u : X → ℝ)
    (hu : UniformContinuous u) (A : Set ℕ) (μ : Measure X) [IsProbabilityMeasure μ]
    (hA : IsMeasureAdmissible P T μ A) {x : X} (hxr : x ∈ randomPoints P A μ)
    (hpos : 0 < lowerBirkhoffAverage T u x) (hupper : upperBirkhoffAverage T u x < ⊤)
    (σ : LimitSide) (hfinite : σ.choose (localEntropy μ T x) < ⊤) :
    σ.choose (localBSDimension μ T u x) < ⊤ ∧
      ∀ s : ℝ, σ.choose (localPressure μ T (fun y ↦ -s * u y) x) = 0 ↔
        s = (σ.choose (localBSDimension μ T u x)).toReal := by
  have hfin : σ.choose (pointwisePressure P T (fun _ ↦ 0) A x) < ⊤ := by
    rw [pointwisePressure_zero_eq_localEntropy P T hT A μ hA hxr]
    cases σ <;> simp only [LimitSide.choose] at hfinite ⊢ <;>
      exact lt_of_lt_of_le (EReal.coe_ennreal_lt_coe_ennreal_iff.2 hfinite) le_top
  obtain ⟨h1, h2⟩ := pointwiseBowenEquation_root P T hT u hu A x hpos hupper σ hfin
  rw [← pointwiseBSDimension_eq_localBSDimension P T hT u hu A μ hA hxr hpos]
  refine ⟨h1, fun s ↦ ?_⟩
  rw [localPressure_smul_eq_pointwisePressure P T hT u hu A μ hA hxr hpos hupper s]
  exact h2 s

omit [MeasurableSpace X] [BorelSpace X] in
/-- The diagonal potential of uniform conformal data is uniformly continuous (the
library's `distortionModuli`). -/
theorem uniformContinuous_conformalPotential (C : UniformConformalData X) :
    UniformContinuous C.potential :=
  C.uniformContinuous_ζ.comp
    ((uniformContinuous_id.prodMk uniformContinuous_id).subtype_mk fun _ ↦ by
      simpa using C.r₀_pos)

omit [MeasurableSpace X] [BorelSpace X] in
/-- Theorem E of [Din] at the level of points: on the conformal locus the static point
dimensions relative to `A` (the algorithmic dimensions) are the pointwise BS dimensions of the
potential.

This is `pointwiseDimensionEqBS` together with `pointwiseDimensionEqBS_upper`
(`PointToSet/Conformal/Distortion/PointwiseDimension.lean`). Blueprint node `meas:remarks`. -/
theorem staticPointDimensions_eq_pointwiseBSDimension_conformal (P : Presentation X)
    (C : UniformConformalData X) (A : Set ℕ) (x : X) (hx : x ∈ conformalLocus C) :
    staticPointDimensions P A x = pointwiseBSDimension P C.T C.potential A x := by
  exact Prod.ext (pointwiseDimensionEqBS P C A x hx) (pointwiseDimensionEqBS_upper P C A x hx)

/-- Remark 8.5 (conformal maps), first step: for uniform conformal data `C` with potential
`u = C.potential` (the logarithm of the derivative), an oracle `A` admissible for
`(X, d, C.T, μ)` and a `μ`-random point `x` of the conformal locus of Theorem E, the
algorithmic (static point) dimensions of `x` relative to `A` are the local BS dimensions
`(d̲_μ(x, T, u), d̄_μ(x, T, u))` (Theorem E with Theorem 8.3(ii)). The paper states the lower
one. Blueprint node `meas:remarks`. -/
theorem staticPointDimensions_eq_localBSDimension_conformal (P : Presentation X)
    (C : UniformConformalData X) (A : Set ℕ) (μ : Measure X) [IsProbabilityMeasure μ]
    (hA : IsMeasureAdmissible P C.T μ A) {x : X} (hxr : x ∈ randomPoints P A μ)
    (hx : x ∈ conformalLocus C) :
    staticPointDimensions P A x = localBSDimension μ C.T C.potential x := by
  rw [staticPointDimensions_eq_pointwiseBSDimension_conformal P C A x hx]
  exact pointwiseBSDimension_eq_localBSDimension P C.T C.uniformContinuous_T.continuous
    C.potential (uniformContinuous_conformalPotential C) A μ hA hxr hx.1.1.1

/-- The lower and upper local dimensions of `μ` at `x` for round balls,
`liminf_{r → 0+} log μ(B(x, r)) / log r` and the `limsup`, in the normalisation of
`normalizedPrecisionComplexity` (infinite when a ball is null).
Blueprint node `meas:remarks`. -/
noncomputable def localDimension (μ : Measure X) (x : X) : ℝ≥0∞ × ℝ≥0∞ :=
  (liminf (fun r : ℝ ↦ infoBits (μ (Metric.ball x r)) / ENNReal.ofReal (-Real.logb 2 r))
      (𝓝[>] (0 : ℝ)),
    limsup (fun r : ℝ ↦ infoBits (μ (Metric.ball x r)) / ENNReal.ofReal (-Real.logb 2 r))
      (𝓝[>] (0 : ℝ)))

end bowenEquation

end Kolmogorov.PointToSet
