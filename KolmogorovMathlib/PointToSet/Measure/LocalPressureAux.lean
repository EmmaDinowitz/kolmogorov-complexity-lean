/-
Copyright (c) 2026 Emma Dinowitz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emma Dinowitz
-/
import KolmogorovMathlib.PointToSet.Measure.UniversalMeasure
import KolmogorovMathlib.PointToSet.BSDimension.Upper.PointToSetPrinciple

/-!
# Auxiliary lemmas for the local pressure and the local BS dimension (§8)

Elementary facts used in `Measure.LocalPressure` and `Measure.PressurePointwise`
(E. Dinowitz, *Entropy of non-invariant measures and orbit complexity of random points*, §8).

* Comparison lemmas for lower and upper limits: additive real errors in `EReal`
  (`liminf_limsup_le_of_le_add_coe_tendsto_zero`), multiplicative errors in `ℝ≥0∞`
  (`liminf_limsup_le_mul_of_eventually_le`, `iSup_le_iSup_of_eventually_le_mul`), and threshold
  comparisons in `EReal` and `ℝ≥0∞` (`liminf_limsup_le_of_forall_lt_coe`,
  `liminf_limsup_le_of_forall_lt_ofReal`).
* Birkhoff sums: `exists_pos_eventually_mul_le_birkhoffSum` (an eventual linear lower bound at
  points of positive lower Birkhoff average), `tendsto_birkhoffSum_atTop`,
  `abs_birkhoffSum_sub_le_of_oscillation`, and vanishing error terms such as
  `tendsto_div_birkhoffSum_of_tendsto_div`.
* Orbit complexity: `exists_orbitComplexityNat_eq`, `orbitComplexityNat_le_of_radius_le`.
* Information: `neg_logb_toReal_le_of_rpow_le`, `ofReal_two_rpow_neg_add_logb_eq`.
-/

namespace Kolmogorov.PointToSet

open Filter Set MeasureTheory
open scoped Topology ENNReal Computability

variable {X : Type*} [MetricSpace X]

/-! ### Auxiliary facts on limits and Birkhoff sums -/

/-- An eventual comparison with a convergent real additive error bounds the lower limits in
`EReal`, including infinite limits. -/
theorem liminf_le_liminf_add_coe_of_eventually_le (f g : ℕ → EReal) (e : ℕ → ℝ) (ω : ℝ)
    (he : Tendsto e atTop (𝓝 ω)) (hfg : ∀ᶠ n in atTop, f n ≤ g n + (e n : EReal)) :
    liminf f atTop ≤ liminf g atTop + (ω : EReal) := by
  have he' : Tendsto (fun n ↦ (e n : EReal)) atTop (𝓝 (ω : EReal)) :=
    EReal.tendsto_coe.mpr he
  have hlimsup := he'.limsup_eq
  calc liminf f atTop ≤ liminf (fun n ↦ g n + (e n : EReal)) atTop := liminf_le_liminf hfg
    _ ≤ liminf g atTop + (ω : EReal) := by
      have h := EReal.liminf_add_le (u := fun n ↦ (e n : EReal)) (v := g)
        (f := atTop) (Or.inl (by rw [hlimsup]; exact EReal.coe_ne_bot _))
        (Or.inl (by rw [hlimsup]; exact EReal.coe_ne_top _))
      simpa only [Pi.add_def, add_comm, hlimsup] using h

/-- An eventual comparison with a convergent real additive error bounds the upper limits in
`EReal`, including infinite limits. -/
theorem limsup_le_limsup_add_coe_of_eventually_le (f g : ℕ → EReal) (e : ℕ → ℝ) (ω : ℝ)
    (he : Tendsto e atTop (𝓝 ω)) (hfg : ∀ᶠ n in atTop, f n ≤ g n + (e n : EReal)) :
    limsup f atTop ≤ limsup g atTop + (ω : EReal) := by
  have he' : Tendsto (fun n ↦ (e n : EReal)) atTop (𝓝 (ω : EReal)) :=
    EReal.tendsto_coe.mpr he
  have hlimsup := he'.limsup_eq
  calc limsup f atTop ≤ limsup (fun n ↦ g n + (e n : EReal)) atTop := limsup_le_limsup hfg
    _ ≤ limsup g atTop + (ω : EReal) := by
      have h := EReal.limsup_add_le (u := g) (v := fun n ↦ (e n : EReal))
        (f := atTop) (Or.inr (by rw [hlimsup]; exact EReal.coe_ne_top _))
        (Or.inr (by rw [hlimsup]; exact EReal.coe_ne_bot _))
      simpa only [Pi.add_def, hlimsup] using h

/-- If `f n ≤ g n + e n` eventually with real errors `e n → 0`, then `liminf f ≤ liminf g`
and `limsup f ≤ limsup g` in `EReal`. -/
theorem liminf_limsup_le_of_le_add_coe_tendsto_zero {f g : ℕ → EReal} {e : ℕ → ℝ}
    (he : Tendsto e atTop (𝓝 0)) (hfg : ∀ᶠ n in atTop, f n ≤ g n + (e n : EReal)) :
    liminf f atTop ≤ liminf g atTop ∧ limsup f atTop ≤ limsup g atTop := by
  have h1 := liminf_le_liminf_add_coe_of_eventually_le f g e 0 he hfg
  have h2 := limsup_le_limsup_add_coe_of_eventually_le f g e 0 he hfg
  rw [EReal.coe_zero, add_zero] at h1 h2
  exact ⟨h1, h2⟩

/-- A monotone sequence bounded eventually by a fixed extended real plus a vanishing real
error has supremum at most that extended real. -/
theorem iSup_le_of_monotone_of_eventually_le_add_coe (f : ℕ → EReal) (hf : Monotone f)
    (ω : ℕ → ℝ) (hω : Tendsto ω atTop (𝓝 0)) (b : EReal)
    (hbound : ∀ᶠ p in atTop, f p ≤ b + (ω p : EReal)) : (⨆ p, f p) ≤ b := by
  have hzero : Tendsto (fun p ↦ (ω p : EReal)) atTop (𝓝 (0 : EReal)) := by
    simpa only [EReal.coe_zero] using EReal.tendsto_coe.mpr hω
  have hsum : Tendsto (fun p ↦ b + (ω p : EReal)) atTop (𝓝 b) := by
    have h := (EReal.continuousAt_add (p := (b, 0)) (Or.inr EReal.zero_ne_bot)
      (Or.inr EReal.zero_ne_top)).tendsto.comp (tendsto_const_nhds.prodMk_nhds hzero)
    simpa only [add_zero, Function.comp_def] using h
  exact le_of_tendsto_of_tendsto (tendsto_atTop_iSup hf) hsum hbound

/-- Multiplication by a finite constant passes through lower and upper limits in `ℝ≥0∞`. -/
theorem liminf_limsup_le_mul_of_eventually_le {f g : ℕ → ℝ≥0∞} {a : ℝ≥0∞} (ha : a ≠ ⊤)
    (h : ∀ᶠ n in atTop, f n ≤ g n * a) :
    liminf f atTop ≤ liminf g atTop * a ∧ limsup f atTop ≤ limsup g atTop * a := by
  have hmono : Monotone fun t : ℝ≥0∞ ↦ t * a := fun _ _ h ↦ by dsimp only; gcongr
  have hcont : Continuous fun t : ℝ≥0∞ ↦ t * a := ENNReal.continuous_mul_const ha
  exact ⟨(liminf_le_liminf h).trans_eq (hmono.map_liminf_of_continuousAt g hcont.continuousAt).symm,
    (limsup_le_limsup h).trans_eq (hmono.map_limsup_of_continuousAt g hcont.continuousAt).symm⟩

/-- If a monotone sequence is eventually bounded by another one times factors tending to
`1`, its supremum is bounded by the supremum of the other one. -/
theorem iSup_le_iSup_of_eventually_le_mul {F G : ℕ → ℝ≥0∞} (hF : Monotone F) {a : ℕ → ℝ≥0∞}
    (ha : Tendsto a atTop (𝓝 1)) (h : ∀ᶠ p in atTop, F p ≤ G p * a p) :
    ⨆ p, F p ≤ ⨆ p, G p := by
  refine iSup_le fun p ↦ ?_
  have ht : Tendsto (fun q ↦ (⨆ p, G p) * a q) atTop (𝓝 ((⨆ p, G p) * 1)) :=
    ENNReal.Tendsto.const_mul ha (Or.inl one_ne_zero)
  rw [mul_one] at ht
  refine ge_of_tendsto ht ?_
  filter_upwards [h, eventually_ge_atTop p] with q hq hpq
  exact (hF hpq).trans (hq.trans (by gcongr; exact le_iSup G q))

/-- A natural number divided by a positive real, as an extended nonnegative real. -/
theorem natCast_div_ofReal_eq (k : ℕ) {a : ℝ} (ha : 0 < a) :
    (k : ℝ≥0∞) / ENNReal.ofReal a = ENNReal.ofReal ((k : ℝ) / a) := by
  rw [ENNReal.ofReal_div_of_pos ha, ENNReal.ofReal_natCast]

omit [MetricSpace X] in
/-- A positive lower Birkhoff average gives an eventual linear lower bound
`δ n ≤ S_n u(x)` with `δ > 0`. -/
theorem exists_pos_eventually_mul_le_birkhoffSum {T : X → X} {u : X → ℝ} {x : X}
    (hx : 0 < lowerBirkhoffAverage T u x) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ n : ℕ in atTop, δ * n ≤ birkhoffSum T u n x := by
  obtain ⟨b, hb0, hb⟩ := exists_between hx
  have hbt : b ≠ ⊤ := ne_top_of_lt hb
  have hbb : b ≠ ⊥ := ne_bot_of_gt hb0
  have hcb : ((b.toReal : ℝ) : EReal) = b := EReal.coe_toReal hbt hbb
  have hc0 : 0 < b.toReal := by
    have := hb0
    rw [← hcb] at this
    exact_mod_cast this
  refine ⟨b.toReal, hc0, ?_⟩
  filter_upwards [eventually_lt_of_lt_liminf hb, eventually_ge_atTop 1] with n h hn
  rw [← hcb, EReal.coe_lt_coe_iff] at h
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  rw [lt_div_iff₀ hn0] at h
  exact h.le

omit [MetricSpace X] in
/-- At a point of positive lower Birkhoff average the Birkhoff sums tend to infinity. -/
theorem tendsto_birkhoffSum_atTop {T : X → X} {u : X → ℝ} {x : X}
    (hx : 0 < lowerBirkhoffAverage T u x) :
    Tendsto (fun n : ℕ ↦ birkhoffSum T u n x) atTop atTop := by
  obtain ⟨δ, hδ, hev⟩ := exists_pos_eventually_mul_le_birkhoffSum hx
  exact tendsto_atTop_mono' atTop hev (Tendsto.const_mul_atTop hδ tendsto_natCast_atTop_atTop)

/-- A local oscillation bound sums to a Birkhoff bound on a Bowen ball. -/
theorem abs_birkhoffSum_sub_le_of_oscillation (T : X → X) (φ : X → ℝ) {x y : X} {n : ℕ}
    {ε ω : ℝ} (hω : ∀ y z, dist y z < ε → |φ y - φ z| ≤ ω) (hy : y ∈ bowenBall T n x ε) :
    |birkhoffSum T φ n y - birkhoffSum T φ n x| ≤ n * ω := by
  rw [birkhoffSum, birkhoffSum, ← Finset.sum_sub_distrib]
  calc |∑ k ∈ Finset.range n, (φ (T^[k] y) - φ (T^[k] x))|
      ≤ ∑ k ∈ Finset.range n, |φ (T^[k] y) - φ (T^[k] x)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ Finset.range n, ω := by
      refine Finset.sum_le_sum fun k hk ↦ hω _ _ ?_
      rw [dist_comm]
      exact mem_bowenBall_iff.1 hy k (Finset.mem_range.1 hk)
    _ = n * ω := by simp

/-- At a positive radius and a positive time, the orbit complexity is the complexity of an
ideal point of the Bowen ball. -/
theorem exists_orbitComplexityNat_eq (P : Presentation X) (T : X → X) (hT : Continuous T)
    (A : Set ℕ) (x : X) {n : ℕ} (hn : 1 ≤ n) {r : ℝ} (hr : 0 < r) :
    ∃ j, P.ι j ∈ bowenBall T n x r ∧ orbitComplexityNat P T A x n r = oracleNatComplexity A j := by
  obtain ⟨j, hj, heq⟩ := entropiesAndOrbitComplexities_attained P T hT A x n hn r hr
  exact ⟨j, hj, by rw [orbitComplexityNat, heq, ENat.toNat_natCast]⟩

/-- The orbit complexity `K_n^A(x, T, r)` does not increase with the radius. -/
theorem orbitComplexityNat_le_of_radius_le (P : Presentation X) (T : X → X)
    (hT : Continuous T) (A : Set ℕ) (x : X) {n : ℕ} (hn : 1 ≤ n) {r r' : ℝ} (hr : 0 < r)
    (h : r ≤ r') : orbitComplexityNat P T A x n r' ≤ orbitComplexityNat P T A x n r := by
  obtain ⟨j, hj, heq⟩ := exists_orbitComplexityNat_eq P T hT A x hn hr
  rw [heq]
  exact orbitComplexityNat_le_of_mem P T A (bowenBall_subset_of_le T n x h hj)

/-- The base-two logarithm of the inverse of a positive finite constant has the same
absolute value. -/
theorem abs_logb_inv_toReal (c : ℝ≥0∞) :
    |Real.logb 2 c⁻¹.toReal| = |Real.logb 2 c.toReal| := by
  rw [ENNReal.toReal_inv, Real.logb_inv, abs_neg]

/-- Threshold comparison in `EReal`: if for all reals `s < z`, eventually `a n < s` implies
`b n ≤ z`, then `liminf b ≤ liminf a` and `limsup b ≤ limsup a`. -/
theorem liminf_limsup_le_of_forall_lt_coe {a b : ℕ → EReal}
    (h : ∀ s z : ℝ, s < z → ∀ᶠ n in atTop, a n < s → b n ≤ z) :
    liminf b atTop ≤ liminf a atTop ∧ limsup b atTop ≤ limsup a atTop := by
  constructor
  · refine EReal.le_of_forall_lt_iff_le.1 fun z hz ↦ ?_
    obtain ⟨s, hs1, hs2⟩ := EReal.lt_iff_exists_real_btwn.1 hz
    have hfr := frequently_lt_of_liminf_lt (by isBoundedDefault) hs1
    exact liminf_le_of_frequently_le' ((hfr.and_eventually
      (h s z (by exact_mod_cast hs2))).mono fun n hn ↦ hn.2 hn.1)
  · refine EReal.le_of_forall_lt_iff_le.1 fun z hz ↦ ?_
    obtain ⟨s, hs1, hs2⟩ := EReal.lt_iff_exists_real_btwn.1 hz
    refine limsup_le_of_le (by isBoundedDefault) ?_
    filter_upwards [eventually_lt_of_limsup_lt hs1 (by isBoundedDefault),
      h s z (by exact_mod_cast hs2)] with n h1 h2 using h2 h1

/-- Threshold comparison in `ℝ≥0∞`: if for every real `s > 0` there is an error `d → 0` such
that eventually `a n < s` implies `b n ≤ s + d n`, then `liminf b ≤ liminf a` and
`limsup b ≤ limsup a`. -/
theorem liminf_limsup_le_of_forall_lt_ofReal {a b : ℕ → ℝ≥0∞}
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
theorem tendsto_logb_natCast_div_nat :
    Tendsto (fun n : ℕ ↦ Real.logb 2 n / n) atTop (𝓝 0) := by
  have h := (Real.tendsto_pow_logb_div_mul_add_atTop (b := 2) 1 0 1 one_ne_zero).comp
    tendsto_natCast_atTop_atTop
  simpa [Function.comp_def] using h

/-- `log₂ t / t → 0` as `t → ∞`. -/
theorem tendsto_logb_div_self_atTop :
    Tendsto (fun t : ℝ ↦ Real.logb 2 t / t) atTop (𝓝 0) := by
  simpa using Real.tendsto_pow_logb_div_mul_add_atTop (b := 2) 1 0 1 one_ne_zero

/-- An error term `(C + D log₂ n) / n` tends to zero. -/
theorem tendsto_add_mul_logb_div_nat (C D : ℝ) :
    Tendsto (fun n : ℕ ↦ (C + D * Real.logb 2 n) / n) atTop (𝓝 0) := by
  have h1 := tendsto_const_div_atTop_nhds_zero_nat C
  have h2 := tendsto_logb_natCast_div_nat.const_mul D
  rw [mul_zero] at h2
  simpa [add_div, mul_div_assoc] using h1.add h2

omit [MetricSpace X] in
/-- At a point of positive lower Birkhoff average, a nonnegative error that is `o(n)` is also
`o(S_n u(x))`. -/
theorem tendsto_div_birkhoffSum_of_tendsto_div {T : X → X} {u : X → ℝ} {x : X}
    (hx : 0 < lowerBirkhoffAverage T u x) {f : ℕ → ℝ} (hf0 : ∀ᶠ n in atTop, 0 ≤ f n)
    (hf : Tendsto (fun n : ℕ ↦ f n / n) atTop (𝓝 0)) :
    Tendsto (fun n ↦ f n / birkhoffSum T u n x) atTop (𝓝 0) := by
  obtain ⟨δ, hδ, hev⟩ := exists_pos_eventually_mul_le_birkhoffSum hx
  have hup : Tendsto (fun n : ℕ ↦ δ⁻¹ * (f n / n)) atTop (𝓝 0) := by
    simpa using hf.const_mul δ⁻¹
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup ?_ ?_
  · filter_upwards [hf0, hev, eventually_ge_atTop 1] with n h0 hn hn1
    have : 0 < δ * n := mul_pos hδ (by exact_mod_cast hn1)
    exact div_nonneg h0 (this.le.trans hn)
  · filter_upwards [hf0, hev, eventually_ge_atTop 1] with n h0 hn hn1
    have : 0 < δ * n := mul_pos hδ (by exact_mod_cast hn1)
    calc f n / birkhoffSum T u n x ≤ f n / (δ * n) := div_le_div_of_nonneg_left h0 this hn
      _ = δ⁻¹ * (f n / n) := by field_simp

omit [MetricSpace X] in
/-- At a point of positive lower Birkhoff average,
`(C + 2 log₂ n + 2 log₂ S_n u(x)) / S_n u(x) → 0`. -/
theorem tendsto_logb_err_div_birkhoffSum {T : X → X} {u : X → ℝ} {x : X}
    (hx : 0 < lowerBirkhoffAverage T u x) (C : ℝ) :
    Tendsto (fun n : ℕ ↦ (C + 2 * Real.logb 2 n + 2 * Real.logb 2 (birkhoffSum T u n x)) /
      birkhoffSum T u n x) atTop (𝓝 0) := by
  have hS := tendsto_birkhoffSum_atTop hx
  have h1 : Tendsto (fun n ↦ C / birkhoffSum T u n x) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hS
  have h2 : Tendsto (fun n : ℕ ↦ Real.logb 2 n / birkhoffSum T u n x) atTop (𝓝 0) :=
    tendsto_div_birkhoffSum_of_tendsto_div hx ((eventually_ge_atTop 1).mono fun n hn ↦
      Real.logb_nonneg one_lt_two (by exact_mod_cast hn)) tendsto_logb_natCast_div_nat
  have h3 := tendsto_logb_div_self_atTop.comp hS
  have h := h1.add ((h2.const_mul 2).add (h3.const_mul 2))
  simp only [mul_zero, add_zero] at h
  refine h.congr fun n ↦ ?_
  simp only [Function.comp_apply]
  ring

/-- A mass of at least `2^{-t}` has `-log₂` of its real value at most `t`. -/
theorem neg_logb_toReal_le_of_rpow_le {q : ℝ≥0∞} (hq : q ≠ ⊤) {t : ℝ}
    (h : ENNReal.ofReal ((2 : ℝ) ^ (-t)) ≤ q) : -Real.logb 2 q.toReal ≤ t := by
  have h2pos : 0 < (2 : ℝ) ^ (-t) := Real.rpow_pos_of_pos two_pos _
  have h' : (2 : ℝ) ^ (-t) ≤ q.toReal := (ENNReal.ofReal_le_iff_le_toReal hq).1 h
  have := (Real.le_logb_iff_rpow_le one_lt_two (h2pos.trans_le h')).2 h'
  linarith

/-- `2^{-(j + 2 log₂ n)} = 2^{-j} / n²` for `n ≥ 1`. -/
theorem ofReal_two_rpow_neg_add_logb_eq (j : ℕ) {n : ℕ} (hn : 1 ≤ n) :
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

/-- `2^{-K}` as an extended real. -/
theorem ofReal_two_rpow_neg_natCast_eq (K : ℕ) :
    ENNReal.ofReal ((2 : ℝ) ^ (-(K : ℝ))) = (2 : ℝ≥0∞)⁻¹ ^ K := by
  rw [Real.rpow_neg zero_le_two, Real.rpow_natCast, ENNReal.ofReal_inv_of_pos (by positivity),
    ENNReal.ofReal_pow zero_le_two, ENNReal.ofReal_ofNat, ENNReal.inv_pow]

end Kolmogorov.PointToSet
