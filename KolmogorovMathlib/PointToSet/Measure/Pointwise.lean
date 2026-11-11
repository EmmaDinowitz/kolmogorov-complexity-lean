/-
Copyright (c) 2026 Emma Dinowitz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emma Dinowitz
-/
import KolmogorovMathlib.PointToSet.Measure.CodingByMeasure
import KolmogorovMathlib.PointToSet.Measure.DeficiencyTest
import KolmogorovMathlib.PointToSet.Pressure.Lower.EntropyPointToSet

/-!
# Orbit complexity of random points (Theorem 3.3 and Corollary 3.6)

Let `A` be admissible for `(X, d, T, μ)`. Then the orbit complexities are at most the local
entropies of `μ` at every point, and they are equal at every point that is `μ`-random relative
to `A` (E. Dinowitz, *Entropy of non-invariant measures and orbit complexity of random
points*, Theorem 3.3). No invariance, ergodicity or compactness is used.

* `orbitComplexityAt_le_localEntropyAt` (Theorem 3.3(i)): `K̲^A(x, T, 6ε) ≤ h̲_μ(T, x, ε)` and
  the same for the upper quantities, at every point.
* `localEntropyAt_le_orbitComplexityAt` (Theorem 3.3(ii)): `h̲_μ(T, x, 2ε) ≤ K̲^A(x, T, ε)` and
  the same for the upper quantities, at every random point.
* `orbitComplexities_le_localEntropy`, `orbitComplexities_eq_localEntropy`: the consequences
  in the limit `ε → 0`.
* `lowerEntropy_le_of_localEntropy_le`, `upperEntropy_le_of_localEntropy_le`,
  `le_lowerEntropy_of_le_localEntropy`, `le_upperEntropy_of_le_localEntropy`
  (Corollary 3.6): Billingsley-type bounds for the Bowen and packing entropies of an arbitrary
  set.

Blueprint nodes `meas:pointwise`, `meas:billingsley`.
-/

namespace Kolmogorov.PointToSet

open Filter Set MeasureTheory
open scoped Topology ENNReal Computability

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

/-! ### Comparison lemmas for limits inferior and superior -/

/-- If `a n ≤ b n + d n` eventually with `d n → 0`, then `liminf a ≤ liminf b` and
`limsup a ≤ limsup b`. -/
private theorem liminf_limsup_le_of_le_add {a b d : ℕ → ℝ≥0∞} (hd : Tendsto d atTop (𝓝 0))
    (h : ∀ᶠ n in atTop, a n ≤ b n + d n) :
    liminf a atTop ≤ liminf b atTop ∧ limsup a atTop ≤ limsup b atTop := by
  constructor
  · calc liminf a atTop ≤ liminf (b + d) atTop := liminf_le_liminf h
      _ = liminf b atTop := ENNReal.liminf_add_of_right_tendsto_zero hd b
  · calc limsup a atTop ≤ limsup (b + d) atTop := limsup_le_limsup h
      _ = limsup b atTop := ENNReal.limsup_add_of_right_tendsto_zero hd b

/-- Threshold comparison: if for every real `s > 0` there is an error `d → 0` such that
eventually `a n < s` implies `b n ≤ s + d n`, then `liminf b ≤ liminf a` and
`limsup b ≤ limsup a`. -/
private theorem liminf_limsup_le_of_forall_lt {a b : ℕ → ℝ≥0∞}
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

/-! ### Theorem 3.3 -/

/-- Theorem 3.3(i), the coding direction, at a fixed scale and at every point:
`K̲^A(x, T, 6ε) ≤ h̲_μ(T, x, ε)` and `K̄^A(x, T, 6ε) ≤ h̄_μ(T, x, ε)`.
Blueprint node `meas:pointwise`. -/
theorem orbitComplexityAt_le_localEntropyAt (P : Presentation X) (T : X → X)
    (hT : Continuous T) (A : Set ℕ) (μ : Measure X) [IsFiniteMeasure μ] (hμ : μ univ ≤ 1)
    (hA : IsMeasureAdmissible P T μ A) (ε : ℚ) (hε : 0 < ε) (x : X) :
    (orbitComplexityAt P T A x (6 * (ε : ℝ))).1 ≤ (localEntropyAt μ T x (ε : ℝ)).1 ∧
      (orbitComplexityAt P T A x (6 * (ε : ℝ))).2 ≤ (localEntropyAt μ T x (ε : ℝ)).2 := by
  obtain ⟨c, hc⟩ := coding_by_measure P T hT A μ hμ hA ε hε
  have hε' : (0 : ℝ) < ε := by exact_mod_cast hε
  refine liminf_limsup_le_of_forall_lt fun s hs ↦ ?_
  refine ⟨fun n ↦ ENNReal.ofReal ((1 + c + 2 * Real.logb 2 (s + 2) + 4 * Real.logb 2 n) / n),
    tendsto_ofReal_err _ _, ?_⟩
  filter_upwards [eventually_ge_atTop 1] with n hn hlt
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
  rw [entropiesAndOrbitComplexities_rate P T hT A x n hn _ (by positivity),
    natCast_div_natCast_eq_ofReal _ hn]
  calc ENNReal.ofReal ((orbitComplexityNat P T A x n (6 * ε) : ℝ) / n)
      ≤ ENNReal.ofReal (s + (1 + c + 2 * Real.logb 2 (s + 2) + 4 * Real.logb 2 n) / n) := by
        refine ENNReal.ofReal_le_ofReal ?_
        rw [div_le_iff₀ hn0, add_mul, div_mul_cancel₀ _ hn0.ne']
        linarith
    _ ≤ _ := ENNReal.ofReal_add_le

/-- Theorem 3.3(ii), the incompressibility direction, at a fixed scale and at every random
point: `h̲_μ(T, x, 2ε) ≤ K̲^A(x, T, ε)` and `h̄_μ(T, x, 2ε) ≤ K̄^A(x, T, ε)`.
Blueprint node `meas:pointwise`. -/
theorem localEntropyAt_le_orbitComplexityAt (P : Presentation X) (T : X → X)
    (hT : Continuous T) (A : Set ℕ) (μ : Measure X) [IsProbabilityMeasure μ]
    (hA : IsMeasureAdmissible P T μ A) (ε : ℚ) (hε : 0 < ε) {x : X}
    (hx : x ∈ randomPoints P A μ) :
    (localEntropyAt μ T x (2 * (ε : ℝ))).1 ≤ (orbitComplexityAt P T A x (ε : ℝ)).1 ∧
      (localEntropyAt μ T x (2 * (ε : ℝ))).2 ≤ (orbitComplexityAt P T A x (ε : ℝ)).2 := by
  obtain ⟨m, hm⟩ := exists_measure_bowenBall_ge_of_mem_randomPoints P T hT A μ hA ε hε hx
  have hε' : (0 : ℝ) < ε := by exact_mod_cast hε
  refine liminf_limsup_le_of_le_add (tendsto_ofReal_err (m : ℝ) 2) ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  set K := orbitComplexityNat P T A x n ε with hK
  have hL : 0 ≤ Real.logb 2 n :=
    Real.logb_nonneg one_lt_two (by exact_mod_cast hn)
  have hinfo : infoBits (μ (bowenBall T n x (2 * ε))) ≤
      ENNReal.ofReal (((K + m : ℕ) : ℝ) + 2 * Real.logb 2 n) := by
    refine infoBits_le_of_rpow_le (by positivity) ?_
    rw [ofReal_two_rpow_neg_eq _ hn]
    exact hm n hn
  rw [localEntropyRate, entropiesAndOrbitComplexities_rate P T hT A x n hn _ hε',
    natCast_div_natCast_eq_ofReal _ hn]
  calc infoBits (μ (bowenBall T n x (2 * ε))) / n
      ≤ ENNReal.ofReal (((K + m : ℕ) : ℝ) + 2 * Real.logb 2 n) / n := by gcongr
    _ = ENNReal.ofReal ((K : ℝ) / n + (m + 2 * Real.logb 2 n) / n) := by
        rw [← ENNReal.ofReal_natCast n, ← ENNReal.ofReal_div_of_pos hn0]
        congr 1
        push_cast
        ring
    _ ≤ _ := ENNReal.ofReal_add_le

/-- Theorem 3.3: at every point the orbit complexities are at most the local entropies,
`K̲^A(x, T) ≤ h̲_μ(T, x)` and `K̄^A(x, T) ≤ h̄_μ(T, x)`. Blueprint node `meas:pointwise`. -/
theorem orbitComplexities_le_localEntropy (P : Presentation X) (T : X → X)
    (hT : Continuous T) (A : Set ℕ) (μ : Measure X) [IsFiniteMeasure μ] (hμ : μ univ ≤ 1)
    (hA : IsMeasureAdmissible P T μ A) (x : X) :
    (orbitComplexities P T A x).1 ≤ (localEntropy μ T x).1 ∧
      (orbitComplexities P T A x).2 ≤ (localEntropy μ T x).2 := by
  have key : ∀ p : ℕ, (orbitComplexityAt P T A x (dyadicRadius p)).1 ≤ (localEntropy μ T x).1 ∧
      (orbitComplexityAt P T A x (dyadicRadius p)).2 ≤ (localEntropy μ T x).2 := by
    intro p
    set ε : ℚ := (2 : ℚ)⁻¹ ^ (p + 3) with hεdef
    have hε : 0 < ε := by positivity
    have h6 : 6 * (ε : ℝ) ≤ dyadicRadius p := by
      have h0 : (0 : ℝ) ≤ (2 : ℝ)⁻¹ ^ p := by positivity
      rw [hεdef, dyadicRadius]
      push_cast
      rw [pow_add]
      norm_num
      linarith
    have h1 := orbitComplexityAt_antitone P T A x h6
    have h2 := orbitComplexityAt_le_localEntropyAt P T hT A μ hμ hA ε hε x
    have h3 := localEntropyAt_le_localEntropy μ T x (ε := (ε : ℝ)) (by exact_mod_cast hε)
    exact ⟨h1.1.trans (h2.1.trans h3.1), h1.2.trans (h2.2.trans h3.2)⟩
  rw [orbitComplexities_eq_iSup_orbitComplexityAt]
  exact ⟨iSup_le fun p ↦ (key p).1, iSup_le fun p ↦ (key p).2⟩

/-- Theorem 3.3: at every point that is `μ`-random relative to an admissible oracle `A`, the
lower and upper orbit complexities equal the lower and upper local entropies of `μ`,
`K̲^A(x, T) = h̲_μ(T, x)` and `K̄^A(x, T) = h̄_μ(T, x)`. Blueprint node `meas:pointwise`. -/
theorem orbitComplexities_eq_localEntropy (P : Presentation X) (T : X → X)
    (hT : Continuous T) (A : Set ℕ) (μ : Measure X) [IsProbabilityMeasure μ]
    (hA : IsMeasureAdmissible P T μ A) {x : X} (hx : x ∈ randomPoints P A μ) :
    orbitComplexities P T A x = localEntropy μ T x := by
  have hle := orbitComplexities_le_localEntropy P T hT A μ prob_le_one hA x
  have hge : ∀ p : ℕ,
      (localEntropyAt μ T x (dyadicRadius p)).1 ≤ (orbitComplexities P T A x).1 ∧
      (localEntropyAt μ T x (dyadicRadius p)).2 ≤ (orbitComplexities P T A x).2 := by
    intro p
    set ε : ℚ := (2 : ℚ)⁻¹ ^ (p + 1) with hεdef
    have hε : 0 < ε := by positivity
    have heq : dyadicRadius p = 2 * (ε : ℝ) := by
      rw [hεdef, dyadicRadius]
      push_cast
      rw [pow_succ]
      ring
    rw [heq]
    have h1 := localEntropyAt_le_orbitComplexityAt P T hT A μ hA ε hε hx
    have h2 := orbitComplexityAt_le_orbitComplexities P T A x (ε := (ε : ℝ))
      (by exact_mod_cast hε)
    exact ⟨h1.1.trans h2.1, h1.2.trans h2.2⟩
  exact Prod.ext (le_antisymm hle.1 (iSup_le fun p ↦ (hge p).1))
    (le_antisymm hle.2 (iSup_le fun p ↦ (hge p).2))

/-- Almost everywhere form of Theorem 3.3: the orbit complexities relative to an admissible
oracle equal the local entropies `μ`-almost everywhere. Blueprint node `meas:pointwise`. -/
theorem ae_orbitComplexities_eq_localEntropy (P : Presentation X) (T : X → X)
    (hT : Continuous T) (A : Set ℕ) (μ : Measure X) [IsProbabilityMeasure μ]
    (hA : IsMeasureAdmissible P T μ A) :
    ∀ᵐ x ∂μ, orbitComplexities P T A x = localEntropy μ T x :=
  (ae_mem_randomPoints P A μ).mono fun _ hx ↦
    orbitComplexities_eq_localEntropy P T hT A μ hA hx

/-! ### Billingsley-type bounds (Corollary 3.6) -/

/-- Corollary 3.6(a), lower entropy: if `h̲_μ(T, x) ≤ s` for all `x ∈ Z`, then the Bowen
entropy of `Z` is at most `s`. Blueprint node `meas:billingsley`. -/
theorem lowerEntropy_le_of_localEntropy_le (P : Presentation X) (T : X → X)
    (hT : Continuous T) (μ : Measure X) [IsProbabilityMeasure μ] (Z : Set X) (s : ℝ≥0∞)
    (h : ∀ x ∈ Z, (localEntropy μ T x).1 ≤ s) : lowerEntropy T Z ≤ s := by
  obtain ⟨C, hC⟩ := exists_measureAdmissible_base P T hT μ
  have hA := hC C (TuringReducible.refl _)
  rw [entropy_effectiveCharacterization_allOracles_pointToSet P T hT Z]
  refine iInf_le_of_le C (iSup₂_le fun x hx ↦ ?_)
  exact (orbitComplexities_le_localEntropy P T hT C μ prob_le_one hA x).1.trans (h x hx)

/-- Corollary 3.6(a), upper entropy: if `h̄_μ(T, x) ≤ s` for all `x ∈ Z`, then the packing
entropy of `Z` is at most `s`. Blueprint node `meas:billingsley`. -/
theorem upperEntropy_le_of_localEntropy_le (P : Presentation X) (T : X → X)
    (hT : Continuous T) (μ : Measure X) [IsProbabilityMeasure μ] (Z : Set X) (s : ℝ≥0∞)
    (h : ∀ x ∈ Z, (localEntropy μ T x).2 ≤ s) : upperEntropy P T Z ≤ s := by
  obtain ⟨C, hC⟩ := exists_measureAdmissible_base P T hT μ
  have hA := hC C (TuringReducible.refl _)
  rw [upperEntropy_pointToSet P T hT Z]
  refine iInf_le_of_le C (iSup₂_le fun x hx ↦ ?_)
  exact (orbitComplexities_le_localEntropy P T hT C μ prob_le_one hA x).2.trans (h x hx)

/-- Corollary 3.6(b), lower entropy: if `Z` has positive outer `μ`-measure and
`h̲_μ(T, x) ≥ s` for all `x ∈ Z`, then the Bowen entropy of `Z` is at least `s`.
Blueprint node `meas:billingsley`. -/
theorem le_lowerEntropy_of_le_localEntropy (P : Presentation X) (T : X → X)
    (hT : Continuous T) (μ : Measure X) [IsProbabilityMeasure μ] {Z : Set X} (hZ : μ Z ≠ 0)
    (s : ℝ≥0∞) (h : ∀ x ∈ Z, s ≤ (localEntropy μ T x).1) : s ≤ lowerEntropy T Z := by
  obtain ⟨B, hB⟩ := entropy_effectiveCharacterization_allOracles_cone P T hT Z
  obtain ⟨C, hC⟩ := exists_measureAdmissible_base P T hT μ
  have hA := hC (oracleJoin B C) (oracle_joins_right B C)
  obtain ⟨x, hxZ, hx⟩ := exists_mem_randomPoints_of_measure_pos P (oracleJoin B C) μ hZ
  rw [hB _ (oracle_joins B C)]
  calc s ≤ (localEntropy μ T x).1 := h x hxZ
    _ = (orbitComplexities P T (oracleJoin B C) x).1 := by
        rw [orbitComplexities_eq_localEntropy P T hT _ μ hA hx]
    _ ≤ ⨆ y ∈ Z, (orbitComplexities P T (oracleJoin B C) y).1 :=
        le_iSup₂ (f := fun y _ ↦ (orbitComplexities P T (oracleJoin B C) y).1) x hxZ

/-- Corollary 3.6(b), upper entropy: if `Z` has positive outer `μ`-measure and
`h̄_μ(T, x) ≥ s` for all `x ∈ Z`, then the packing entropy of `Z` is at least `s`.
Blueprint node `meas:billingsley`. -/
theorem le_upperEntropy_of_le_localEntropy (P : Presentation X) (T : X → X)
    (hT : Continuous T) (μ : Measure X) [IsProbabilityMeasure μ] {Z : Set X} (hZ : μ Z ≠ 0)
    (s : ℝ≥0∞) (h : ∀ x ∈ Z, s ≤ (localEntropy μ T x).2) : s ≤ upperEntropy P T Z := by
  obtain ⟨B, hB⟩ := upperEntropy_pointToSet_cone P T hT Z
  obtain ⟨C, hC⟩ := exists_measureAdmissible_base P T hT μ
  have hA := hC (oracleJoin B C) (oracle_joins_right B C)
  obtain ⟨x, hxZ, hx⟩ := exists_mem_randomPoints_of_measure_pos P (oracleJoin B C) μ hZ
  rw [hB _ (oracle_joins B C)]
  calc s ≤ (localEntropy μ T x).2 := h x hxZ
    _ = (orbitComplexities P T (oracleJoin B C) x).2 := by
        rw [orbitComplexities_eq_localEntropy P T hT _ μ hA hx]
    _ ≤ ⨆ y ∈ Z, (orbitComplexities P T (oracleJoin B C) y).2 :=
        le_iSup₂ (f := fun y _ ↦ (orbitComplexities P T (oracleJoin B C) y).2) x hxZ

end Kolmogorov.PointToSet
