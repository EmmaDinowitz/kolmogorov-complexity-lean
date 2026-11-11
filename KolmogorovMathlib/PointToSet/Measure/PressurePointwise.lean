/-
Copyright (c) 2026 Emma Dinowitz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emma Dinowitz
-/
import KolmogorovMathlib.PointToSet.Measure.LocalPressure
import KolmogorovMathlib.PointToSet.Measure.LocalPressureAux

/-!
# Pointwise pressure and BS dimension of random points (Theorem 8.3, Corollary 8.4)

Lemmas 3.1 and 3.2 are statements about `K_n^A` alone, so the pointwise theorem extends to the
pointwise pressure and BS dimension of the point-to-set chapter (E. Dinowitz, *Entropy of
non-invariant measures and orbit complexity of random points*, §8). The potentials `φ` and `u`
are uniformly continuous.

* `pointwisePressure_le_localPressure`, `pointwiseBSDimension_le_localBSDimension`
  (Theorem 8.3(i)): the inequalities at every point with `inf_n S_n φ(x) / n > -∞`,
  respectively with positive lower Birkhoff average of `u`.
* `pointwisePressure_eq_localPressure`, `pointwiseBSDimension_eq_localBSDimension`
  (Theorem 8.3(ii)): equality at random points.
* `pointwisePressure_eq_localPressure_universalMeasure`,
  `pointwiseBSDimension_eq_localBSDimension_universalMeasure` (Theorem 8.3(iii)): with the
  universal measure in place of `μ`, equality at every point.
* Corollary 8.4: Billingsley-type bounds (`lowerPressure_le_of_localPressure_le`, …) and dual
  principles (`lowerPressure_eq_iInf_measure`, `lowerBSDimension_eq_iInf_measure`, …) for the
  pressure and the BS dimension of arbitrary sets.

Blueprint nodes `meas:pressure-pointwise`, `meas:pressure-billingsley`, `meas:pressure-dual`.
-/

namespace Kolmogorov.PointToSet

open Filter Set MeasureTheory
open scoped Topology ENNReal Computability

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

/-- The hypothesis `inf_n S_n φ(x) / n > -∞` of Theorem 8.3(i). -/
def BirkhoffBoundedBelow (T : X → X) (φ : X → ℝ) (x : X) : Prop :=
  ∃ L : ℝ, ∀ n : ℕ, 1 ≤ n → L ≤ birkhoffSum T φ n x / n

/-! ### Comparison at a fixed scale -/

omit [MeasurableSpace X] [BorelSpace X] in
/-- At a fixed time, an oscillation-free bound on the orbit pressure rate: shrinking the radius
increases the rate of `K_n^A(x, T, ε) + S_n φ(x)`. -/
private theorem orbitPressureRate_le_of_le_radius (P : Presentation X) (T : X → X)
    (hT : Continuous T) (φ : X → ℝ) (A : Set ℕ) (x : X) {n : ℕ} (hn : 1 ≤ n) {r r' : ℝ}
    (hr : 0 < r) (h : r ≤ r') :
    orbitPressureRate P T φ A x n r' ≤ orbitPressureRate P T φ A x n r := by
  have hK : (orbitComplexityNat P T A x n r' : ℝ) ≤ orbitComplexityNat P T A x n r := by
    exact_mod_cast orbitComplexityNat_le_of_radius_le P T hT A x hn hr h
  exact EReal.coe_le_coe_iff.2 (div_le_div_of_nonneg_right (by linarith) (Nat.cast_nonneg n))

omit [MeasurableSpace X] [BorelSpace X] in
/-- Shrinking the radius increases the orbit BS rate. -/
private theorem orbitBSRate_le_of_le_radius (P : Presentation X) (T : X → X)
    (hT : Continuous T) (u : X → ℝ) (A : Set ℕ) (x : X) {n : ℕ} (hn : 1 ≤ n) {r r' : ℝ}
    (hr : 0 < r) (h : r ≤ r') : orbitBSRate P T u A x n r' ≤ orbitBSRate P T u A x n r :=
  ENNReal.div_le_div_right
    (Nat.cast_le.2 (orbitComplexityNat_le_of_radius_le P T hT A x hn hr h)) _

/-- `6 · 2^{-(p + 3)} ≤ 2^{-p}`. -/
private theorem six_mul_dyadicRadius_add_three_le (p : ℕ) :
    6 * dyadicRadius (p + 3) ≤ dyadicRadius p := by
  have h0 : (0 : ℝ) ≤ (2 : ℝ)⁻¹ ^ p := by positivity
  rw [dyadicRadius, dyadicRadius, pow_add]
  norm_num
  linarith

/-- The dyadic radius `2^{-p}` as the cast of a positive rational. -/
private theorem dyadicRadius_eq_ratCast (p : ℕ) :
    dyadicRadius p = (((2 : ℚ)⁻¹ ^ p : ℚ) : ℝ) := by
  simp [dyadicRadius]

/-- Theorem 8.3(i) at a fixed scale, pressure: the lower and upper rates of
`K_n^A(x, T, 6ε) + S_n φ(x)` are at most the local pressures at the scale `ε`. -/
theorem orbitPressureRate_le_localPressureAt (P : Presentation X) (T : X → X)
    (hT : Continuous T) (φ : X → ℝ) (A : Set ℕ) (μ : Measure X) [IsFiniteMeasure μ]
    (hμ : μ univ ≤ 1) (hA : IsMeasureAdmissible P T μ A) (ε : ℚ) (hε : 0 < ε) {x : X}
    (hx : BirkhoffBoundedBelow T φ x) :
    liminf (fun n ↦ orbitPressureRate P T φ A x n (6 * (ε : ℝ))) atTop ≤
        (localPressureAt μ T φ x (ε : ℝ)).1 ∧
      limsup (fun n ↦ orbitPressureRate P T φ A x n (6 * (ε : ℝ))) atTop ≤
        (localPressureAt μ T φ x (ε : ℝ)).2 := by
  obtain ⟨c, hc⟩ := coding_by_measure P T hT A μ hμ hA ε hε
  obtain ⟨L, hL⟩ := hx
  refine liminf_limsup_le_of_forall_lt_coe fun s z hsz ↦ ?_
  set C : ℝ := 1 + c + 2 * Real.logb 2 (|s - L| + 2) with hC
  have herr := tendsto_add_mul_logb_div_nat C 4
  filter_upwards [eventually_ge_atTop 1, herr.eventually (gt_mem_nhds (sub_pos.2 hsz))]
    with n hn herrn hlt
  set q := μ (bowenBall T n x (ε : ℝ)) with hq
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  rw [localPressureRate, ← hq] at hlt
  split_ifs at hlt with h0
  · exact absurd hlt (not_lt.2 le_top)
  rw [EReal.coe_lt_coe_iff] at hlt
  have hq1 : q ≤ 1 := (measure_mono (subset_univ _)).trans hμ
  have hqt : q ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hq1
  set I := -Real.logb 2 q.toReal with hI
  have hI0 : 0 ≤ I := neg_nonneg.2 (Real.logb_nonpos one_lt_two ENNReal.toReal_nonneg
    (by simpa using ENNReal.toReal_mono ENNReal.one_ne_top hq1))
  have hS : L * n ≤ birkhoffSum T φ n x := (le_div_iff₀ hn0).1 (hL n hn)
  have hIlt : I < (s - L) * n := by
    rw [div_lt_iff₀ hn0] at hlt
    nlinarith
  set k := ⌊I⌋₊ + 1 with hk
  have hIk : I < k := by
    push_cast [hk]
    exact Nat.lt_floor_add_one _
  have hqk : (2 : ℝ≥0∞)⁻¹ ^ k < q := by
    refine two_inv_pow_lt_of_infoBits_lt ?_
    rw [infoBits_of_ne h0, ← hI, ← ENNReal.ofReal_natCast]
    exact (ENNReal.ofReal_lt_ofReal_iff (by positivity)).2 hIk
  have hK := hc x n k hn hqk
  have hkr : (k : ℝ) ≤ I + 1 := by
    have := Nat.floor_le hI0
    push_cast [hk]
    linarith
  have hk1 : (k : ℝ) + 1 ≤ (|s - L| + 2) * n := by
    have h1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    nlinarith [le_abs_self (s - L)]
  have hlog : Real.logb 2 ((k : ℝ) + 1) ≤ Real.logb 2 (|s - L| + 2) + Real.logb 2 n := by
    rw [← Real.logb_mul (by positivity) hn0.ne']
    exact Real.logb_le_logb_of_le one_lt_two (by positivity) hk1
  have hKr : (orbitComplexityNat P T A x n (6 * (ε : ℝ)) : ℝ) ≤ I + (C + 4 * Real.logb 2 n) := by
    rw [hC]
    linarith
  rw [orbitPressureRate, EReal.coe_le_coe_iff]
  have he : (orbitComplexityNat P T A x n (6 * (ε : ℝ)) + birkhoffSum T φ n x) / n ≤
      (I + birkhoffSum T φ n x) / n + (C + 4 * Real.logb 2 n) / n := by
    rw [← add_div]
    exact div_le_div_of_nonneg_right (by linarith) hn0.le
  linarith

/-- Theorem 8.3(i) at a fixed scale, BS dimension: the lower and upper rates of
`K_n^A(x, T, 6ε) / S_n u(x)` are at most the local BS dimensions at the scale `ε`. -/
theorem orbitBSRate_le_localBSDimensionAt (P : Presentation X) (T : X → X)
    (hT : Continuous T) (u : X → ℝ) (A : Set ℕ) (μ : Measure X) [IsFiniteMeasure μ]
    (hμ : μ univ ≤ 1) (hA : IsMeasureAdmissible P T μ A) (ε : ℚ) (hε : 0 < ε) {x : X}
    (hx : 0 < lowerBirkhoffAverage T u x) :
    liminf (fun n ↦ orbitBSRate P T u A x n (6 * (ε : ℝ))) atTop ≤
        (localBSDimensionAt μ T u x (ε : ℝ)).1 ∧
      limsup (fun n ↦ orbitBSRate P T u A x n (6 * (ε : ℝ))) atTop ≤
        (localBSDimensionAt μ T u x (ε : ℝ)).2 := by
  obtain ⟨c, hc⟩ := coding_by_measure P T hT A μ hμ hA ε hε
  refine liminf_limsup_le_of_forall_lt_ofReal fun s hs ↦ ?_
  set C : ℝ := 1 + c + 2 * Real.logb 2 (s + 2) with hC
  refine ⟨fun n ↦ ENNReal.ofReal ((C + 2 * Real.logb 2 n +
    2 * Real.logb 2 (birkhoffSum T u n x)) / birkhoffSum T u n x),
    by simpa using ENNReal.tendsto_ofReal (tendsto_logb_err_div_birkhoffSum hx C), ?_⟩
  filter_upwards [eventually_ge_atTop 1, (tendsto_birkhoffSum_atTop hx).eventually_ge_atTop 1]
    with n hn hS1 hlt
  set S := birkhoffSum T u n x with hSdef
  set I := infoBits (μ (bowenBall T n x (ε : ℝ))) with hI
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hSpos : 0 < S := zero_lt_one.trans_le hS1
  have hSE : ENNReal.ofReal S ≠ 0 := (ENNReal.ofReal_pos.2 hSpos).ne'
  have hlt' : I < ENNReal.ofReal (s * S) := by
    rw [localBSRate, ← hSdef, ← hI, ENNReal.div_lt_iff (Or.inl hSE) (Or.inl ENNReal.ofReal_ne_top)]
      at hlt
    rwa [ENNReal.ofReal_mul hs.le]
  have hItop : I ≠ ⊤ := (hlt'.trans ENNReal.ofReal_lt_top).ne
  have hIr : I.toReal < s * S := (ENNReal.lt_ofReal_iff_toReal_lt hItop).1 hlt'
  set k := ⌊I.toReal⌋₊ + 1 with hk
  have hIk : I < k := by
    rw [← ENNReal.ofReal_toReal hItop, ← ENNReal.ofReal_natCast]
    refine (ENNReal.ofReal_lt_ofReal_iff (by positivity)).2 ?_
    push_cast [hk]
    exact Nat.lt_floor_add_one _
  have hK := hc x n k hn (two_inv_pow_lt_of_infoBits_lt hIk)
  have hkr : (k : ℝ) ≤ s * S + 1 := by
    have := Nat.floor_le (ENNReal.toReal_nonneg (a := I))
    push_cast [hk]
    linarith
  have hk1 : (k : ℝ) + 1 ≤ (s + 2) * S := by nlinarith
  have hlog : Real.logb 2 ((k : ℝ) + 1) ≤ Real.logb 2 (s + 2) + Real.logb 2 S := by
    rw [← Real.logb_mul (by positivity) hSpos.ne']
    exact Real.logb_le_logb_of_le one_lt_two (by positivity) hk1
  have hKr : (orbitComplexityNat P T A x n (6 * (ε : ℝ)) : ℝ) ≤
      s * S + (C + 2 * Real.logb 2 n + 2 * Real.logb 2 S) := by
    rw [hC]
    linarith
  rw [orbitBSRate, ← hSdef, natCast_div_ofReal_eq _ hSpos]
  calc ENNReal.ofReal ((orbitComplexityNat P T A x n (6 * (ε : ℝ)) : ℝ) / S)
      ≤ ENNReal.ofReal (s + (C + 2 * Real.logb 2 n + 2 * Real.logb 2 S) / S) := by
        refine ENNReal.ofReal_le_ofReal ?_
        rw [div_le_iff₀ hSpos, add_mul, div_mul_cancel₀ _ hSpos.ne']
        linarith
    _ ≤ _ := ENNReal.ofReal_add_le

/-- Theorem 8.3(ii) at a fixed scale, pressure: at a random point the local pressures at the
scale `2ε` are at most the lower and upper rates of `K_n^A(x, T, ε) + S_n φ(x)`. -/
theorem localPressureAt_le_orbitPressureRate (P : Presentation X) (T : X → X)
    (hT : Continuous T) (φ : X → ℝ) (A : Set ℕ) (μ : Measure X) [IsProbabilityMeasure μ]
    (hA : IsMeasureAdmissible P T μ A) (ε : ℚ) (hε : 0 < ε) {x : X}
    (hxr : x ∈ randomPoints P A μ) :
    (localPressureAt μ T φ x (2 * (ε : ℝ))).1 ≤
        liminf (fun n ↦ orbitPressureRate P T φ A x n (ε : ℝ)) atTop ∧
      (localPressureAt μ T φ x (2 * (ε : ℝ))).2 ≤
        limsup (fun n ↦ orbitPressureRate P T φ A x n (ε : ℝ)) atTop := by
  obtain ⟨m, hm⟩ := exists_measure_bowenBall_ge_of_mem_randomPoints P T hT A μ hA ε hε hxr
  refine liminf_limsup_le_of_le_add_coe_tendsto_zero (tendsto_add_mul_logb_div_nat m 2) ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  set K := orbitComplexityNat P T A x n ε with hK
  have hge : ENNReal.ofReal ((2 : ℝ) ^ (-(((K + m : ℕ) : ℝ) + 2 * Real.logb 2 n))) ≤
      μ (bowenBall T n x (2 * ε)) := by
    rw [ofReal_two_rpow_neg_add_logb_eq _ hn]
    exact hm n hn
  have h0 : μ (bowenBall T n x (2 * ε)) ≠ 0 :=
    (lt_of_lt_of_le (ENNReal.ofReal_pos.2 (Real.rpow_pos_of_pos two_pos _)) hge).ne'
  have hI := neg_logb_toReal_le_of_rpow_le (measure_ne_top μ _) hge
  push_cast at hI
  simp only [localPressureRate, h0, ↓reduceIte, orbitPressureRate]
  rw [← EReal.coe_add, EReal.coe_le_coe_iff, ← add_div]
  exact div_le_div_of_nonneg_right (by linarith) hn0.le

/-- Theorem 8.3(ii) at a fixed scale, BS dimension: at a random point of positive lower
Birkhoff average the local BS dimensions at the scale `2ε` are at most the lower and upper
rates of `K_n^A(x, T, ε) / S_n u(x)`. -/
theorem localBSDimensionAt_le_orbitBSRate (P : Presentation X) (T : X → X)
    (hT : Continuous T) (u : X → ℝ) (A : Set ℕ) (μ : Measure X) [IsProbabilityMeasure μ]
    (hA : IsMeasureAdmissible P T μ A) (ε : ℚ) (hε : 0 < ε) {x : X}
    (hxr : x ∈ randomPoints P A μ) (hx : 0 < lowerBirkhoffAverage T u x) :
    (localBSDimensionAt μ T u x (2 * (ε : ℝ))).1 ≤
        liminf (fun n ↦ orbitBSRate P T u A x n (ε : ℝ)) atTop ∧
      (localBSDimensionAt μ T u x (2 * (ε : ℝ))).2 ≤
        limsup (fun n ↦ orbitBSRate P T u A x n (ε : ℝ)) atTop := by
  obtain ⟨m, hm⟩ := exists_measure_bowenBall_ge_of_mem_randomPoints P T hT A μ hA ε hε hxr
  have hd : Tendsto (fun n : ℕ ↦ ENNReal.ofReal ((m + 2 * Real.logb 2 n) /
      birkhoffSum T u n x)) atTop (𝓝 0) := by
    have := tendsto_div_birkhoffSum_of_tendsto_div hx ((eventually_ge_atTop 1).mono
      fun n hn ↦ by
        have := Real.logb_nonneg one_lt_two (show (1 : ℝ) ≤ n by exact_mod_cast hn)
        positivity) (tendsto_add_mul_logb_div_nat m 2)
    simpa using ENNReal.tendsto_ofReal this
  have hev : ∀ᶠ n in atTop, localBSRate μ T u x n (2 * ε) ≤ orbitBSRate P T u A x n ε +
      ENNReal.ofReal ((m + 2 * Real.logb 2 n) / birkhoffSum T u n x) := by
    filter_upwards [eventually_ge_atTop 1, (tendsto_birkhoffSum_atTop hx).eventually_gt_atTop 0]
      with n hn hS
    set K := orbitComplexityNat P T A x n ε with hK
    have hL : 0 ≤ Real.logb 2 n := Real.logb_nonneg one_lt_two (by exact_mod_cast hn)
    have hinfo : infoBits (μ (bowenBall T n x (2 * ε))) ≤
        ENNReal.ofReal (((K + m : ℕ) : ℝ) + 2 * Real.logb 2 n) := by
      refine infoBits_le_of_rpow_le (by positivity) ?_
      rw [ofReal_two_rpow_neg_add_logb_eq _ hn]
      exact hm n hn
    rw [localBSRate, orbitBSRate, natCast_div_ofReal_eq _ hS]
    calc infoBits (μ (bowenBall T n x (2 * ε))) / ENNReal.ofReal (birkhoffSum T u n x)
        ≤ ENNReal.ofReal (((K + m : ℕ) : ℝ) + 2 * Real.logb 2 n) /
            ENNReal.ofReal (birkhoffSum T u n x) := by gcongr
      _ = ENNReal.ofReal ((K : ℝ) / birkhoffSum T u n x +
            (m + 2 * Real.logb 2 n) / birkhoffSum T u n x) := by
          rw [← ENNReal.ofReal_div_of_pos hS]
          congr 1
          push_cast
          ring
      _ ≤ _ := ENNReal.ofReal_add_le
  exact ⟨liminf_le_liminf_of_le_add_tendsto_zero hev hd,
    limsup_le_limsup_of_le_add_tendsto_zero hev hd⟩

/-- `2 · 2^{-(p + 1)} = 2^{-p}`. -/
private theorem two_mul_dyadicRadius_succ (p : ℕ) : 2 * dyadicRadius (p + 1) = dyadicRadius p := by
  rw [dyadicRadius, dyadicRadius, pow_succ]
  ring

/-! ### Theorem 8.3 -/

/-- Theorem 8.3(i), pressure: at every point with `inf_n S_n φ(x) / n > -∞` the pointwise
pressures are at most the local pressures. Blueprint node `meas:pressure-pointwise`. -/
theorem pointwisePressure_le_localPressure (P : Presentation X) (T : X → X)
    (hT : Continuous T) (φ : X → ℝ) (hφ : UniformContinuous φ) (A : Set ℕ) (μ : Measure X)
    [IsFiniteMeasure μ] (hμ : μ univ ≤ 1) (hA : IsMeasureAdmissible P T μ A) {x : X}
    (hx : BirkhoffBoundedBelow T φ x) :
    (pointwisePressure P T φ A x).1 ≤ (localPressure μ T φ x).1 ∧
      (pointwisePressure P T φ A x).2 ≤ (localPressure μ T φ x).2 := by
  rw [pointwisePressure_eq_orbitPressureRate P T hT φ hφ A x]
  have key : ∀ p : ℕ,
      liminf (fun n ↦ orbitPressureRate P T φ A x n (dyadicRadius p)) atTop ≤
        (localPressure μ T φ x).1 ∧
      limsup (fun n ↦ orbitPressureRate P T φ A x n (dyadicRadius p)) atTop ≤
        (localPressure μ T φ x).2 := by
    intro p
    have hε : (0 : ℚ) < (2 : ℚ)⁻¹ ^ (p + 3) := by positivity
    have h := orbitPressureRate_le_localPressureAt P T hT φ A μ hμ hA _ hε hx
    rw [← dyadicRadius_eq_ratCast] at h
    have hmono : ∀ᶠ n in atTop, orbitPressureRate P T φ A x n (dyadicRadius p) ≤
        orbitPressureRate P T φ A x n (6 * dyadicRadius (p + 3)) :=
      (eventually_ge_atTop 1).mono fun n hn ↦ orbitPressureRate_le_of_le_radius P T hT φ A x hn
        (mul_pos (by norm_num) (dyadicRadius_pos _)) (six_mul_dyadicRadius_add_three_le p)
    exact ⟨(liminf_le_liminf hmono).trans (h.1.trans
        (le_iSup (fun q ↦ (localPressureAt μ T φ x (dyadicRadius q)).1) (p + 3))),
      (limsup_le_limsup hmono).trans (h.2.trans
        (le_iSup (fun q ↦ (localPressureAt μ T φ x (dyadicRadius q)).2) (p + 3)))⟩
  exact ⟨iSup_le fun p ↦ (key p).1, iSup_le fun p ↦ (key p).2⟩

/-- Theorem 8.3(i), BS dimension: at every point of positive lower Birkhoff average the
pointwise BS dimensions are at most the local BS dimensions.
Blueprint node `meas:pressure-pointwise`. -/
theorem pointwiseBSDimension_le_localBSDimension (P : Presentation X) (T : X → X)
    (hT : Continuous T) (u : X → ℝ) (hu : UniformContinuous u) (A : Set ℕ) (μ : Measure X)
    [IsFiniteMeasure μ] (hμ : μ univ ≤ 1) (hA : IsMeasureAdmissible P T μ A) {x : X}
    (hx : 0 < lowerBirkhoffAverage T u x) :
    (pointwiseBSDimension P T u A x).1 ≤ (localBSDimension μ T u x).1 ∧
      (pointwiseBSDimension P T u A x).2 ≤ (localBSDimension μ T u x).2 := by
  rw [pointwiseBSDimension_eq_orbitBSRate P T hT u hu A hx]
  have key : ∀ p : ℕ,
      liminf (fun n ↦ orbitBSRate P T u A x n (dyadicRadius p)) atTop ≤
        (localBSDimension μ T u x).1 ∧
      limsup (fun n ↦ orbitBSRate P T u A x n (dyadicRadius p)) atTop ≤
        (localBSDimension μ T u x).2 := by
    intro p
    have hε : (0 : ℚ) < (2 : ℚ)⁻¹ ^ (p + 3) := by positivity
    have h := orbitBSRate_le_localBSDimensionAt P T hT u A μ hμ hA _ hε hx
    rw [← dyadicRadius_eq_ratCast] at h
    have hmono : ∀ᶠ n in atTop, orbitBSRate P T u A x n (dyadicRadius p) ≤
        orbitBSRate P T u A x n (6 * dyadicRadius (p + 3)) :=
      (eventually_ge_atTop 1).mono fun n hn ↦ orbitBSRate_le_of_le_radius P T hT u A x hn
        (mul_pos (by norm_num) (dyadicRadius_pos _)) (six_mul_dyadicRadius_add_three_le p)
    exact ⟨(liminf_le_liminf hmono).trans (h.1.trans
        (le_iSup (fun q ↦ (localBSDimensionAt μ T u x (dyadicRadius q)).1) (p + 3))),
      (limsup_le_limsup hmono).trans (h.2.trans
        (le_iSup (fun q ↦ (localBSDimensionAt μ T u x (dyadicRadius q)).2) (p + 3)))⟩
  exact ⟨iSup_le fun p ↦ (key p).1, iSup_le fun p ↦ (key p).2⟩

/-- Theorem 8.3(ii), pressure: at every random point with `inf_n S_n φ(x) / n > -∞` the
pointwise pressures equal the local pressures. Blueprint node `meas:pressure-pointwise`. -/
theorem pointwisePressure_eq_localPressure (P : Presentation X) (T : X → X)
    (hT : Continuous T) (φ : X → ℝ) (hφ : UniformContinuous φ) (A : Set ℕ) (μ : Measure X)
    [IsProbabilityMeasure μ] (hA : IsMeasureAdmissible P T μ A) {x : X}
    (hxr : x ∈ randomPoints P A μ) (hx : BirkhoffBoundedBelow T φ x) :
    pointwisePressure P T φ A x = localPressure μ T φ x := by
  have hle := pointwisePressure_le_localPressure P T hT φ hφ A μ prob_le_one hA hx
  rw [pointwisePressure_eq_orbitPressureRate P T hT φ hφ A x] at hle ⊢
  have hge : ∀ p : ℕ, (localPressureAt μ T φ x (dyadicRadius p)).1 ≤
        ⨆ q : ℕ, liminf (fun n ↦ orbitPressureRate P T φ A x n (dyadicRadius q)) atTop ∧
      (localPressureAt μ T φ x (dyadicRadius p)).2 ≤
        ⨆ q : ℕ, limsup (fun n ↦ orbitPressureRate P T φ A x n (dyadicRadius q)) atTop := by
    intro p
    have hε : (0 : ℚ) < (2 : ℚ)⁻¹ ^ (p + 1) := by positivity
    have h := localPressureAt_le_orbitPressureRate P T hT φ A μ hA _ hε hxr
    rw [← dyadicRadius_eq_ratCast, two_mul_dyadicRadius_succ] at h
    exact ⟨h.1.trans (le_iSup (fun q ↦ liminf (fun n ↦
        orbitPressureRate P T φ A x n (dyadicRadius q)) atTop) (p + 1)),
      h.2.trans (le_iSup (fun q ↦ limsup (fun n ↦
        orbitPressureRate P T φ A x n (dyadicRadius q)) atTop) (p + 1))⟩
  exact Prod.ext (le_antisymm hle.1 (iSup_le fun p ↦ (hge p).1))
    (le_antisymm hle.2 (iSup_le fun p ↦ (hge p).2))

/-- Theorem 8.3(ii), BS dimension: at every random point of positive lower Birkhoff average
the pointwise BS dimensions equal the local BS dimensions.
Blueprint node `meas:pressure-pointwise`. -/
theorem pointwiseBSDimension_eq_localBSDimension (P : Presentation X) (T : X → X)
    (hT : Continuous T) (u : X → ℝ) (hu : UniformContinuous u) (A : Set ℕ) (μ : Measure X)
    [IsProbabilityMeasure μ] (hA : IsMeasureAdmissible P T μ A) {x : X}
    (hxr : x ∈ randomPoints P A μ) (hx : 0 < lowerBirkhoffAverage T u x) :
    pointwiseBSDimension P T u A x = localBSDimension μ T u x := by
  have hle := pointwiseBSDimension_le_localBSDimension P T hT u hu A μ prob_le_one hA hx
  rw [pointwiseBSDimension_eq_orbitBSRate P T hT u hu A hx] at hle ⊢
  have hge : ∀ p : ℕ, (localBSDimensionAt μ T u x (dyadicRadius p)).1 ≤
        ⨆ q : ℕ, liminf (fun n ↦ orbitBSRate P T u A x n (dyadicRadius q)) atTop ∧
      (localBSDimensionAt μ T u x (dyadicRadius p)).2 ≤
        ⨆ q : ℕ, limsup (fun n ↦ orbitBSRate P T u A x n (dyadicRadius q)) atTop := by
    intro p
    have hε : (0 : ℚ) < (2 : ℚ)⁻¹ ^ (p + 1) := by positivity
    have h := localBSDimensionAt_le_orbitBSRate P T hT u A μ hA _ hε hxr hx
    rw [← dyadicRadius_eq_ratCast, two_mul_dyadicRadius_succ] at h
    exact ⟨h.1.trans (le_iSup (fun q ↦ liminf (fun n ↦
        orbitBSRate P T u A x n (dyadicRadius q)) atTop) (p + 1)),
      h.2.trans (le_iSup (fun q ↦ limsup (fun n ↦
        orbitBSRate P T u A x n (dyadicRadius q)) atTop) (p + 1))⟩
  exact Prod.ext (le_antisymm hle.1 (iSup_le fun p ↦ (hge p).1))
    (le_antisymm hle.2 (iSup_le fun p ↦ (hge p).2))

/-- Theorem 8.3(iii), pressure: with the universal measure, equality holds at every point
with `inf_n S_n φ(x) / n > -∞`. Blueprint node `meas:pressure-pointwise`. -/
theorem pointwisePressure_eq_localPressure_universalMeasure (P : Presentation X) (T : X → X)
    (hT : Continuous T) (φ : X → ℝ) (hφ : UniformContinuous φ) (A : Set ℕ)
    (hP : ComputablePresentationIn P A) (hTA : IsRepresentedMapIn P P A T) {x : X}
    (hx : BirkhoffBoundedBelow T φ x) :
    pointwisePressure P T φ A x = localPressure (universalMeasure P A) T φ x := by
  have hle := pointwisePressure_le_localPressure P T hT φ hφ A (universalMeasure P A)
    (universalMeasure_univ_le_one P A) (isMeasureAdmissible_universalMeasure P T A hP hTA) hx
  rw [pointwisePressure_eq_orbitPressureRate P T hT φ hφ A x] at hle ⊢
  have hrate : ∀ p : ℕ, ∀ᶠ n in atTop,
      localPressureRate (universalMeasure P A) T φ x n (dyadicRadius p) ≤
        orbitPressureRate P T φ A x n (dyadicRadius p) := by
    intro p
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    have hge : ENNReal.ofReal ((2 : ℝ) ^ (-(orbitComplexityNat P T A x n (dyadicRadius p) : ℝ)))
        ≤ universalMeasure P A (bowenBall T n x (dyadicRadius p)) := by
      rw [ofReal_two_rpow_neg_natCast_eq]
      exact universalMeasure_bowenBall_ge P T hT A x hn (dyadicRadius_pos p)
    have h0 : universalMeasure P A (bowenBall T n x (dyadicRadius p)) ≠ 0 :=
      (lt_of_lt_of_le (ENNReal.ofReal_pos.2 (Real.rpow_pos_of_pos two_pos _)) hge).ne'
    have hI := neg_logb_toReal_le_of_rpow_le (measure_ne_top _ _) hge
    simp only [localPressureRate, h0, ↓reduceIte, orbitPressureRate, EReal.coe_le_coe_iff]
    exact div_le_div_of_nonneg_right (by linarith) hn0.le
  exact Prod.ext
    (le_antisymm hle.1 (iSup_le fun p ↦ (liminf_le_liminf (hrate p)).trans (le_iSup (fun q ↦
      liminf (fun n ↦ orbitPressureRate P T φ A x n (dyadicRadius q)) atTop) p)))
    (le_antisymm hle.2 (iSup_le fun p ↦ (limsup_le_limsup (hrate p)).trans (le_iSup (fun q ↦
      limsup (fun n ↦ orbitPressureRate P T φ A x n (dyadicRadius q)) atTop) p)))

/-- Theorem 8.3(iii), BS dimension: with the universal measure, equality holds at every point
of positive lower Birkhoff average. Blueprint node `meas:pressure-pointwise`. -/
theorem pointwiseBSDimension_eq_localBSDimension_universalMeasure (P : Presentation X)
    (T : X → X) (hT : Continuous T) (u : X → ℝ) (hu : UniformContinuous u) (A : Set ℕ)
    (hP : ComputablePresentationIn P A) (hTA : IsRepresentedMapIn P P A T) {x : X}
    (hx : 0 < lowerBirkhoffAverage T u x) :
    pointwiseBSDimension P T u A x = localBSDimension (universalMeasure P A) T u x := by
  have hle := pointwiseBSDimension_le_localBSDimension P T hT u hu A (universalMeasure P A)
    (universalMeasure_univ_le_one P A) (isMeasureAdmissible_universalMeasure P T A hP hTA) hx
  rw [pointwiseBSDimension_eq_orbitBSRate P T hT u hu A hx] at hle ⊢
  have hrate : ∀ p : ℕ, ∀ᶠ n in atTop,
      localBSRate (universalMeasure P A) T u x n (dyadicRadius p) ≤
        orbitBSRate P T u A x n (dyadicRadius p) := by
    intro p
    filter_upwards [eventually_ge_atTop 1] with n hn
    refine ENNReal.div_le_div_right ?_ _
    calc infoBits (universalMeasure P A (bowenBall T n x (dyadicRadius p)))
        ≤ ENNReal.ofReal (orbitComplexityNat P T A x n (dyadicRadius p) : ℝ) := by
          refine infoBits_le_of_rpow_le (by positivity) ?_
          rw [ofReal_two_rpow_neg_natCast_eq]
          exact universalMeasure_bowenBall_ge P T hT A x hn (dyadicRadius_pos p)
      _ = _ := ENNReal.ofReal_natCast _
  exact Prod.ext
    (le_antisymm hle.1 (iSup_le fun p ↦ (liminf_le_liminf (hrate p)).trans (le_iSup (fun q ↦
      liminf (fun n ↦ orbitBSRate P T u A x n (dyadicRadius q)) atTop) p)))
    (le_antisymm hle.2 (iSup_le fun p ↦ (limsup_le_limsup (hrate p)).trans (le_iSup (fun q ↦
      limsup (fun n ↦ orbitBSRate P T u A x n (dyadicRadius q)) atTop) p)))

/-! ### Corollary 8.4: Billingsley-type bounds -/

/-- Corollary 8.4(a), lower pressure. Blueprint node `meas:pressure-billingsley`. -/
theorem lowerPressure_le_of_localPressure_le (D : PressureData X) (μ : Measure X)
    [IsProbabilityMeasure μ] (Z : Set X) (hZ : ∀ x ∈ Z, BirkhoffBoundedBelow D.T D.φ x)
    (s : EReal) (h : ∀ x ∈ Z, (localPressure μ D.T D.φ x).1 ≤ s) :
    lowerPressure D.T D.φ D.p₀ Z ≤ s := by
  obtain ⟨C, hC⟩ := exists_measureAdmissible_base D.presentation D.T D.continuous_T μ
  refine (lowerPressure_pointToSet_all_oracles D Z C).trans (iSup₂_le fun x hx ↦ ?_)
  exact (pointwisePressure_le_localPressure D.presentation D.T D.continuous_T D.φ
    D.uniformContinuous_φ C μ prob_le_one (hC C (TuringReducible.refl _)) (hZ x hx)).1.trans
    (h x hx)

/-- Corollary 8.4(a), upper pressure. Blueprint node `meas:pressure-billingsley`. -/
theorem upperPressure_le_of_localPressure_le (D : PressureData X) (μ : Measure X)
    [IsProbabilityMeasure μ] (Z : Set X) (hZ : ∀ x ∈ Z, BirkhoffBoundedBelow D.T D.φ x)
    (s : EReal) (h : ∀ x ∈ Z, (localPressure μ D.T D.φ x).2 ≤ s) :
    upperPressure D.T D.φ D.p₀ Z ≤ s := by
  obtain ⟨C, hC⟩ := exists_measureAdmissible_base D.presentation D.T D.continuous_T μ
  refine (upperPressure_pointToSet_all_oracles D Z C).trans (iSup₂_le fun x hx ↦ ?_)
  exact (pointwisePressure_le_localPressure D.presentation D.T D.continuous_T D.φ
    D.uniformContinuous_φ C μ prob_le_one (hC C (TuringReducible.refl _)) (hZ x hx)).2.trans
    (h x hx)

/-- Corollary 8.4(a), lower BS dimension. Blueprint node `meas:pressure-billingsley`. -/
theorem lowerBSDimension_le_of_localBSDimension_le (P : Presentation X) (T : X → X)
    (hT : Continuous T) (u : X → ℝ) (hu : UniformContinuous u) (μ : Measure X)
    [IsProbabilityMeasure μ] (Z : Set X) (hZ : ∀ x ∈ Z, 0 < lowerBirkhoffAverage T u x)
    (s : ℝ≥0∞) (h : ∀ x ∈ Z, (localBSDimension μ T u x).1 ≤ s) :
    lowerBSDimension T u Z ≤ s := by
  obtain ⟨C, hC⟩ := exists_measureAdmissible_base P T hT μ
  have h1 := bsPointToSet_all_oracles P T hT u hu Z hZ C LimitSide.lower
  simp only [LimitSide.choose] at h1
  refine h1.trans (iSup₂_le fun x hx ↦ ?_)
  exact (pointwiseBSDimension_le_localBSDimension P T hT u hu C μ prob_le_one
    (hC C (TuringReducible.refl _)) (hZ x hx)).1.trans (h x hx)

/-- Corollary 8.4(a), upper BS dimension. Blueprint node `meas:pressure-billingsley`. -/
theorem upperBSDimension_le_of_localBSDimension_le (P : Presentation X) (T : X → X)
    (hT : Continuous T) (u : X → ℝ) (hu : UniformContinuous u) (μ : Measure X)
    [IsProbabilityMeasure μ] (Z : Set X) (hZ : ∀ x ∈ Z, 0 < lowerBirkhoffAverage T u x)
    (s : ℝ≥0∞) (h : ∀ x ∈ Z, (localBSDimension μ T u x).2 ≤ s) :
    upperBSDimension T u Z ≤ s := by
  obtain ⟨C, hC⟩ := exists_measureAdmissible_base P T hT μ
  have h1 := bsPointToSet_all_oracles P T hT u hu Z hZ C LimitSide.upper
  simp only [LimitSide.choose] at h1
  refine h1.trans (iSup₂_le fun x hx ↦ ?_)
  exact (pointwiseBSDimension_le_localBSDimension P T hT u hu C μ prob_le_one
    (hC C (TuringReducible.refl _)) (hZ x hx)).2.trans (h x hx)

/-- Corollary 8.4(b), lower pressure. Blueprint node `meas:pressure-billingsley`. -/
theorem le_lowerPressure_of_le_localPressure (D : PressureData X) (μ : Measure X)
    [IsProbabilityMeasure μ] {Z : Set X} (hμZ : μ Z ≠ 0)
    (hZ : ∀ x ∈ Z, BirkhoffBoundedBelow D.T D.φ x) (s : EReal)
    (h : ∀ x ∈ Z, s ≤ (localPressure μ D.T D.φ x).1) :
    s ≤ lowerPressure D.T D.φ D.p₀ Z := by
  obtain ⟨B, hB⟩ := lowerPressure_pointToSet_cone D Z
  obtain ⟨C, hC⟩ := exists_measureAdmissible_base D.presentation D.T D.continuous_T μ
  have hA := hC (oracleJoin B C) (oracle_joins_right B C)
  obtain ⟨x, hxZ, hx⟩ :=
    exists_mem_randomPoints_of_measure_pos D.presentation (oracleJoin B C) μ hμZ
  rw [hB _ (oracle_joins B C)]
  calc s ≤ (localPressure μ D.T D.φ x).1 := h x hxZ
    _ = (pointwisePressure D.presentation D.T D.φ (oracleJoin B C) x).1 := by
        rw [pointwisePressure_eq_localPressure D.presentation D.T D.continuous_T D.φ
          D.uniformContinuous_φ _ μ hA hx (hZ x hxZ)]
    _ ≤ ⨆ y ∈ Z, (pointwisePressure D.presentation D.T D.φ (oracleJoin B C) y).1 :=
        le_iSup₂ (f := fun y _ ↦ (pointwisePressure D.presentation D.T D.φ (oracleJoin B C) y).1)
          x hxZ

/-- Corollary 8.4(b), upper pressure. Blueprint node `meas:pressure-billingsley`. -/
theorem le_upperPressure_of_le_localPressure (D : PressureData X) (μ : Measure X)
    [IsProbabilityMeasure μ] {Z : Set X} (hμZ : μ Z ≠ 0)
    (hZ : ∀ x ∈ Z, BirkhoffBoundedBelow D.T D.φ x) (s : EReal)
    (h : ∀ x ∈ Z, s ≤ (localPressure μ D.T D.φ x).2) :
    s ≤ upperPressure D.T D.φ D.p₀ Z := by
  obtain ⟨B, hB⟩ := upperPressure_pointToSet_cone D Z
  obtain ⟨C, hC⟩ := exists_measureAdmissible_base D.presentation D.T D.continuous_T μ
  have hA := hC (oracleJoin B C) (oracle_joins_right B C)
  obtain ⟨x, hxZ, hx⟩ :=
    exists_mem_randomPoints_of_measure_pos D.presentation (oracleJoin B C) μ hμZ
  rw [hB _ (oracle_joins B C)]
  calc s ≤ (localPressure μ D.T D.φ x).2 := h x hxZ
    _ = (pointwisePressure D.presentation D.T D.φ (oracleJoin B C) x).2 := by
        rw [pointwisePressure_eq_localPressure D.presentation D.T D.continuous_T D.φ
          D.uniformContinuous_φ _ μ hA hx (hZ x hxZ)]
    _ ≤ ⨆ y ∈ Z, (pointwisePressure D.presentation D.T D.φ (oracleJoin B C) y).2 :=
        le_iSup₂ (f := fun y _ ↦ (pointwisePressure D.presentation D.T D.φ (oracleJoin B C) y).2)
          x hxZ

/-- Corollary 8.4(b), lower BS dimension. Blueprint node `meas:pressure-billingsley`. -/
theorem le_lowerBSDimension_of_le_localBSDimension (P : Presentation X) (T : X → X)
    (hT : Continuous T) (u : X → ℝ) (hu : UniformContinuous u) (μ : Measure X)
    [IsProbabilityMeasure μ] {Z : Set X} (hμZ : μ Z ≠ 0)
    (hZ : ∀ x ∈ Z, 0 < lowerBirkhoffAverage T u x) (s : ℝ≥0∞)
    (h : ∀ x ∈ Z, s ≤ (localBSDimension μ T u x).1) : s ≤ lowerBSDimension T u Z := by
  obtain ⟨B, hB⟩ := bsPointToSet_cone P T hT u hu Z hZ
  obtain ⟨C, hC⟩ := exists_measureAdmissible_base P T hT μ
  have hA := hC (oracleJoin B C) (oracle_joins_right B C)
  obtain ⟨x, hxZ, hx⟩ := exists_mem_randomPoints_of_measure_pos P (oracleJoin B C) μ hμZ
  have heq := (hB (oracleJoin B C) (oracle_joins B C)).2 LimitSide.lower
  simp only [LimitSide.choose] at heq
  rw [heq]
  calc s ≤ (localBSDimension μ T u x).1 := h x hxZ
    _ = (pointwiseBSDimension P T u (oracleJoin B C) x).1 := by
        rw [pointwiseBSDimension_eq_localBSDimension P T hT u hu _ μ hA hx (hZ x hxZ)]
    _ ≤ ⨆ y ∈ Z, (pointwiseBSDimension P T u (oracleJoin B C) y).1 :=
        le_iSup₂ (f := fun y _ ↦ (pointwiseBSDimension P T u (oracleJoin B C) y).1) x hxZ

/-- Corollary 8.4(b), upper BS dimension. Blueprint node `meas:pressure-billingsley`. -/
theorem le_upperBSDimension_of_le_localBSDimension (P : Presentation X) (T : X → X)
    (hT : Continuous T) (u : X → ℝ) (hu : UniformContinuous u) (μ : Measure X)
    [IsProbabilityMeasure μ] {Z : Set X} (hμZ : μ Z ≠ 0)
    (hZ : ∀ x ∈ Z, 0 < lowerBirkhoffAverage T u x) (s : ℝ≥0∞)
    (h : ∀ x ∈ Z, s ≤ (localBSDimension μ T u x).2) : s ≤ upperBSDimension T u Z := by
  obtain ⟨B, hB⟩ := bsPointToSet_cone P T hT u hu Z hZ
  obtain ⟨C, hC⟩ := exists_measureAdmissible_base P T hT μ
  have hA := hC (oracleJoin B C) (oracle_joins_right B C)
  obtain ⟨x, hxZ, hx⟩ := exists_mem_randomPoints_of_measure_pos P (oracleJoin B C) μ hμZ
  have heq := (hB (oracleJoin B C) (oracle_joins B C)).2 LimitSide.upper
  simp only [LimitSide.choose] at heq
  rw [heq]
  calc s ≤ (localBSDimension μ T u x).2 := h x hxZ
    _ = (pointwiseBSDimension P T u (oracleJoin B C) x).2 := by
        rw [pointwiseBSDimension_eq_localBSDimension P T hT u hu _ μ hA hx (hZ x hxZ)]
    _ ≤ ⨆ y ∈ Z, (pointwiseBSDimension P T u (oracleJoin B C) y).2 :=
        le_iSup₂ (f := fun y _ ↦ (pointwiseBSDimension P T u (oracleJoin B C) y).2) x hxZ

/-! ### Corollary 8.4: dual principles -/

omit [BorelSpace X] in
/-- Above every oracle `B` there is an oracle `A` computing the metric table and representing
the dynamics, together with a normalizing constant that makes its universal measure a
probability measure. -/
private theorem exists_normalized_universalMeasure (P : Presentation X) (T : X → X)
    (hT : Continuous T) (B : Set ℕ) :
    ∃ A : Set ℕ, charOracle B ≤ᵀ charOracle A ∧ ComputablePresentationIn P A ∧
      IsRepresentedMapIn P P A T ∧ ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧
        IsProbabilityMeasure (c • universalMeasure P A) := by
  obtain ⟨C, hC⟩ := exists_admissible_base P T hT (fun j : Fin 0 ↦ j.elim0) (fun j ↦ j.elim0)
  have hAd := hC (oracleJoin B C) (oracle_joins_right B C)
  have h0 := universalMeasure_univ_ne_zero P (oracleJoin B C)
  have htop := measure_ne_top (universalMeasure P (oracleJoin B C)) univ
  exact ⟨oracleJoin B C, oracle_joins B C, hAd.1, hAd.2.1, _, ENNReal.inv_ne_zero.2 htop,
    ENNReal.inv_ne_top.2 h0, ⟨by simp [Measure.smul_apply, ENNReal.inv_mul_cancel h0 htop]⟩⟩

/-- Corollary 8.4(c), lower pressure: `P̲(Z, T, φ) = min_μ sup_{x ∈ Z} P̲_μ(x, T, φ)` over
Borel probability measures. Blueprint node `meas:pressure-dual`. -/
theorem lowerPressure_eq_iInf_measure (D : PressureData X) {Z : Set X}
    (hZ : ∀ x ∈ Z, BirkhoffBoundedBelow D.T D.φ x) :
    lowerPressure D.T D.φ D.p₀ Z =
      ⨅ (μ : Measure X) (_ : IsProbabilityMeasure μ),
        ⨆ x ∈ Z, (localPressure μ D.T D.φ x).1 := by
  refine le_antisymm (le_iInf₂ fun μ hμ ↦ lowerPressure_le_of_localPressure_le D μ Z hZ _
    fun x hx ↦ le_iSup₂ (f := fun x _ ↦ (localPressure μ D.T D.φ x).1) x hx) ?_
  obtain ⟨B, hB⟩ := lowerPressure_pointToSet_cone D Z
  obtain ⟨A, hBA, hP, hTA, c, hc0, hc, hμ⟩ :=
    exists_normalized_universalMeasure D.presentation D.T D.continuous_T B
  refine iInf₂_le_of_le (c • universalMeasure D.presentation A) hμ ?_
  rw [hB A hBA]
  refine iSup₂_le fun x hx ↦ ?_
  rw [localPressure_smul _ _ _ _ hc0 hc, ← pointwisePressure_eq_localPressure_universalMeasure
    D.presentation D.T D.continuous_T D.φ D.uniformContinuous_φ A hP hTA (hZ x hx)]
  exact le_iSup₂ (f := fun y _ ↦ (pointwisePressure D.presentation D.T D.φ A y).1) x hx

/-- Corollary 8.4(c), upper pressure. Blueprint node `meas:pressure-dual`. -/
theorem upperPressure_eq_iInf_measure (D : PressureData X) {Z : Set X}
    (hZ : ∀ x ∈ Z, BirkhoffBoundedBelow D.T D.φ x) :
    upperPressure D.T D.φ D.p₀ Z =
      ⨅ (μ : Measure X) (_ : IsProbabilityMeasure μ),
        ⨆ x ∈ Z, (localPressure μ D.T D.φ x).2 := by
  refine le_antisymm (le_iInf₂ fun μ hμ ↦ upperPressure_le_of_localPressure_le D μ Z hZ _
    fun x hx ↦ le_iSup₂ (f := fun x _ ↦ (localPressure μ D.T D.φ x).2) x hx) ?_
  obtain ⟨B, hB⟩ := upperPressure_pointToSet_cone D Z
  obtain ⟨A, hBA, hP, hTA, c, hc0, hc, hμ⟩ :=
    exists_normalized_universalMeasure D.presentation D.T D.continuous_T B
  refine iInf₂_le_of_le (c • universalMeasure D.presentation A) hμ ?_
  rw [hB A hBA]
  refine iSup₂_le fun x hx ↦ ?_
  rw [localPressure_smul _ _ _ _ hc0 hc, ← pointwisePressure_eq_localPressure_universalMeasure
    D.presentation D.T D.continuous_T D.φ D.uniformContinuous_φ A hP hTA (hZ x hx)]
  exact le_iSup₂ (f := fun y _ ↦ (pointwisePressure D.presentation D.T D.φ A y).2) x hx

/-- Corollary 8.4(c), lower BS dimension: `dim_BS(Z, T, u) = min_μ sup_{x ∈ Z} d̲_μ(x, T, u)`.
Blueprint node `meas:pressure-dual`. -/
theorem lowerBSDimension_eq_iInf_measure (P : Presentation X) (T : X → X) (hT : Continuous T)
    (u : X → ℝ) (hu : UniformContinuous u) {Z : Set X}
    (hZ : ∀ x ∈ Z, 0 < lowerBirkhoffAverage T u x) :
    lowerBSDimension T u Z =
      ⨅ (μ : Measure X) (_ : IsProbabilityMeasure μ),
        ⨆ x ∈ Z, (localBSDimension μ T u x).1 := by
  refine le_antisymm (le_iInf₂ fun μ hμ ↦ lowerBSDimension_le_of_localBSDimension_le P T hT u hu
    μ Z hZ _ fun x hx ↦ le_iSup₂ (f := fun x _ ↦ (localBSDimension μ T u x).1) x hx) ?_
  obtain ⟨B, hB⟩ := bsPointToSet_cone P T hT u hu Z hZ
  obtain ⟨A, hBA, hP, hTA, c, hc0, hc, hμ⟩ := exists_normalized_universalMeasure P T hT B
  refine iInf₂_le_of_le (c • universalMeasure P A) hμ ?_
  have heq := (hB A hBA).2 LimitSide.lower
  simp only [LimitSide.choose] at heq
  rw [heq]
  refine iSup₂_le fun x hx ↦ ?_
  rw [localBSDimension_smul _ _ _ (hZ x hx) hc0 hc,
    ← pointwiseBSDimension_eq_localBSDimension_universalMeasure P T hT u hu A hP hTA (hZ x hx)]
  exact le_iSup₂ (f := fun y _ ↦ (pointwiseBSDimension P T u A y).1) x hx

/-- Corollary 8.4(c), upper BS dimension. Blueprint node `meas:pressure-dual`. -/
theorem upperBSDimension_eq_iInf_measure (P : Presentation X) (T : X → X) (hT : Continuous T)
    (u : X → ℝ) (hu : UniformContinuous u) {Z : Set X}
    (hZ : ∀ x ∈ Z, 0 < lowerBirkhoffAverage T u x) :
    upperBSDimension T u Z =
      ⨅ (μ : Measure X) (_ : IsProbabilityMeasure μ),
        ⨆ x ∈ Z, (localBSDimension μ T u x).2 := by
  refine le_antisymm (le_iInf₂ fun μ hμ ↦ upperBSDimension_le_of_localBSDimension_le P T hT u hu
    μ Z hZ _ fun x hx ↦ le_iSup₂ (f := fun x _ ↦ (localBSDimension μ T u x).2) x hx) ?_
  obtain ⟨B, hB⟩ := bsPointToSet_cone P T hT u hu Z hZ
  obtain ⟨A, hBA, hP, hTA, c, hc0, hc, hμ⟩ := exists_normalized_universalMeasure P T hT B
  refine iInf₂_le_of_le (c • universalMeasure P A) hμ ?_
  have heq := (hB A hBA).2 LimitSide.upper
  simp only [LimitSide.choose] at heq
  rw [heq]
  refine iSup₂_le fun x hx ↦ ?_
  rw [localBSDimension_smul _ _ _ (hZ x hx) hc0 hc,
    ← pointwiseBSDimension_eq_localBSDimension_universalMeasure P T hT u hu A hP hTA (hZ x hx)]
  exact le_iSup₂ (f := fun y _ ↦ (pointwiseBSDimension P T u A y).2) x hx

end Kolmogorov.PointToSet
