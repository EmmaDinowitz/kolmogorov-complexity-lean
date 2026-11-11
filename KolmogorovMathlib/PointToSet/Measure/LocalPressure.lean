/-
Copyright (c) 2026 Emma Dinowitz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emma Dinowitz
-/
import KolmogorovMathlib.PointToSet.Measure.LocalPressureAux

/-!
# Local pressure and local BS dimension of a measure (§8)

For a finite Borel measure `μ`, a potential `φ` and a positive potential `u`, the local
pressure and the local Barreira–Schmeling dimension at a point `x` are

`P̲_μ(x, T, φ, ε) = liminf_n (-log₂ μ(B_n(x, T, ε)) + S_n φ(x)) / n`,
`d̲_μ(x, T, u, ε) = liminf_n -log₂ μ(B_n(x, T, ε)) / S_n u(x)`,

their limits as `ε → 0`, and the upper versions with `limsup` (E. Dinowitz, *Entropy of
non-invariant measures and orbit complexity of random points*, Definition 8.1). For `u = 1`
the local BS dimension is the local entropy.

Lemma 8.2 moves the weights of the pointwise pressure and BS dimension of the point-to-set
chapter from the ideal points of a Bowen ball to its centre: the pointwise quantities are the
rates of `K_n^A(x, T, ε) + S_n φ(x)` and of `K_n^A(x, T, ε) / S_n u(x)`.

* `localPressureRate`, `localPressureAt`, `localPressure`; `localBSRate`, `localBSDimensionAt`,
  `localBSDimension`.
* `orbitPressureRate`, `orbitBSRate`: the rates `(K_n^A(x, T, ε) + S_n φ(x)) / n` and
  `K_n^A(x, T, ε) / S_n u(x)`.
* `abs_finiteScalePressureCost_sub_le` (Lemma 8.2), `pointwisePressure_eq_orbitPressureRate`,
  `pointwiseBSDimension_eq_orbitBSRate`.
* `localBSDimension_one`, `localPressure_zero`, `localPressure_smul`, `localBSDimension_smul`:
  the local BS dimension of `u = 1` is the local entropy, the local pressure of `φ = 0` is the
  local entropy, and rescaling the measure changes neither.

The comparison lemmas for limits used here are in `Measure.LocalPressureAux`.

Blueprint nodes `meas:local-pressure`, `meas:weights`.
-/

namespace Kolmogorov.PointToSet

open Filter Set MeasureTheory
open scoped Topology ENNReal Computability

variable {X : Type*} [MetricSpace X] [MeasurableSpace X]

/-- The finite-time local pressure rate `(-log₂ μ(B_n(x, T, ε)) + S_n φ(x)) / n`, infinite when
the Bowen ball is null. Blueprint node `meas:local-pressure`. -/
noncomputable def localPressureRate (μ : Measure X) (T : X → X) (φ : X → ℝ) (x : X) (n : ℕ)
    (ε : ℝ) : EReal :=
  if μ (bowenBall T n x ε) = 0 then ⊤ else
    (((-Real.logb 2 (μ (bowenBall T n x ε)).toReal + birkhoffSum T φ n x) / n : ℝ) : EReal)

/-- The lower and upper local pressures at the scale `ε`. -/
noncomputable def localPressureAt (μ : Measure X) (T : X → X) (φ : X → ℝ) (x : X) (ε : ℝ) :
    EReal × EReal :=
  (liminf (fun n ↦ localPressureRate μ T φ x n ε) atTop,
    limsup (fun n ↦ localPressureRate μ T φ x n ε) atTop)

/-- The lower and upper local pressures `P̲_μ(x, T, φ)`, `P̄_μ(x, T, φ)` (Definition 8.1).
Blueprint node `meas:local-pressure`. -/
noncomputable def localPressure (μ : Measure X) (T : X → X) (φ : X → ℝ) (x : X) :
    EReal × EReal :=
  (⨆ p : ℕ, (localPressureAt μ T φ x (dyadicRadius p)).1,
    ⨆ p : ℕ, (localPressureAt μ T φ x (dyadicRadius p)).2)

/-- The finite-time local BS rate `-log₂ μ(B_n(x, T, ε)) / S_n u(x)`.
Blueprint node `meas:local-pressure`. -/
noncomputable def localBSRate (μ : Measure X) (T : X → X) (u : X → ℝ) (x : X) (n : ℕ)
    (ε : ℝ) : ℝ≥0∞ :=
  infoBits (μ (bowenBall T n x ε)) / ENNReal.ofReal (birkhoffSum T u n x)

/-- The lower and upper local BS dimensions at the scale `ε`. -/
noncomputable def localBSDimensionAt (μ : Measure X) (T : X → X) (u : X → ℝ) (x : X)
    (ε : ℝ) : ℝ≥0∞ × ℝ≥0∞ :=
  (liminf (fun n ↦ localBSRate μ T u x n ε) atTop,
    limsup (fun n ↦ localBSRate μ T u x n ε) atTop)

/-- The lower and upper local BS dimensions `d̲_μ(x, T, u)`, `d̄_μ(x, T, u)` (Definition 8.1).
Blueprint node `meas:local-pressure`. -/
noncomputable def localBSDimension (μ : Measure X) (T : X → X) (u : X → ℝ) (x : X) :
    ℝ≥0∞ × ℝ≥0∞ :=
  (⨆ p : ℕ, (localBSDimensionAt μ T u x (dyadicRadius p)).1,
    ⨆ p : ℕ, (localBSDimensionAt μ T u x (dyadicRadius p)).2)


/-! ### Elementary properties of the local quantities -/

/-- For `u = 1` the local BS dimension is the local entropy. -/
theorem localBSDimension_one (μ : Measure X) (T : X → X) (x : X) :
    localBSDimension μ T (fun _ ↦ 1) x = localEntropy μ T x := by
  have hS : ∀ n : ℕ, birkhoffSum T (fun _ ↦ (1 : ℝ)) n x = n := fun n ↦ by
    simp [birkhoffSum]
  simp only [localBSDimension, localBSDimensionAt, localBSRate, hS, ENNReal.ofReal_natCast,
    localEntropy, localEntropyAt, localEntropyRate]

/-- For the zero potential, a positive time and a measure of mass at most one, the local
pressure rate is the local entropy rate. -/
theorem localPressureRate_zero_eq (μ : Measure X) (hμ : μ univ ≤ 1) (T : X → X) (x : X)
    {n : ℕ} (hn : 1 ≤ n) (ε : ℝ) :
    localPressureRate μ T (fun _ ↦ 0) x n ε = ((localEntropyRate μ T x n ε : ℝ≥0∞) : EReal) := by
  have hS : birkhoffSum T (fun _ ↦ (0 : ℝ)) n x = 0 := by simp [birkhoffSum]
  rw [localPressureRate, localEntropyRate, hS, add_zero]
  split_ifs with h
  · rw [h, infoBits_zero, ENNReal.top_div_of_ne_top (ENNReal.natCast_ne_top n),
      EReal.coe_ennreal_top]
  · have hle : μ (bowenBall T n x ε) ≤ 1 := (measure_mono (subset_univ _)).trans hμ
    have hle' : (μ (bowenBall T n x ε)).toReal ≤ 1 := by
      simpa using ENNReal.toReal_mono ENNReal.one_ne_top hle
    have hnn : 0 ≤ -Real.logb 2 (μ (bowenBall T n x ε)).toReal :=
      neg_nonneg.2 (Real.logb_nonpos one_lt_two ENNReal.toReal_nonneg hle')
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    rw [infoBits_of_ne h, ← ENNReal.ofReal_natCast n, ← ENNReal.ofReal_div_of_pos hn0,
      EReal.coe_ennreal_ofReal, max_eq_left (div_nonneg hnn hn0.le)]

/-- For the zero potential and a measure of total mass at most one, the local pressure is the
local entropy. -/
theorem localPressure_zero (μ : Measure X) (hμ : μ univ ≤ 1) (T : X → X) (x : X) :
    localPressure μ T (fun _ ↦ 0) x =
      (((localEntropy μ T x).1 : EReal), ((localEntropy μ T x).2 : EReal)) := by
  have hrate : ∀ ε : ℝ, ∀ᶠ n in atTop, localPressureRate μ T (fun _ ↦ 0) x n ε =
      ((localEntropyRate μ T x n ε : ℝ≥0∞) : EReal) := fun ε ↦
    (eventually_ge_atTop 1).mono fun n hn ↦ localPressureRate_zero_eq μ hμ T x hn ε
  simp only [localPressure, localPressureAt, localEntropy, localEntropyAt,
    EReal.coe_ennreal_iSup, EReal.coe_ennreal_liminf, EReal.coe_ennreal_limsup]
  exact Prod.ext (iSup_congr fun p ↦ liminf_congr (hrate _))
    (iSup_congr fun p ↦ limsup_congr (hrate _))

/-- Rescaling a measure by a positive finite constant `c` raises the local pressure rate by
at most `|log₂ c| / n`. -/
theorem localPressureRate_smul_le (μ : Measure X) (T : X → X) (φ : X → ℝ) (x : X) (n : ℕ)
    (ε : ℝ) {c : ℝ≥0∞} (hc0 : c ≠ 0) (hc : c ≠ ⊤) :
    localPressureRate (c • μ) T φ x n ε ≤
      localPressureRate μ T φ x n ε + ((|Real.logb 2 c.toReal| / n : ℝ) : EReal) := by
  simp only [localPressureRate, Measure.smul_apply, smul_eq_mul, mul_eq_zero, hc0, false_or]
  split_ifs with h
  · simp
  · rw [← EReal.coe_add, EReal.coe_le_coe_iff]
    rcases eq_or_ne (μ (bowenBall T n x ε)) ⊤ with htop | htop
    · rw [htop, ENNReal.mul_top hc0]
      exact le_add_of_nonneg_right (by positivity)
    · have hcpos : 0 < c.toReal := ENNReal.toReal_pos hc0 hc
      have hpos : 0 < (μ (bowenBall T n x ε)).toReal := ENNReal.toReal_pos h htop
      rw [ENNReal.toReal_mul, Real.logb_mul hcpos.ne' hpos.ne', ← add_div]
      refine div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg n)
      linarith [neg_le_abs (Real.logb 2 c.toReal)]

/-- Rescaling a measure by a positive finite constant does not change its local pressures at
a fixed scale. -/
theorem localPressureAt_smul (μ : Measure X) (T : X → X) (φ : X → ℝ) (x : X) (ε : ℝ)
    {c : ℝ≥0∞} (hc0 : c ≠ 0) (hc : c ≠ ⊤) :
    localPressureAt (c • μ) T φ x ε = localPressureAt μ T φ x ε := by
  have he : Tendsto (fun n : ℕ ↦ |Real.logb 2 c.toReal| / n) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat _
  have h1 := liminf_limsup_le_of_le_add_coe_tendsto_zero he
    (.of_forall fun n ↦ localPressureRate_smul_le μ T φ x n ε hc0 hc)
  have h2 := liminf_limsup_le_of_le_add_coe_tendsto_zero
    (f := fun n ↦ localPressureRate μ T φ x n ε) (g := fun n ↦ localPressureRate (c • μ) T φ x n ε)
    he (.of_forall fun n ↦ by
    have := localPressureRate_smul_le (c • μ) T φ x n ε (ENNReal.inv_ne_zero.2 hc)
      (ENNReal.inv_ne_top.2 hc0)
    rwa [smul_smul, ENNReal.inv_mul_cancel hc0 hc, one_smul, abs_logb_inv_toReal] at this)
  exact Prod.ext (le_antisymm h1.1 h2.1) (le_antisymm h1.2 h2.2)

/-- Rescaling a measure by a positive finite constant does not change its local pressures. -/
theorem localPressure_smul (μ : Measure X) (T : X → X) (φ : X → ℝ) (x : X) {c : ℝ≥0∞}
    (hc0 : c ≠ 0) (hc : c ≠ ⊤) : localPressure (c • μ) T φ x = localPressure μ T φ x := by
  simp only [localPressure, localPressureAt_smul μ T φ x _ hc0 hc]

/-- Rescaling a measure by a positive finite constant `c` raises the local BS rate by at most
`|log₂ c| / S_n u(x)`. -/
theorem localBSRate_smul_le (μ : Measure X) (T : X → X) (u : X → ℝ) (x : X) (n : ℕ) (ε : ℝ)
    {c : ℝ≥0∞} (hc0 : c ≠ 0) (hc : c ≠ ⊤) :
    localBSRate (c • μ) T u x n ε ≤ localBSRate μ T u x n ε +
      ENNReal.ofReal |Real.logb 2 c.toReal| / ENNReal.ofReal (birkhoffSum T u n x) := by
  simp only [localBSRate, Measure.smul_apply, smul_eq_mul, ← ENNReal.add_div]
  exact ENNReal.div_le_div_right (infoBits_mul_le hc0 hc _) _

/-- Rescaling a measure by a positive finite constant does not change its local BS dimensions
at a fixed scale, at a point of positive lower Birkhoff average. -/
theorem localBSDimensionAt_smul (μ : Measure X) (T : X → X) (u : X → ℝ) {x : X}
    (hx : 0 < lowerBirkhoffAverage T u x) (ε : ℝ) {c : ℝ≥0∞} (hc0 : c ≠ 0) (hc : c ≠ ⊤) :
    localBSDimensionAt (c • μ) T u x ε = localBSDimensionAt μ T u x ε := by
  set C := ENNReal.ofReal |Real.logb 2 c.toReal|
  have hd : Tendsto (fun n ↦ C / ENNReal.ofReal (birkhoffSum T u n x)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun n ↦ ENNReal.ofReal (birkhoffSum T u n x)) atTop (𝓝 ⊤) :=
      ENNReal.tendsto_ofReal_atTop.comp (tendsto_birkhoffSum_atTop hx)
    simpa using ENNReal.Tendsto.const_div (a := C) h1 (Or.inr ENNReal.ofReal_ne_top)
  have h1 : ∀ n : ℕ, localBSRate (c • μ) T u x n ε ≤ localBSRate μ T u x n ε +
      C / ENNReal.ofReal (birkhoffSum T u n x) := fun n ↦
    localBSRate_smul_le μ T u x n ε hc0 hc
  have h2 : ∀ n : ℕ, localBSRate μ T u x n ε ≤ localBSRate (c • μ) T u x n ε +
      C / ENNReal.ofReal (birkhoffSum T u n x) := fun n ↦ by
    have := localBSRate_smul_le (c • μ) T u x n ε (ENNReal.inv_ne_zero.2 hc)
      (ENNReal.inv_ne_top.2 hc0)
    rwa [smul_smul, ENNReal.inv_mul_cancel hc0 hc, one_smul, abs_logb_inv_toReal] at this
  exact Prod.ext
    (le_antisymm (liminf_le_liminf_of_le_add_tendsto_zero (.of_forall h1) hd)
      (liminf_le_liminf_of_le_add_tendsto_zero (.of_forall h2) hd))
    (le_antisymm (limsup_le_limsup_of_le_add_tendsto_zero (.of_forall h1) hd)
      (limsup_le_limsup_of_le_add_tendsto_zero (.of_forall h2) hd))

/-- Rescaling a measure by a positive finite constant does not change its local BS dimensions
at a point of positive lower Birkhoff average. -/
theorem localBSDimension_smul (μ : Measure X) (T : X → X) (u : X → ℝ) {x : X}
    (hx : 0 < lowerBirkhoffAverage T u x) {c : ℝ≥0∞} (hc0 : c ≠ 0) (hc : c ≠ ⊤) :
    localBSDimension (c • μ) T u x = localBSDimension μ T u x := by
  simp only [localBSDimension, localBSDimensionAt_smul μ T u hx _ hc0 hc]

/-! ### Weights at the point (Lemma 8.2) -/

/-- The rate `(K_n^A(x, T, ε) + S_n φ(x)) / n`. Blueprint node `meas:weights`. -/
noncomputable def orbitPressureRate (P : Presentation X) (T : X → X) (φ : X → ℝ) (A : Set ℕ)
    (x : X) (n : ℕ) (ε : ℝ) : EReal :=
  (((orbitComplexityNat P T A x n ε + birkhoffSum T φ n x) / n : ℝ) : EReal)

/-- The rate `K_n^A(x, T, ε) / S_n u(x)`. Blueprint node `meas:weights`. -/
noncomputable def orbitBSRate (P : Presentation X) (T : X → X) (u : X → ℝ) (A : Set ℕ)
    (x : X) (n : ℕ) (ε : ℝ) : ℝ≥0∞ :=
  (orbitComplexityNat P T A x n ε : ℝ≥0∞) / ENNReal.ofReal (birkhoffSum T u n x)

omit [MeasurableSpace X] in
/-- Lemma 8.2 (weights at the point): if `φ` oscillates by at most `ω` on sets of diameter
less than `ε`, then `min_{x_i ∈ B_n(x, T, ε)} (K^A(i) + S_n φ(x_i))` differs from
`K_n^A(x, T, ε) + S_n φ(x)` by at most `n ω`. Blueprint node `meas:weights`. -/
theorem abs_finiteScalePressureCost_sub_le (P : Presentation X) (T : X → X) (hT : Continuous T)
    (φ : X → ℝ) (A : Set ℕ) (x : X) {n : ℕ} (hn : 1 ≤ n) {ε : ℝ} (hε : 0 < ε) {ω : ℝ}
    (hω : ∀ y z, dist y z < ε → |φ y - φ z| ≤ ω) :
    ∃ c : ℝ, finiteScalePressureCost P T φ A x n ε = (c : EReal) ∧
      |c - (orbitComplexityNat P T A x n ε + birkhoffSum T φ n x)| ≤ n * ω := by
  obtain ⟨i, hi, hcost⟩ := finite_scale_min_attained P T hT φ A x n hn ε hε ω hω
  obtain ⟨j, hj, heq⟩ := exists_orbitComplexityNat_eq P T hT A x hn hε
  refine ⟨_, hcost, abs_le.2 ⟨?_, ?_⟩⟩
  · have hK : (orbitComplexityNat P T A x n ε : ℝ) ≤ oracleNatComplexity A i := by
      exact_mod_cast orbitComplexityNat_le_of_mem P T A hi
    linarith [(abs_le.1 (abs_birkhoffSum_sub_le_of_oscillation T φ hω hi)).1]
  · have hle : finiteScalePressureCost P T φ A x n ε ≤
        ((oracleNatComplexity A j + birkhoffSum T φ n (P.ι j) : ℝ) : EReal) := iInf₂_le j hj
    rw [hcost, EReal.coe_le_coe_iff] at hle
    rw [heq]
    linarith [(abs_le.1 (abs_birkhoffSum_sub_le_of_oscillation T φ hω hj)).2]

omit [MeasurableSpace X] in
/-- Lemma 8.2 for the normalized rates, upper bound: the pressure rate is at most the rate
of `K_n^A(x, T, ε) + S_n φ(x)` plus the oscillation `ω`. -/
theorem finiteScalePressureRate_le_orbitPressureRate_add (P : Presentation X) (T : X → X)
    (hT : Continuous T) (φ : X → ℝ) (A : Set ℕ) (x : X) {n : ℕ} (hn : 1 ≤ n) {ε : ℝ}
    (hε : 0 < ε) {ω : ℝ} (hω : ∀ y z, dist y z < ε → |φ y - φ z| ≤ ω) :
    finiteScalePressureRate P T φ A x n ε ≤ orbitPressureRate P T φ A x n ε + (ω : EReal) := by
  obtain ⟨j, hj, heq⟩ := exists_orbitComplexityNat_eq P T hT A x hn hε
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  simp only [finiteScalePressureRate, show n ≠ 0 by omega, ↓reduceIte]
  rw [orbitPressureRate, ← EReal.coe_add]
  refine (iInf₂_le j hj).trans (EReal.coe_le_coe_iff.2 ?_)
  rw [div_le_iff₀ hn0, add_mul, div_mul_cancel₀ _ hn0.ne', heq]
  linarith [(abs_le.1 (abs_birkhoffSum_sub_le_of_oscillation T φ hω hj)).2]

omit [MeasurableSpace X] in
/-- Lemma 8.2 for the normalized rates, lower bound: the rate of
`K_n^A(x, T, ε) + S_n φ(x)` is at most the pressure rate plus the oscillation `ω`. -/
theorem orbitPressureRate_le_finiteScalePressureRate_add (P : Presentation X) (T : X → X)
    (φ : X → ℝ) (A : Set ℕ) (x : X) {n : ℕ} (hn : 1 ≤ n) {ε : ℝ} {ω : ℝ}
    (hω : ∀ y z, dist y z < ε → |φ y - φ z| ≤ ω) :
    orbitPressureRate P T φ A x n ε ≤ finiteScalePressureRate P T φ A x n ε + (ω : EReal) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have key : ((((orbitComplexityNat P T A x n ε + birkhoffSum T φ n x) / n - ω : ℝ)) : EReal) ≤
      finiteScalePressureRate P T φ A x n ε := by
    simp only [finiteScalePressureRate, show n ≠ 0 by omega, ↓reduceIte]
    refine le_iInf₂ fun i hi ↦ EReal.coe_le_coe_iff.2 ?_
    have hK : (orbitComplexityNat P T A x n ε : ℝ) ≤ oracleNatComplexity A i := by
      exact_mod_cast orbitComplexityNat_le_of_mem P T A hi
    rw [sub_le_iff_le_add, div_le_iff₀ hn0, add_mul, div_mul_cancel₀ _ hn0.ne']
    linarith [(abs_le.1 (abs_birkhoffSum_sub_le_of_oscillation T φ hω hi)).1]
  calc orbitPressureRate P T φ A x n ε
      = ((((orbitComplexityNat P T A x n ε + birkhoffSum T φ n x) / n - ω : ℝ)) : EReal) +
          (ω : EReal) := by rw [orbitPressureRate, ← EReal.coe_add, sub_add_cancel]
    _ ≤ _ := add_le_add key le_rfl

omit [MeasurableSpace X] in
/-- The finite-scale pressure rates increase as the dyadic scale shrinks. -/
theorem monotone_finiteScalePressureRate_dyadicRadius (P : Presentation X) (T : X → X)
    (φ : X → ℝ) (A : Set ℕ) (x : X) (n : ℕ) :
    Monotone fun p ↦ finiteScalePressureRate P T φ A x n (dyadicRadius p) := by
  intro p q hpq
  simp only [finiteScalePressureRate]
  split_ifs
  · exact le_rfl
  · exact iInf_mono fun i ↦ iInf_mono' fun hi ↦
      ⟨bowenBall_subset_of_le T n x (dyadicRadius_antitone hpq) hi, le_rfl⟩

omit [MeasurableSpace X] in
/-- The orbit pressure rates increase as the radius shrinks, at positive times. -/
theorem orbitPressureRate_antitone_radius (P : Presentation X) (T : X → X) (hT : Continuous T)
    (φ : X → ℝ) (A : Set ℕ) (x : X) {n : ℕ} (hn : 1 ≤ n) {r r' : ℝ} (hr : 0 < r)
    (h : r ≤ r') : orbitPressureRate P T φ A x n r' ≤ orbitPressureRate P T φ A x n r := by
  have hK : (orbitComplexityNat P T A x n r' : ℝ) ≤ orbitComplexityNat P T A x n r := by
    exact_mod_cast orbitComplexityNat_le_of_radius_le P T hT A x hn hr h
  exact EReal.coe_le_coe_iff.2 (div_le_div_of_nonneg_right (by linarith) (Nat.cast_nonneg n))

omit [MeasurableSpace X] in
/-- The orbit BS rates increase as the radius shrinks, at positive times. -/
theorem orbitBSRate_antitone_radius (P : Presentation X) (T : X → X) (hT : Continuous T)
    (u : X → ℝ) (A : Set ℕ) (x : X) {n : ℕ} (hn : 1 ≤ n) {r r' : ℝ} (hr : 0 < r)
    (h : r ≤ r') : orbitBSRate P T u A x n r' ≤ orbitBSRate P T u A x n r :=
  ENNReal.div_le_div_right
    (Nat.cast_le.2 (orbitComplexityNat_le_of_radius_le P T hT A x hn hr h)) _

omit [MeasurableSpace X] in
/-- Lemma 8.2, consequence for the pressure: for a uniformly continuous potential the pointwise
pressure is the limit as `ε → 0` of the rates of `K_n^A(x, T, ε) + S_n φ(x)`.
Blueprint node `meas:weights`. -/
theorem pointwisePressure_eq_orbitPressureRate (P : Presentation X) (T : X → X)
    (hT : Continuous T) (φ : X → ℝ) (hφ : UniformContinuous φ) (A : Set ℕ) (x : X) :
    pointwisePressure P T φ A x =
      (⨆ p : ℕ, liminf (fun n ↦ orbitPressureRate P T φ A x n (dyadicRadius p)) atTop,
        ⨆ p : ℕ, limsup (fun n ↦ orbitPressureRate P T φ A x n (dyadicRadius p)) atTop) := by
  obtain ⟨ω, -, hω0, p₀, hω⟩ := small_scale_oscillation φ hφ
  have hω' : ∀ p ≥ p₀, ∀ y z, dist y z < dyadicRadius p → |φ y - φ z| ≤ ω p :=
    fun p hp y z h ↦ hω p hp y z (h.trans (by linarith [dyadicRadius_pos p]))
  set F : ℕ → ℕ → EReal := fun p n ↦ finiteScalePressureRate P T φ A x n (dyadicRadius p)
  set G : ℕ → ℕ → EReal := fun p n ↦ orbitPressureRate P T φ A x n (dyadicRadius p)
  have hFG : ∀ p ≥ p₀, ∀ᶠ n in atTop, F p n ≤ G p n + ((fun _ : ℕ ↦ ω p) n : EReal) :=
    fun p hp ↦ (eventually_ge_atTop 1).mono fun n hn ↦
      finiteScalePressureRate_le_orbitPressureRate_add P T hT φ A x hn (dyadicRadius_pos p)
        (hω' p hp)
  have hGF : ∀ p ≥ p₀, ∀ᶠ n in atTop, G p n ≤ F p n + ((fun _ : ℕ ↦ ω p) n : EReal) :=
    fun p hp ↦ (eventually_ge_atTop 1).mono fun n hn ↦
      orbitPressureRate_le_finiteScalePressureRate_add P T φ A x hn (hω' p hp)
  have hFm : ∀ n, Monotone fun p ↦ F p n := fun n ↦
    monotone_finiteScalePressureRate_dyadicRadius P T φ A x n
  have hGm : ∀ p q, p ≤ q → ∀ᶠ n in atTop, G p n ≤ G q n := fun p q hpq ↦
    (eventually_ge_atTop 1).mono fun n hn ↦ orbitPressureRate_antitone_radius P T hT φ A x hn
      (dyadicRadius_pos q) (dyadicRadius_antitone hpq)
  have hc : ∀ p, Tendsto (fun _ : ℕ ↦ ω p) atTop (𝓝 (ω p)) := fun _ ↦ tendsto_const_nhds
  refine Prod.ext (le_antisymm ?_ ?_) (le_antisymm ?_ ?_)
  · refine iSup_le_of_monotone_of_eventually_le_add_coe _
      (fun p q hpq ↦ liminf_le_liminf (.of_forall fun n ↦ hFm n hpq)) ω hω0 _ ?_
    filter_upwards [eventually_ge_atTop p₀] with p hp
    exact (liminf_le_liminf_add_coe_of_eventually_le _ _ _ _ (hc p) (hFG p hp)).trans
      (add_le_add (le_iSup (fun q ↦ liminf (G q) atTop) p) le_rfl)
  · refine iSup_le_of_monotone_of_eventually_le_add_coe _
      (fun p q hpq ↦ liminf_le_liminf (hGm p q hpq)) ω hω0 _ ?_
    filter_upwards [eventually_ge_atTop p₀] with p hp
    exact (liminf_le_liminf_add_coe_of_eventually_le _ _ _ _ (hc p) (hGF p hp)).trans
      (add_le_add (le_iSup (fun q ↦ liminf (F q) atTop) p) le_rfl)
  · refine iSup_le_of_monotone_of_eventually_le_add_coe _
      (fun p q hpq ↦ limsup_le_limsup (.of_forall fun n ↦ hFm n hpq)) ω hω0 _ ?_
    filter_upwards [eventually_ge_atTop p₀] with p hp
    exact (limsup_le_limsup_add_coe_of_eventually_le _ _ _ _ (hc p) (hFG p hp)).trans
      (add_le_add (le_iSup (fun q ↦ limsup (G q) atTop) p) le_rfl)
  · refine iSup_le_of_monotone_of_eventually_le_add_coe _
      (fun p q hpq ↦ limsup_le_limsup (hGm p q hpq)) ω hω0 _ ?_
    filter_upwards [eventually_ge_atTop p₀] with p hp
    exact (limsup_le_limsup_add_coe_of_eventually_le _ _ _ _ (hc p) (hGF p hp)).trans
      (add_le_add (le_iSup (fun q ↦ limsup (F q) atTop) p) le_rfl)

omit [MeasurableSpace X] in
/-- Lemma 8.2, consequence for the BS dimension: for a uniformly continuous potential and a
point of positive lower Birkhoff average, the pointwise BS dimension is the limit as `ε → 0`
of the rates of `K_n^A(x, T, ε) / S_n u(x)`. Blueprint node `meas:weights`. -/
theorem pointwiseBSDimension_eq_orbitBSRate (P : Presentation X) (T : X → X)
    (hT : Continuous T) (u : X → ℝ) (hu : UniformContinuous u) (A : Set ℕ) {x : X}
    (hx : 0 < lowerBirkhoffAverage T u x) :
    pointwiseBSDimension P T u A x =
      (⨆ p : ℕ, liminf (fun n ↦ orbitBSRate P T u A x n (dyadicRadius p)) atTop,
        ⨆ p : ℕ, limsup (fun n ↦ orbitBSRate P T u A x n (dyadicRadius p)) atTop) := by
  obtain ⟨ω, hωpos, hω0, p₀, hω⟩ := small_scale_oscillation u hu
  obtain ⟨δ, hδ, hev⟩ := exists_pos_eventually_mul_le_birkhoffSum hx
  have hω' : ∀ p ≥ p₀, ∀ y z, dist y z < dyadicRadius p → |u y - u z| ≤ ω p :=
    fun p hp y z h ↦ hω p hp y z (h.trans (by linarith [dyadicRadius_pos p]))
  set F : ℕ → ℕ → ℝ≥0∞ := fun p n ↦ finiteScaleBSCost P T u A x n (dyadicRadius p)
  set G : ℕ → ℕ → ℝ≥0∞ := fun p n ↦ orbitBSRate P T u A x n (dyadicRadius p)
  set a : ℕ → ℝ≥0∞ := fun p ↦ ENNReal.ofReal (δ / (δ - ω p))
  set b : ℕ → ℝ≥0∞ := fun p ↦ ENNReal.ofReal ((δ + ω p) / δ)
  have ha : Tendsto a atTop (𝓝 1) := by
    have h : Tendsto (fun p ↦ δ / (δ - ω p)) atTop (𝓝 (δ / (δ - 0))) :=
      tendsto_const_nhds.div (tendsto_const_nhds.sub hω0) (by simpa using hδ.ne')
    rw [sub_zero, div_self hδ.ne'] at h
    simpa [a] using ENNReal.tendsto_ofReal h
  have hb : Tendsto b atTop (𝓝 1) := by
    have h : Tendsto (fun p ↦ (δ + ω p) / δ) atTop (𝓝 ((δ + 0) / δ)) :=
      (tendsto_const_nhds.add hω0).div_const δ
    rw [add_zero, div_self hδ.ne'] at h
    simpa [b] using ENNReal.tendsto_ofReal h
  have hgood : ∀ᶠ p in atTop, p₀ ≤ p ∧ ω p < δ :=
    (eventually_ge_atTop p₀).and (hω0.eventually (gt_mem_nhds hδ))
  have hpt : ∀ᶠ n : ℕ in atTop, 1 ≤ n ∧ δ * n ≤ birkhoffSum T u n x :=
    (eventually_ge_atTop 1).and hev
  have hFG : ∀ p, p₀ ≤ p → ω p < δ → ∀ᶠ n in atTop, F p n ≤ G p n * a p := by
    intro p hp hlt
    filter_upwards [hpt] with n ⟨hn, hδn⟩
    obtain ⟨j, hj, heq⟩ := exists_orbitComplexityNat_eq P T hT A x hn (dyadicRadius_pos p)
    have hosc := abs_le.1 (abs_birkhoffSum_sub_le_of_oscillation T u (hω' p hp) hj)
    have hSx : 0 < birkhoffSum T u n x :=
      lt_of_lt_of_le (mul_pos hδ (by exact_mod_cast hn)) hδn
    have h1 : δ * n * ω p ≤ birkhoffSum T u n x * ω p :=
      mul_le_mul_of_nonneg_right hδn (hωpos p).le
    have hSj : birkhoffSum T u n x * (δ - ω p) / δ ≤ birkhoffSum T u n (P.ι j) := by
      rw [div_le_iff₀ hδ]
      nlinarith
    have hpos' : 0 < birkhoffSum T u n x * (δ - ω p) / δ :=
      div_pos (mul_pos hSx (sub_pos.2 hlt)) hδ
    calc F p n ≤ (oracleNatComplexity A j : ℝ≥0∞) /
          ENNReal.ofReal (birkhoffSum T u n (P.ι j)) :=
          finiteScaleBSCost_le_div P T u A (by omega) hj (hpos'.trans_le hSj)
      _ = ENNReal.ofReal ((orbitComplexityNat P T A x n (dyadicRadius p) : ℝ) /
          birkhoffSum T u n (P.ι j)) := by
          rw [heq, natCast_div_ofReal_eq _ (hpos'.trans_le hSj)]
      _ ≤ ENNReal.ofReal ((orbitComplexityNat P T A x n (dyadicRadius p) : ℝ) /
          birkhoffSum T u n x * (δ / (δ - ω p))) := by
          refine ENNReal.ofReal_le_ofReal ?_
          have he : (orbitComplexityNat P T A x n (dyadicRadius p) : ℝ) /
              birkhoffSum T u n x * (δ / (δ - ω p)) =
              (orbitComplexityNat P T A x n (dyadicRadius p) : ℝ) /
                (birkhoffSum T u n x * (δ - ω p) / δ) := by
            field_simp [(sub_pos.2 hlt).ne']
          rw [he]
          exact div_le_div_of_nonneg_left (Nat.cast_nonneg _) hpos' hSj
      _ = G p n * a p := by
          rw [ENNReal.ofReal_mul (div_nonneg (Nat.cast_nonneg _) hSx.le)]
          simp only [G, a, orbitBSRate, natCast_div_ofReal_eq _ hSx]
  have hGF : ∀ p, p₀ ≤ p → ∀ᶠ n in atTop, G p n ≤ F p n * b p := by
    intro p hp
    filter_upwards [hpt] with n ⟨hn, hδn⟩
    have hSx : 0 < birkhoffSum T u n x :=
      lt_of_lt_of_le (mul_pos hδ (by exact_mod_cast hn)) hδn
    have hbpos : 0 < (δ + ω p) / δ := div_pos (by linarith [hωpos p]) hδ
    have h1 : δ * n * ω p ≤ birkhoffSum T u n x * ω p :=
      mul_le_mul_of_nonneg_right hδn (hωpos p).le
    rw [← ENNReal.div_le_iff (ENNReal.ofReal_pos.2 hbpos).ne' ENNReal.ofReal_ne_top]
    simp only [F, finiteScaleBSCost, show n ≠ 0 by omega, ↓reduceIte]
    refine le_iInf fun i ↦ le_iInf fun hi ↦ le_iInf fun hpos ↦ ?_
    have hK : (orbitComplexityNat P T A x n (dyadicRadius p) : ℝ) ≤ oracleNatComplexity A i := by
      exact_mod_cast orbitComplexityNat_le_of_mem P T A hi
    have hosc := abs_le.1 (abs_birkhoffSum_sub_le_of_oscillation T u (hω' p hp) hi)
    have hSi : birkhoffSum T u n (P.ι i) ≤ birkhoffSum T u n x * (δ + ω p) / δ := by
      rw [le_div_iff₀ hδ]
      nlinarith
    simp only [G, orbitBSRate]
    rw [natCast_div_ofReal_eq _ hSx, natCast_div_ofReal_eq _ hpos,
      ← ENNReal.ofReal_div_of_pos hbpos]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [div_div, show birkhoffSum T u n x * ((δ + ω p) / δ) =
      birkhoffSum T u n x * (δ + ω p) / δ by ring]
    exact div_le_div₀ (Nat.cast_nonneg _) hK hpos hSi
  have hFm : Monotone fun p ↦ liminf (F p) atTop := fun p q hpq ↦ liminf_le_liminf
    (.of_forall fun n ↦ pointwiseBSDimension_antitone_radius P T u A x n
      (dyadicRadius_antitone hpq))
  have hFm' : Monotone fun p ↦ limsup (F p) atTop := fun p q hpq ↦ limsup_le_limsup
    (.of_forall fun n ↦ pointwiseBSDimension_antitone_radius P T u A x n
      (dyadicRadius_antitone hpq))
  have hGm : ∀ p q, p ≤ q → ∀ᶠ n in atTop, G p n ≤ G q n := fun p q hpq ↦
    (eventually_ge_atTop 1).mono fun n hn ↦ orbitBSRate_antitone_radius P T hT u A x hn
      (dyadicRadius_pos q) (dyadicRadius_antitone hpq)
  have hGm₁ : Monotone fun p ↦ liminf (G p) atTop := fun p q hpq ↦ liminf_le_liminf (hGm p q hpq)
  have hGm₂ : Monotone fun p ↦ limsup (G p) atTop := fun p q hpq ↦ limsup_le_limsup (hGm p q hpq)
  have hFG' : ∀ᶠ p in atTop, liminf (F p) atTop ≤ liminf (G p) atTop * a p ∧
      limsup (F p) atTop ≤ limsup (G p) atTop * a p := hgood.mono fun p ⟨hp, hlt⟩ ↦
    liminf_limsup_le_mul_of_eventually_le ENNReal.ofReal_ne_top (hFG p hp hlt)
  have hGF' : ∀ᶠ p in atTop, liminf (G p) atTop ≤ liminf (F p) atTop * b p ∧
      limsup (G p) atTop ≤ limsup (F p) atTop * b p := hgood.mono fun p ⟨hp, _⟩ ↦
    liminf_limsup_le_mul_of_eventually_le ENNReal.ofReal_ne_top (hGF p hp)
  exact Prod.ext
    (le_antisymm (iSup_le_iSup_of_eventually_le_mul hFm ha (hFG'.mono fun _ h ↦ h.1))
      (iSup_le_iSup_of_eventually_le_mul hGm₁ hb (hGF'.mono fun _ h ↦ h.1)))
    (le_antisymm (iSup_le_iSup_of_eventually_le_mul hFm' ha (hFG'.mono fun _ h ↦ h.2))
      (iSup_le_iSup_of_eventually_le_mul hGm₂ hb (hGF'.mono fun _ h ↦ h.2)))

end Kolmogorov.PointToSet
