/-
Copyright (c) 2026 Emma Dinowitz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emma Dinowitz
-/
import KolmogorovMathlib.PointToSet.Measure.InformationRate
import KolmogorovMathlib.PointToSet.SymbolicSet
import KolmogorovMathlib.AlgorithmicRandomness.ComputableMeasure
import Mathlib.MeasureTheory.Measure.Dirac.Basic

/-!
# Local entropies on a one-sided shift

On the sequence space `ℕ → α` with a first-difference metric `dist x y = β ^ firstDiff x y`
(`0 < β < 1`) and the left shift `σ`, the Bowen ball `B_n(x, σ, β^k)` is the cylinder
`[x↾(n + k)]`. Hence for every Borel measure `μ`

`h̲_μ(σ, x) = liminf_n -(1/n) log₂ μ[x↾n]`, `h̄_μ(σ, x) = limsup_n -(1/n) log₂ μ[x↾n]`,

and the information rates are the growth rates of `∫ -log₂ μ[x↾n] dμ(x)`
(E. Dinowitz, *Entropy of non-invariant measures and orbit complexity of random points*, §5).

* `shiftMap`: the left shift.
* `bowenBall_shiftMap_eq_cylinder`: `B_n(x, σ, β^k) = [x↾(n + k)]` for `n ≥ 1`.
* `localEntropy_shiftMap`, `informationRate_shiftMap`: the cylinder formulas.
* `localEntropy_dirac`: a point mass has local entropies `(0, 0)` at its atom, on any space.
* `map_localEntropy_compProd_id` (Example 7.4(1)): for the identity kernel `ω ↦ δ_ω` the law of
  `Φ_{δ_ω}(x)` under `μ ⊗ δ` is `δ_{(0, 0)}`, whatever `μ`.

On Cantor space `ℕ → Bool` with the metric `cantorMetricSpace`
(`dist x y = (1/2) ^ firstDiff x y`, inducing the product topology and uniformity; a local
instance, not a global one) and the fair-coin measure `uniformMeasure`:

* `uniformMeasure_cylinder`: `μ[x↾n] = 2^{-n}`;
* `localEntropy_uniformMeasure_shiftMap`, `entropyLaw_uniformMeasure_shiftMap`: every point has
  local entropies `(1, 1)`, so `Λ_μ = δ_{(1, 1)}`;
* `map_localEntropy_compProd_id_ne_entropyLaw`: the law of `Φ_{δ_x}(x)` under `μ ⊗ δ` differs
  from `Λ_μ` (failure of integral affinity for point masses, Example 7.4(1)).

Blueprint node `meas:shift`.
-/

namespace Kolmogorov.PointToSet

open Filter Set MeasureTheory
open scoped Topology ENNReal ProbabilityTheory

/-- The left shift on a sequence space. Blueprint node `meas:shift`. -/
def shiftMap {α : Type*} (x : ℕ → α) : ℕ → α := fun j ↦ x (j + 1)

/-- A point mass has local entropies `(0, 0)` at its atom (Example 7.4(1)).
Blueprint node `meas:shift`. -/
theorem localEntropy_dirac {X : Type*} [MetricSpace X] [MeasurableSpace X] (T : X → X)
    (x : X) : localEntropy (Measure.dirac x) T x = (0, 0) := by
  have h : ∀ ε : ℝ, 0 < ε → (fun n : ℕ ↦ localEntropyRate (Measure.dirac x) T x n ε) =
      fun _ ↦ 0 := fun ε hε ↦ funext fun n ↦ by
    rw [localEntropyRate, Measure.dirac_apply_of_mem (self_mem_bowenBall T n x ε hε),
      infoBits_of_ne one_ne_zero]
    simp
  simp only [localEntropy, localEntropyAt, h _ (dyadicRadius_pos _), liminf_const,
    limsup_const, iSup_const]

/-- Shifting the index by `k` while keeping the denominator `n` does not change the lower and
upper growth rates: `a (n + k) / (n + k) ≤ a (n + k) / n ≤ (1 + 1/m) a (n + k) / (n + k)` for
`n ≥ k m + 1`. -/
private lemma rate_add (a : ℕ → ℝ≥0∞) (k : ℕ) :
    liminf (fun n : ℕ ↦ a (n + k) / n) atTop = liminf (fun n : ℕ ↦ a n / n) atTop ∧
      limsup (fun n : ℕ ↦ a (n + k) / n) atTop = limsup (fun n : ℕ ↦ a n / n) atTop := by
  have hl := liminf_nat_add (fun n : ℕ ↦ a n / n) k
  have hu := limsup_nat_add (fun n : ℕ ↦ a n / n) k
  rw [← hl, ← hu]
  set v : ℕ → ℝ≥0∞ := fun n ↦ a (n + k) / ((n + k : ℕ) : ℝ≥0∞) with hv
  set w : ℕ → ℝ≥0∞ := fun n ↦ a (n + k) / (n : ℝ≥0∞) with hw
  have hvw : ∀ n, v n ≤ w n := fun n ↦
    ENNReal.div_le_div_left (by exact_mod_cast Nat.le_add_right n k) _
  -- for `m ≥ 1`, eventually `w n ≤ (1 + m⁻¹) * v n`
  have hwv : ∀ m : ℕ, 1 ≤ m → ∀ᶠ n in atTop, w n ≤ (1 + (m : ℝ≥0∞)⁻¹) * v n := by
    intro m hm
    filter_upwards [eventually_ge_atTop (k * m + 1)] with n hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (Nat.succ_pos _).trans_le hn
    have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
    have hnk : (0 : ℝ) < ((n + k : ℕ) : ℝ) := by push_cast; positivity
    have hinv : (n : ℝ≥0∞)⁻¹ ≤ (1 + (m : ℝ≥0∞)⁻¹) * ((n + k : ℕ) : ℝ≥0∞)⁻¹ := by
      rw [← ENNReal.ofReal_natCast n, ← ENNReal.ofReal_natCast m,
        ← ENNReal.ofReal_natCast (n + k), ← ENNReal.ofReal_inv_of_pos hn0,
        ← ENNReal.ofReal_inv_of_pos hm0, ← ENNReal.ofReal_inv_of_pos hnk,
        ← ENNReal.ofReal_one, ← ENNReal.ofReal_add zero_le_one (by positivity),
        ← ENNReal.ofReal_mul (by positivity)]
      refine ENNReal.ofReal_le_ofReal ?_
      have hkm : (k : ℝ) * m ≤ n := by exact_mod_cast (Nat.le_succ _).trans hn
      push_cast
      rw [← sub_nonneg]
      have hnk' : (0 : ℝ) < n + k := by positivity
      have : (1 + (m : ℝ)⁻¹) * ((n : ℝ) + k)⁻¹ - (n : ℝ)⁻¹ = (n - k * m) / (m * n * (n + k)) := by
        field_simp
        ring
      rw [this]
      exact div_nonneg (by linarith) (by positivity)
    simp only [hw, hv, div_eq_mul_inv]
    calc a (n + k) * (n : ℝ≥0∞)⁻¹ ≤ a (n + k) * ((1 + (m : ℝ≥0∞)⁻¹) * ((n + k : ℕ) : ℝ≥0∞)⁻¹) :=
          by gcongr
      _ = _ := by ring
  have hlim : Tendsto (fun m : ℕ ↦ 1 + (m : ℝ≥0∞)⁻¹) atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.add ENNReal.tendsto_inv_nat_nhds_zero
  have hc : ∀ m : ℕ, 1 ≤ m → (1 + (m : ℝ≥0∞)⁻¹) ≠ ⊤ := fun m hm ↦
    ENNReal.add_ne_top.2 ⟨ENNReal.one_ne_top, ENNReal.inv_ne_top.2 (by exact_mod_cast
      (Nat.one_pos.trans_le hm).ne')⟩
  constructor
  · refine le_antisymm ?_ (liminf_le_liminf (.of_forall hvw))
    have hT := ENNReal.Tendsto.mul_const hlim (b := liminf v atTop) (Or.inl one_ne_zero)
    rw [one_mul] at hT
    refine ge_of_tendsto hT ((eventually_ge_atTop 1).mono fun m hm ↦ ?_)
    rw [← ENNReal.liminf_const_mul_of_ne_top (hc m hm)]
    exact liminf_le_liminf (hwv m hm)
  · refine le_antisymm ?_ (limsup_le_limsup (.of_forall hvw))
    have hT := ENNReal.Tendsto.mul_const hlim (b := limsup v atTop) (Or.inl one_ne_zero)
    rw [one_mul] at hT
    refine ge_of_tendsto hT ((eventually_ge_atTop 1).mono fun m hm ↦ ?_)
    rw [← ENNReal.limsup_const_mul_of_ne_top (hc m hm)]
    exact limsup_le_limsup (hwv m hm)

section firstDiff

variable {α : Type*} [MetricSpace (ℕ → α)] {β : ℝ}

omit [MetricSpace (ℕ → α)] in
/-- The iterates of the shift: `σ^j x = (x (i + j))_i`. -/
private lemma iterate_shiftMap (x : ℕ → α) (j : ℕ) :
    shiftMap^[j] x = fun i ↦ x (i + j) := by
  induction j generalizing x with
  | zero => rfl
  | succ j ih =>
    rw [Function.iterate_succ_apply, ih]
    funext i
    simp only [shiftMap]
    ring_nf

/-- For a first-difference metric, `d(x, y) < β^k` iff `x` and `y` agree up to the index `k`. -/
private lemma dist_lt_pow_iff (hβ : 0 < β) (hβ₁ : β < 1)
    (hd : ∀ x y : ℕ → α, x ≠ y → dist x y = β ^ PiNat.firstDiff x y) {x y : ℕ → α} {k : ℕ} :
    dist x y < β ^ k ↔ ∀ i ≤ k, x i = y i := by
  constructor
  · intro h i hi
    by_cases hxy : x = y
    · rw [hxy]
    rw [hd x y hxy] at h
    refine PiNat.apply_eq_of_lt_firstDiff (lt_of_not_ge fun hle ↦ ?_)
    exact h.not_ge (pow_le_pow_of_le_one hβ.le hβ₁.le (hle.trans hi))
  · intro h
    by_cases hxy : x = y
    · rw [hxy, dist_self]
      positivity
    rw [hd x y hxy]
    have hk : k + 1 ≤ PiNat.firstDiff x y := by
      by_contra hlt
      exact PiNat.apply_firstDiff_ne hxy (h _ (by omega))
    calc β ^ PiNat.firstDiff x y ≤ β ^ (k + 1) := pow_le_pow_of_le_one hβ.le hβ₁.le hk
      _ < β ^ k := pow_lt_pow_right_of_lt_one₀ hβ hβ₁ (Nat.lt_succ_self k)

/-- The left shift is continuous for a first-difference metric. -/
theorem continuous_shiftMap (hβ : 0 < β) (hβ₁ : β < 1)
    (hd : ∀ x y : ℕ → α, x ≠ y → dist x y = β ^ PiNat.firstDiff x y) :
    Continuous (shiftMap : (ℕ → α) → ℕ → α) := by
  refine Metric.continuous_iff.2 fun x ε hε ↦ ?_
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one hε hβ₁
  refine ⟨β ^ (k + 1), by positivity, fun y hy ↦ ?_⟩
  rw [dist_comm] at hy ⊢
  have h := (dist_lt_pow_iff hβ hβ₁ hd).1 hy
  exact ((dist_lt_pow_iff hβ hβ₁ hd).2 fun i hi ↦ h (i + 1) (by omega)).trans hk

/-- On a shift with a first-difference metric the Bowen ball of order `n ≥ 1` and radius
`β^k` about `x` is the cylinder `[x↾(n + k)]`. Blueprint node `meas:shift`. -/
theorem bowenBall_shiftMap_eq_cylinder (hβ : 0 < β) (hβ₁ : β < 1)
    (hd : ∀ x y : ℕ → α, x ≠ y → dist x y = β ^ PiNat.firstDiff x y) (x : ℕ → α) {n : ℕ}
    (hn : 1 ≤ n) (k : ℕ) : bowenBall shiftMap n x (β ^ k) = PiNat.cylinder x (n + k) := by
  ext y
  simp only [mem_bowenBall_iff, PiNat.mem_cylinder_iff, iterate_shiftMap,
    dist_lt_pow_iff hβ hβ₁ hd]
  constructor
  · intro h m hm
    by_cases hmk : m ≤ k
    · exact (h 0 (by omega) m hmk).symm
    · have := h (m - k) (by omega) k le_rfl
      rw [show k + (m - k) = m by omega] at this
      exact this.symm
  · intro h j hj i hi
    exact (h (i + j) (by omega)).symm

/-- The scale argument common to `localEntropy_shiftMap` and `informationRate_shiftMap`: if
`f n` is antitone in the scale and `f n (β^k) = a (n + k)` for `n ≥ 1`, then the suprema over the
dyadic scales of the growth rates of `f n` are the growth rates of `a`, since every dyadic radius
lies between two powers of `β`. -/
private lemma iSup_dyadic_eq (hβ₁ : β < 1) (f : ℕ → ℝ → ℝ≥0∞)
    (hf : ∀ n, Antitone (f n)) (a : ℕ → ℝ≥0∞)
    (ha : ∀ n, 1 ≤ n → ∀ k : ℕ, f n (β ^ k) = a (n + k)) :
    (⨆ p : ℕ, liminf (fun n : ℕ ↦ f n (dyadicRadius p) / n) atTop,
        ⨆ p : ℕ, limsup (fun n : ℕ ↦ f n (dyadicRadius p) / n) atTop) =
      (liminf (fun n : ℕ ↦ a n / n) atTop, limsup (fun n : ℕ ↦ a n / n) atTop) := by
  have hk : ∀ k : ℕ, (fun n : ℕ ↦ f n (β ^ k) / n) =ᶠ[atTop] fun n : ℕ ↦ a (n + k) / n :=
    fun k ↦ (eventually_ge_atTop 1).mono fun n hn ↦ by simp only [ha n hn k]
  have hmono : ∀ {r s : ℝ}, r ≤ s → ∀ n : ℕ, f n s / n ≤ f n r / n :=
    fun h n ↦ ENNReal.div_le_div_right (hf n h) _
  have hp : ∀ p : ℕ, ∃ k : ℕ, β ^ k ≤ dyadicRadius p ∧ dyadicRadius p ≤ β ^ 0 := fun p ↦ by
    obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (dyadicRadius_pos p) hβ₁
    refine ⟨k, hk.le, ?_⟩
    rw [pow_zero, dyadicRadius]
    exact pow_le_one₀ (by norm_num) (by norm_num)
  ext
  · refine (iSup_congr fun p ↦ ?_).trans iSup_const
    obtain ⟨k, hk₁, hk₂⟩ := hp p
    refine le_antisymm ?_ ?_
    · refine (liminf_le_liminf (.of_forall (hmono hk₁))).trans ?_
      rw [liminf_congr (hk k), (rate_add a k).1]
    · refine le_trans ?_ (liminf_le_liminf (.of_forall (hmono hk₂)))
      rw [liminf_congr (hk 0), (rate_add a 0).1]
  · refine (iSup_congr fun p ↦ ?_).trans iSup_const
    obtain ⟨k, hk₁, hk₂⟩ := hp p
    refine le_antisymm ?_ ?_
    · refine (limsup_le_limsup (.of_forall (hmono hk₁))).trans ?_
      rw [limsup_congr (hk k), (rate_add a k).2]
    · refine le_trans ?_ (limsup_le_limsup (.of_forall (hmono hk₂)))
      rw [limsup_congr (hk 0), (rate_add a 0).2]

variable [MeasurableSpace (ℕ → α)]

/-- On a shift with a first-difference metric the local entropies of a measure are the lower
and upper growth rates of `-log₂ μ[x↾n]`. Blueprint node `meas:shift`. -/
theorem localEntropy_shiftMap (hβ : 0 < β) (hβ₁ : β < 1)
    (hd : ∀ x y : ℕ → α, x ≠ y → dist x y = β ^ PiNat.firstDiff x y) (μ : Measure (ℕ → α))
    (x : ℕ → α) :
    localEntropy μ shiftMap x =
      (liminf (fun n : ℕ ↦ infoBits (μ (PiNat.cylinder x n)) / n) atTop,
        limsup (fun n : ℕ ↦ infoBits (μ (PiNat.cylinder x n)) / n) atTop) :=
  iSup_dyadic_eq hβ₁ (fun n ε ↦ infoBits (μ (bowenBall shiftMap n x ε)))
    (fun n _ _ h ↦ infoBits_antitone (measure_mono (bowenBall_subset_of_le _ n x h))) _
    fun n hn k ↦ by rw [bowenBall_shiftMap_eq_cylinder hβ hβ₁ hd x hn k]

/-- On a shift with a first-difference metric the information rates of a measure are the
lower and upper growth rates of `∫ -log₂ μ[x↾n] dμ(x)`. Blueprint node `meas:shift`. -/
theorem informationRate_shiftMap [BorelSpace (ℕ → α)] (hβ : 0 < β) (hβ₁ : β < 1)
    (hd : ∀ x y : ℕ → α, x ≠ y → dist x y = β ^ PiNat.firstDiff x y) (μ : Measure (ℕ → α)) :
    informationRate μ shiftMap =
      (liminf (fun n : ℕ ↦ (∫⁻ x, infoBits (μ (PiNat.cylinder x n)) ∂μ) / n) atTop,
        limsup (fun n : ℕ ↦ (∫⁻ x, infoBits (μ (PiNat.cylinder x n)) ∂μ) / n) atTop) :=
  iSup_dyadic_eq hβ₁ (fun n ε ↦ bowenInformation μ shiftMap n ε)
    (fun n _ _ h ↦ lintegral_mono fun x ↦
      infoBits_antitone (measure_mono (bowenBall_subset_of_le _ n x h))) _
    fun n hn k ↦ by
      simp only [bowenInformation, bowenBall_shiftMap_eq_cylinder hβ hβ₁ hd _ hn k]

end firstDiff

section dirac

variable {X : Type*} [MetricSpace X] [SecondCountableTopology X] [MeasurableSpace X]
  [BorelSpace X]

/-- Example 7.4(1), failure of integral affinity for point masses: for the identity kernel
`ω ↦ δ_ω` and any Borel probability measure `μ`, the law of `Φ_{δ_ω}(x)` under `μ ⊗ δ` is the
point mass at `(0, 0)`, since `x = ω` almost surely and `Φ_{δ_x}(x) = (0, 0)`.
Blueprint node `meas:shift`. -/
theorem map_localEntropy_compProd_id (μ : Measure X) [IsProbabilityMeasure μ] (T : X → X) :
    Measure.map (fun p : X × X ↦ localEntropy (ProbabilityTheory.Kernel.id p.1) T p.2)
        (μ ⊗ₘ ProbabilityTheory.Kernel.id) = Measure.dirac (0, 0) := by
  have hdiag : ∀ᵐ p ∂(μ ⊗ₘ ProbabilityTheory.Kernel.id), p.1 = p.2 := by
    rw [Measure.compProd_id]
    exact (ae_map_iff measurable_diag.aemeasurable measurableSet_diagonal).2
      (.of_forall fun _ ↦ rfl)
  rw [Measure.map_congr (g := fun _ ↦ ((0, 0) : ℝ≥0∞ × ℝ≥0∞)) (hdiag.mono fun p hp ↦ by
    simp only [ProbabilityTheory.Kernel.id_apply, hp, localEntropy_dirac]), Measure.map_const]
  simp

end dirac

section cantor

/-- The Cantor metric `dist x y = (1/2) ^ firstDiff x y` on `ℕ → Bool`. Its uniformity, hence
its topology, is definitionally the product one, so the product σ-algebra is its Borel
σ-algebra. Not a global instance: use `attribute [local instance] cantorMetricSpace`. -/
@[reducible] noncomputable def cantorMetricSpace : MetricSpace (ℕ → Bool) :=
  PiNat.metricSpaceOfDiscreteUniformity fun _ ↦ rfl

attribute [local instance] cantorMetricSpace

/-- The Cantor metric is the first-difference metric with ratio `1/2`. -/
theorem cantorMetricSpace_dist_eq {x y : ℕ → Bool} (h : x ≠ y) :
    dist x y = (1 / 2 : ℝ) ^ PiNat.firstDiff x y :=
  PiNat.dist_eq_of_ne h

/-- The left shift is continuous on Cantor space. -/
theorem continuous_shiftMap_cantor : Continuous (shiftMap : (ℕ → Bool) → ℕ → Bool) :=
  continuous_shiftMap (β := 1 / 2) (by norm_num) (by norm_num) fun _ _ ↦ cantorMetricSpace_dist_eq

/-- The product σ-algebra of Cantor space is the Borel σ-algebra of the Cantor metric. -/
theorem borelSpace_cantorMetricSpace : BorelSpace (ℕ → Bool) := inferInstance

/-- The fair-coin measure of the cylinder `[x↾n]` is `2^{-n}`. Blueprint node `meas:shift`. -/
theorem uniformMeasure_cylinder (x : ℕ → Bool) (n : ℕ) :
    uniformMeasure (PiNat.cylinder x n) = (2 : ℝ≥0∞)⁻¹ ^ n := by
  have h : cantorCylinder (cantorPrefix x n) = PiNat.cylinder x n := by
    ext y
    simp [cantorCylinder, IsCantorPrefix, cantorPrefix, PiNat.mem_cylinder_iff]
  have := cantorMass_uniformMeasure (cantorPrefix x n)
  rwa [cantorMass, h, cantorPrefix_length] at this

/-- For the fair-coin measure on Cantor space every point has local entropies `(1, 1)` under
the shift. Blueprint node `meas:shift`. -/
theorem localEntropy_uniformMeasure_shiftMap (x : ℕ → Bool) :
    localEntropy uniformMeasure shiftMap x = (1, 1) := by
  have hd : ∀ x y : ℕ → Bool, x ≠ y → dist x y = (1 / 2 : ℝ) ^ PiNat.firstDiff x y :=
    fun _ _ ↦ cantorMetricSpace_dist_eq
  have h1 : (fun n : ℕ ↦ infoBits (uniformMeasure (PiNat.cylinder x n)) / n) =ᶠ[atTop]
      fun _ ↦ 1 := (eventually_ge_atTop 1).mono fun n hn ↦ by
    have hn0 : (n : ℝ≥0∞) ≠ 0 := by exact_mod_cast (Nat.one_pos.trans_le hn).ne'
    simp only
    rw [uniformMeasure_cylinder, infoBits_of_ne (by simp), ENNReal.toReal_pow,
      ENNReal.toReal_inv, ENNReal.toReal_ofNat, Real.logb_pow, Real.logb_inv,
      Real.logb_self_eq_one one_lt_two]
    simp only [mul_neg, mul_one, neg_neg, ENNReal.ofReal_natCast]
    exact ENNReal.div_self hn0 (ENNReal.natCast_ne_top n)
  rw [localEntropy_shiftMap (by norm_num) (by norm_num) hd, liminf_congr h1, limsup_congr h1,
    liminf_const, limsup_const]

/-- The entropy law of the fair-coin measure under the shift is the point mass at `(1, 1)`.
Blueprint node `meas:shift`. -/
theorem entropyLaw_uniformMeasure_shiftMap :
    entropyLaw uniformMeasure shiftMap = Measure.dirac (1, 1) := by
  have h : localEntropy uniformMeasure (shiftMap : (ℕ → Bool) → ℕ → Bool) = fun _ ↦ (1, 1) :=
    funext localEntropy_uniformMeasure_shiftMap
  rw [entropyLaw, h, Measure.map_const]
  simp

/-- Example 7.4(1): for the fair-coin measure `μ` on Cantor space and the identity kernel
`ω ↦ δ_ω`, the law of `Φ_{δ_ω}(x)` under `μ ⊗ δ` (which is `δ_{(0, 0)}`) differs from the entropy
law `Λ_μ = δ_{(1, 1)}`: the entropy law is not affine along this disintegration.
Blueprint node `meas:shift`. -/
theorem map_localEntropy_compProd_id_ne_entropyLaw :
    Measure.map (fun p : (ℕ → Bool) × (ℕ → Bool) ↦
        localEntropy (ProbabilityTheory.Kernel.id p.1) shiftMap p.2)
        (uniformMeasure ⊗ₘ ProbabilityTheory.Kernel.id) ≠
      entropyLaw uniformMeasure shiftMap := by
  rw [map_localEntropy_compProd_id, entropyLaw_uniformMeasure_shiftMap]
  intro h
  have := congrArg (fun ν : Measure (ℝ≥0∞ × ℝ≥0∞) ↦ ν {((0, 0) : ℝ≥0∞ × ℝ≥0∞)}) h
  simp at this

end cantor

end Kolmogorov.PointToSet
