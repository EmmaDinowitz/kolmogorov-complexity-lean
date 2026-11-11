/-
Copyright (c) 2026 Emma Dinowitz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emma Dinowitz
-/
import KolmogorovMathlib.PointToSet.Measure.ShiftDecompositionAux

/-!
# Smooth families of product measures (Remark 7.7): helper material

Let `μ_θ = ⨂_i Bernoulli(β_i(θ))` for `θ ∈ [0, 1]`, with `β_i : [0, 1] → [δ, 1 - δ]` uniformly
`L`-Lipschitz (Remark 7.7 of E. Dinowitz, *Entropy of non-invariant measures and orbit
complexity of random points*). This file proves the two estimates of the remark:

* `smooth_cylinder_ge`: for `|θ - θ'| < 1/(k n)` with `2L ≤ δ k` and every word `w` of length
  `n`, `μ_{θ'}[w] ≥ μ_θ[w] / 2` (a product of `n` factors, each at least
  `1 - 1/(2n)` times the corresponding factor of `μ_θ[w]`; Bernoulli's inequality);
* `ae_eventually_measure_ball_ge`: for every probability measure `P` on `[0, 1]` and `k ≥ 1`,
  `P(B(θ, 1/(k n))) ≥ n^{-3}` for all large `n`, for `P`-almost every `θ` (a covering of
  `[0, 1]` by `k n + 1` intervals and the first Borel–Cantelli lemma);

and combines them into `ae_logb_ratio_le_smoothFamily`: `log₂ (μ_θ[x↾n] / μ[x↾n]) ≤
3 log₂ n + 1` for all large `n`, for `P ⊗ μ_•`-almost every `(θ, x)`, where `μ = ∫ μ_θ dP`.

Blueprint node `meas:examples`.
-/

namespace Kolmogorov.PointToSet

open Filter Set MeasureTheory ProbabilityTheory
open scoped Topology ENNReal NNReal

section smooth

/-- The probability `β` or `1 - β` of the symbol `a` under `Bernoulli(β)`. -/
noncomputable def bernoulliWeight (b : unitInterval) (a : Bool) : ℝ :=
  if a then (b : ℝ) else 1 - b

/-- The mass of a cylinder under a product of Bernoulli measures:
`(⨂_i Bernoulli(b_i))[x↾n] = ∏_{i < n} b_i(x_i)`. -/
theorem infinitePi_bernoulli_cylinder (b : ℕ → unitInterval) (x : ℕ → Bool) (n : ℕ) :
    Measure.infinitePi (fun i ↦ ProbabilityTheory.bernoulliMeasure true false (b i))
        (PiNat.cylinder x n) =
      ENNReal.ofReal (∏ i ∈ Finset.range n, bernoulliWeight (b i) (x i)) := by
  have hc : PiNat.cylinder x n = Set.pi (Finset.range n : Set ℕ) fun i ↦ {x i} := by
    ext y
    simp [PiNat.mem_cylinder_iff]
  rw [hc, Measure.infinitePi_pi _ fun _ _ ↦ measurableSet_singleton _,
    ENNReal.ofReal_prod_of_nonneg fun i _ ↦ ?_]
  · refine Finset.prod_congr rfl fun i _ ↦ ?_
    cases hx : x i
    · rw [bernoulliMeasure_apply_of_notMem_of_mem _ (measurableSet_singleton _) (by simp)
        (by simp)]
      simp only [bernoulliWeight, Bool.false_eq_true, ite_false]
      rw [← ENNReal.ofReal_coe_nnreal]
      congr 1
    · rw [bernoulliMeasure_apply_of_mem_of_notMem _ (measurableSet_singleton _) (by simp)
        (by simp)]
      simp only [bernoulliWeight, ite_true]
      rw [← ENNReal.ofReal_coe_nnreal]
      rfl
  · unfold bernoulliWeight
    split_ifs
    · exact (b i).2.1
    · exact sub_nonneg.2 (b i).2.2

variable (β : ℕ → unitInterval → unitInterval) {δ : ℝ} {L : ℝ≥0}

omit β in
/-- The weights are at least `δ` when `β ∈ [δ, 1 - δ]`. -/
lemma le_bernoulliWeight {b : unitInterval} (hb : δ ≤ (b : ℝ) ∧ (b : ℝ) ≤ 1 - δ) (a : Bool) :
    δ ≤ bernoulliWeight b a := by
  unfold bernoulliWeight
  split_ifs
  · exact hb.1
  · linarith [hb.2]

/-- One factor: if `|θ - θ'| < 1/(k n)` and `2L ≤ δ k`, then
`b_i(θ', a) ≥ (1 - 1/(2n)) b_i(θ, a)`. -/
lemma bernoulliWeight_ge (hδ : 0 < δ) (hβ : ∀ i θ, δ ≤ (β i θ : ℝ) ∧ (β i θ : ℝ) ≤ 1 - δ)
    (hL : ∀ i, LipschitzWith L (β i)) {k n : ℕ} (hk1 : 1 ≤ k) (hk : 2 * (L : ℝ) ≤ δ * k)
    (hn : 1 ≤ n)
    {θ θ' : unitInterval} (hθ : dist θ θ' < 1 / (k * n : ℝ)) (i : ℕ) (a : Bool) :
    (1 - 1 / (2 * n : ℝ)) * bernoulliWeight (β i θ) a ≤ bernoulliWeight (β i θ') a := by
  have hlip : |(β i θ : ℝ) - β i θ'| ≤ L * dist θ θ' := by
    have := (hL i).dist_le_mul θ θ'
    rwa [Subtype.dist_eq, Real.dist_eq] at this
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk1
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  -- `|b(θ') - b(θ)| ≤ L dist θ θ' ≤ δ / (2n) ≤ b(θ) / (2n)`
  have hdiff : |bernoulliWeight (β i θ) a - bernoulliWeight (β i θ') a| ≤
      bernoulliWeight (β i θ) a / (2 * n) := by
    have h1 : |bernoulliWeight (β i θ) a - bernoulliWeight (β i θ') a| =
        |(β i θ : ℝ) - β i θ'| := by
      unfold bernoulliWeight
      split_ifs
      · rfl
      · rw [show (1 - (β i θ : ℝ)) - (1 - β i θ') = -((β i θ : ℝ) - β i θ') by ring, abs_neg]
    have h2 : (L : ℝ) * dist θ θ' ≤ δ / (2 * n) := by
      have hd : dist θ θ' * (k * n) < 1 := by
        rwa [lt_div_iff₀ (by positivity)] at hθ
      rw [le_div_iff₀ (by positivity)]
      nlinarith [dist_nonneg (x := θ) (y := θ'), L.2]
    have h3 : δ / (2 * n) ≤ bernoulliWeight (β i θ) a / (2 * n) :=
      div_le_div_of_nonneg_right (le_bernoulliWeight (hβ i θ) a) (by positivity)
    rw [h1]
    exact hlip.trans (h2.trans h3)
  have := (abs_le.1 hdiff).2
  have hw : 0 ≤ bernoulliWeight (β i θ) a := hδ.le.trans (le_bernoulliWeight (hβ i θ) a)
  have : bernoulliWeight (β i θ) a / (2 * n) = 1 / (2 * n) * bernoulliWeight (β i θ) a := by
    ring
  nlinarith

/-- Remark 7.7, first estimate: if `|θ - θ'| < 1/(k n)` and `2L ≤ δ k`, then
`μ_{θ'}[x↾n] ≥ μ_θ[x↾n] / 2` (in the real form of the products of weights). -/
lemma prod_bernoulliWeight_ge (hδ : 0 < δ)
    (hβ : ∀ i θ, δ ≤ (β i θ : ℝ) ∧ (β i θ : ℝ) ≤ 1 - δ)
    (hL : ∀ i, LipschitzWith L (β i)) {k n : ℕ} (hk1 : 1 ≤ k) (hk : 2 * (L : ℝ) ≤ δ * k)
    (hn : 1 ≤ n)
    {θ θ' : unitInterval} (hθ : dist θ θ' < 1 / (k * n : ℝ)) (x : ℕ → Bool) :
    (1 / 2) * ∏ i ∈ Finset.range n, bernoulliWeight (β i θ) (x i) ≤
      ∏ i ∈ Finset.range n, bernoulliWeight (β i θ') (x i) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hle : 1 / (2 * n : ℝ) ≤ 1 := (div_le_one (by positivity : (0 : ℝ) < 2 * n)).2 (by linarith)
  have hw : ∀ i, 0 ≤ bernoulliWeight (β i θ) (x i) := fun i ↦
    hδ.le.trans (le_bernoulliWeight (hβ i θ) _)
  have hbern : (1 / 2 : ℝ) ≤ (1 - 1 / (2 * n : ℝ)) ^ n := by
    have := one_add_mul_le_pow (a := -(1 / (2 * n : ℝ)))
      (by linarith) n
    rw [← sub_eq_add_neg] at this
    calc (1 / 2 : ℝ) = 1 + n * -(1 / (2 * n)) := by field_simp; ring
      _ ≤ _ := this
  calc (1 / 2) * ∏ i ∈ Finset.range n, bernoulliWeight (β i θ) (x i)
      ≤ (1 - 1 / (2 * n : ℝ)) ^ n * ∏ i ∈ Finset.range n, bernoulliWeight (β i θ) (x i) :=
        mul_le_mul_of_nonneg_right hbern (Finset.prod_nonneg fun i _ ↦ hw i)
    _ = ∏ i ∈ Finset.range n, ((1 - 1 / (2 * n : ℝ)) * bernoulliWeight (β i θ) (x i)) := by
        rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range]
    _ ≤ _ := Finset.prod_le_prod₀
        (fun i _ ↦ mul_nonneg (by linarith) (hw i))
        fun i _ ↦ bernoulliWeight_ge β hδ hβ hL hk1 hk hn hθ i (x i)

omit β in
/-- Remark 7.7, second estimate (covering argument): for every probability measure `P` on
`[0, 1]` and `k ≥ 1`, `P(B(θ, 1/(k n))) ≥ n^{-3}` for all large `n`, `P`-almost everywhere. -/
theorem ae_eventually_measure_ball_ge (P : Measure unitInterval) [IsProbabilityMeasure P]
    {k : ℕ} (hk : 1 ≤ k) :
    ∀ᵐ θ ∂P, ∀ᶠ n : ℕ in atTop,
      ENNReal.ofReal (1 / (n : ℝ) ^ 3) ≤ P (Metric.ball θ (1 / (k * n : ℝ))) := by
  -- the interval of index `j` at scale `N = k n`
  set I : ℕ → ℕ → Set unitInterval := fun N j ↦ {θ | ⌊(θ : ℝ) * N⌋₊ = j}
  set s : ℕ → Set unitInterval := fun n ↦
    {θ | P (Metric.ball θ (1 / (k * n : ℝ))) < ENNReal.ofReal (1 / (n : ℝ) ^ 3)}
  have hsub : ∀ n, 1 ≤ n → s n ⊆ ⋃ j ∈ (Finset.range (k * n + 1)).filter
      (fun j ↦ P (I (k * n) j) < ENNReal.ofReal (1 / (n : ℝ) ^ 3)), I (k * n) j := by
    intro n hn θ hθ
    have hN : (0 : ℝ) < k * n := by
      have : (1 : ℝ) ≤ k := by exact_mod_cast hk
      have : (1 : ℝ) ≤ n := by exact_mod_cast hn
      positivity
    have hIball : I (k * n) ⌊(θ : ℝ) * (k * n : ℕ)⌋₊ ⊆ Metric.ball θ (1 / (k * n : ℝ)) := by
      intro θ' hθ'
      simp only [I, mem_ofPred_eq] at hθ'
      rw [Metric.mem_ball, Subtype.dist_eq, Real.dist_eq]
      have h1 := Nat.floor_le (mul_nonneg θ'.2.1 (Nat.cast_nonneg (k * n)))
      have h2 := Nat.lt_floor_add_one ((θ' : ℝ) * (k * n : ℕ))
      have h3 := Nat.floor_le (mul_nonneg θ.2.1 (Nat.cast_nonneg (k * n)))
      have h4 := Nat.lt_floor_add_one ((θ : ℝ) * (k * n : ℕ))
      rw [hθ'] at h1 h2
      push_cast at h1 h2 h3 h4
      rw [abs_sub_lt_iff]
      constructor <;> rw [lt_div_iff₀ hN] <;> nlinarith
    simp only [mem_iUnion, Finset.mem_filter, Finset.mem_range, exists_prop]
    refine ⟨⌊(θ : ℝ) * (k * n : ℕ)⌋₊, ⟨?_, (measure_mono hIball).trans_lt hθ⟩, rfl⟩
    rw [Nat.lt_add_one_iff]
    refine Nat.floor_le_of_le ?_
    calc (θ : ℝ) * (k * n : ℕ) ≤ 1 * (k * n : ℕ) :=
          mul_le_mul_of_nonneg_right θ.2.2 (Nat.cast_nonneg _)
      _ = (k * n : ℕ) := one_mul _
  have hbound : ∀ n, 1 ≤ n → P (s n) ≤ ENNReal.ofReal (2 * k / (n : ℝ) ^ 2) := by
    intro n hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    refine (measure_mono (hsub n hn)).trans ((measure_biUnion_finset_le _ _).trans ?_)
    calc ∑ j ∈ (Finset.range (k * n + 1)).filter
          (fun j ↦ P (I (k * n) j) < ENNReal.ofReal (1 / (n : ℝ) ^ 3)), P (I (k * n) j)
        ≤ ∑ _j ∈ Finset.range (k * n + 1), ENNReal.ofReal (1 / (n : ℝ) ^ 3) := by
          refine (Finset.sum_le_sum fun j hj ↦ (Finset.mem_filter.1 hj).2.le).trans ?_
          exact Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
      _ = ENNReal.ofReal ((k * n + 1 : ℕ) * (1 / (n : ℝ) ^ 3)) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, ENNReal.ofReal_mul
            (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
      _ ≤ ENNReal.ofReal (2 * k / (n : ℝ) ^ 2) := by
          refine ENNReal.ofReal_le_ofReal ?_
          have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
          have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
          push_cast
          rw [mul_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
          nlinarith [mul_le_mul hk1 hn1 zero_le_one (by linarith : (0 : ℝ) ≤ k)]
  have hsum : ∑' n, P (s (n + 1)) ≠ ∞ := by
    refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum fun n ↦ hbound (n + 1) (by omega))
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun n ↦ by positivity)]
    · exact ENNReal.ofReal_ne_top
    · have := ((Real.summable_one_div_nat_pow.2 one_lt_two).comp_injective
        (add_left_injective 1)).mul_left (2 * k : ℝ)
      refine this.congr fun n ↦ ?_
      simp [div_eq_mul_inv]
  filter_upwards [ae_eventually_notMem hsum] with θ hθ
  obtain ⟨N, hN⟩ := eventually_atTop.1 hθ
  refine eventually_atTop.2 ⟨N + 1, fun n hn ↦ ?_⟩
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have := hN m (by omega)
  simpa [s] using this

/-- Remark 7.7, the key bound: for the smooth family `μ_θ = ⨂_i Bernoulli(β_i(θ))`
(`β_i ∈ [δ, 1 - δ]`, uniformly `L`-Lipschitz), every probability measure `P` on `[0, 1]` and
`P ⊗ μ_•`-almost every `(θ, x)`, `log₂ (μ_θ[x↾n] / μ[x↾n]) ≤ 3 log₂ n + 1` for all large `n`,
where `μ = ∫ μ_θ dP`. -/
theorem ae_logb_ratio_le_smoothFamily (hδ : 0 < δ)
    (hβ : ∀ i θ, δ ≤ (β i θ : ℝ) ∧ (β i θ : ℝ) ≤ 1 - δ) (hL : ∀ i, LipschitzWith L (β i))
    (κ : Kernel unitInterval (ℕ → Bool)) [IsMarkovKernel κ]
    (hκ : ∀ θ, κ θ =
      Measure.infinitePi fun i ↦ ProbabilityTheory.bernoulliMeasure true false (β i θ))
    (P : Measure unitInterval) [IsProbabilityMeasure P] :
    ∀ᵐ p ∂(P ⊗ₘ κ), ∀ᶠ n : ℕ in atTop,
      Real.logb 2 ((κ p.1 (PiNat.cylinder p.2 n)).toReal /
        ((P.bind κ) (PiNat.cylinder p.2 n)).toReal) ≤ 3 * Real.logb 2 n + 1 := by
  set k : ℕ := ⌈2 * (L : ℝ) / δ⌉₊ + 1
  have hk1 : 1 ≤ k := by omega
  have hk : 2 * (L : ℝ) ≤ δ * k := by
    have h := Nat.le_ceil (2 * (L : ℝ) / δ)
    rw [div_le_iff₀ hδ] at h
    have : (k : ℝ) = ⌈2 * (L : ℝ) / δ⌉₊ + 1 := by simp [k]
    rw [this]
    nlinarith
  have hP := ae_eventually_measure_ball_ge P hk1
  have hM : ∀ᵐ p ∂(P ⊗ₘ κ), ∀ᶠ n : ℕ in atTop,
      ENNReal.ofReal (1 / (n : ℝ) ^ 3) ≤ P (Metric.ball p.1 (1 / (k * n : ℝ))) := by
    have key : ∀ R : unitInterval → Prop, (∀ᵐ θ ∂P, R θ) → ∀ᵐ p ∂(P ⊗ₘ κ), R p.1 := by
      intro R hR
      have h' : ∀ᵐ θ ∂(P ⊗ₘ κ).map Prod.fst, R θ := by
        rw [show (P ⊗ₘ κ).map Prod.fst = P from Measure.fst_compProd P κ]
        exact hR
      exact ae_of_ae_map measurable_fst.aemeasurable h'
    exact key _ hP
  filter_upwards [hM] with p hp
  filter_upwards [hp, eventually_ge_atTop 1] with n hn h1
  set C := PiNat.cylinder p.2 n
  have hCm : MeasurableSet C := measurableSet_cantor_cylinder p.2 n
  set w : unitInterval → ℝ := fun θ ↦ ∏ i ∈ Finset.range n, bernoulliWeight (β i θ) (p.2 i)
  have hκC : ∀ θ, κ θ C = ENNReal.ofReal (w θ) := fun θ ↦ by
    rw [hκ, infinitePi_bernoulli_cylinder]
  have hw0 : 0 < w p.1 :=
    Finset.prod_pos fun i _ ↦ hδ.trans_le (le_bernoulliWeight (hβ i p.1) _)
  have hn0 : (0 : ℝ) < n := by exact_mod_cast h1
  have hμ : ENNReal.ofReal (1 / 2 * w p.1 * (1 / (n : ℝ) ^ 3)) ≤ (P.bind κ) C := by
    rw [Measure.bind_apply hCm (Kernel.aemeasurable _)]
    calc ENNReal.ofReal (1 / 2 * w p.1 * (1 / (n : ℝ) ^ 3))
        = ENNReal.ofReal (1 / 2 * w p.1) * ENNReal.ofReal (1 / (n : ℝ) ^ 3) :=
          ENNReal.ofReal_mul (by positivity)
      _ ≤ ENNReal.ofReal (1 / 2 * w p.1) * P (Metric.ball p.1 (1 / (k * n : ℝ))) :=
          mul_le_mul_right hn _
      _ = ∫⁻ θ', (Metric.ball p.1 (1 / (k * n : ℝ))).indicator
            (fun _ ↦ ENNReal.ofReal (1 / 2 * w p.1)) θ' ∂P :=
          (lintegral_indicator_const Metric.isOpen_ball.measurableSet _).symm
      _ ≤ ∫⁻ θ', κ θ' C ∂P := lintegral_mono fun θ' ↦ by
          by_cases h : θ' ∈ Metric.ball p.1 (1 / (k * n : ℝ))
          · rw [indicator_of_mem h, hκC]
            rw [Metric.mem_ball, dist_comm] at h
            exact ENNReal.ofReal_le_ofReal (prod_bernoulliWeight_ge β hδ hβ hL hk1 hk h1 h p.2)
          · rw [indicator_of_notMem h]
            exact bot_le
  have hpos : 0 < 1 / 2 * w p.1 * (1 / (n : ℝ) ^ 3) := by positivity
  have hμt : 1 / 2 * w p.1 * (1 / (n : ℝ) ^ 3) ≤ ((P.bind κ) C).toReal := by
    have := ENNReal.toReal_mono (measure_ne_top _ _) hμ
    rwa [ENNReal.toReal_ofReal hpos.le] at this
  rw [hκC, ENNReal.toReal_ofReal hw0.le]
  have hratio : w p.1 / ((P.bind κ) C).toReal ≤ 2 * (n : ℝ) ^ 3 := by
    rw [div_le_iff₀ (hpos.trans_le hμt)]
    have h2 : 2 * (n : ℝ) ^ 3 * (1 / 2 * w p.1 * (1 / (n : ℝ) ^ 3)) = w p.1 := by
      field_simp
    nlinarith [mul_le_mul_of_nonneg_left hμt (by positivity : (0 : ℝ) ≤ 2 * (n : ℝ) ^ 3)]
  calc Real.logb 2 (w p.1 / ((P.bind κ) C).toReal) ≤ Real.logb 2 (2 * (n : ℝ) ^ 3) :=
        Real.logb_le_logb_of_le one_lt_two (div_pos hw0 (hpos.trans_le hμt)) hratio
    _ = 3 * Real.logb 2 n + 1 := by
        rw [Real.logb_mul (by norm_num) (by positivity), Real.logb_self_eq_one one_lt_two,
          Real.logb_pow]
        push_cast
        ring

end smooth

end Kolmogorov.PointToSet
