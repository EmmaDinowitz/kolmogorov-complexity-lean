/-
Copyright (c) 2026 Emma Dinowitz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emma Dinowitz
-/
import KolmogorovMathlib.PointToSet.Measure.Ergodic.ExampleFiveFiveLowerAux
import KolmogorovMathlib.PointToSet.Measure.RandomNonAtom

/-!
# Example 5.5(2): a random point of lower complexity `0` for a measure of entropy `1`

This file proves `exists_random_lowerLocalEntropy_eq_zero'`, the core of Example 5.5(2) of
E. Dinowitz, *Entropy of non-invariant measures and orbit complexity of random points*, on Cantor
space with its standard computable presentation `cantorPresentation`.

Let `Ω` be the binary expansion of Chaitin's `Ω`, with computable approximations `W t` whose bits
stabilise to those of `Ω` (`ex55l_exists_omega`), let `N_k = k^(k+1)`, and let
`E_k = ex55l_In W k` (for `k = ⟨n, t⟩`: `W t↾n` is new at stage `t > n` and `y↾n = W t↾n`).
The causal map `f' = ex55l_f W` replaces the block `[N_k, N_{k+1})` of `y` by zeros when
`y ∈ E_k`, and `μ' = λ ∘ f'⁻¹`.

* **`Φ_{μ'} = (1, 1)` almost everywhere** (`ex55l_ae_localEntropy_eq_one`). The upper bound `≤ 1`
  holds on the set of `x` with `μ'[x↾n] ≥ 2^{-n}` for all `n`, whose complement has empty
  preimage. For the lower bound, call `[N_k, N_k + k + 1)` the window of the block `k`. If from
  some block `i₀` on every window of `x` contains a `1`, a `v` with `f'(v)↾n = x↾n` cannot lie in
  `E_k` for the blocks `k ≥ i₀` whose window ends before `n`, so `v` copies `x` there and
  `μ'[x↾n] ≤ 2^{-(n - k - 1 - N_{i₀})}` for `n` in the block `k` (`ex55l_map_cylinder_le`); since
  `k = o(N_k)` the lower rate is at least `1`. The exceptional set has `μ'`-measure `0`: if
  `f'(y)` has infinitely many zero windows then either `y ∈ E_k` infinitely often, which forces
  `y = Ω` (`ex55l_eventually_not_in`), or `y` itself has infinitely many zero windows, a null set
  by Borel–Cantelli (`λ(window k is zero) = 2^{-(k+1)}`).
* **The random point** `z' = f'(Ω)` is `μ'`-random
  (`cantorPres_map_mem_randomPoints_of_isMartinLofRandom`) and `Ω ∈ E_k` for infinitely many `k`
  (`ex55l_frequently_in`); for those `μ'[z'↾N_{k+1}] ≥ λ[Ω↾N_k] = 2^{-N_k}`
  (`ex55l_pow_le_map_of_in`), and `N_k / N_{k+1} → 0`, so `h̲_{μ'}(σ, z') = 0`
  (`ex55l_liminf_eq_zero`).

Blueprint node `meas:examples`.
-/

namespace Kolmogorov.PointToSet

open Filter Set MeasureTheory
open scoped Topology ENNReal Computability

attribute [local instance] cantorMetricSpace

/-! ### Fair-coin measure of finitely many coordinates -/

/-- Prescribing finitely many coordinates is a measurable condition. -/
lemma ex55l_measurableSet_finset (S : Finset ℕ) (c : ℕ → Bool) :
    MeasurableSet {v : ℕ → Bool | ∀ j ∈ S, v j = c j} := by
  have hset : {v : ℕ → Bool | ∀ j ∈ S, v j = c j} = (↑S : Set ℕ).pi fun j ↦ {c j} := by
    ext v; simp [Set.mem_pi]
  rw [hset]
  exact MeasurableSet.pi S.countable_toSet fun _ _ ↦ measurableSet_singleton _

/-- The fair-coin measure of prescribing the coordinates in a finite set `S`: `2^{-|S|}`. -/
lemma ex55l_uniformMeasure_finset (S : Finset ℕ) (c : ℕ → Bool) :
    uniformMeasure {v : ℕ → Bool | ∀ j ∈ S, v j = c j} = 2⁻¹ ^ S.card := by
  have hset : {v : ℕ → Bool | ∀ j ∈ S, v j = c j} = (↑S : Set ℕ).pi fun j ↦ {c j} := by
    ext v; simp [Set.mem_pi]
  rw [hset, uniformMeasure, bernoulliMeasure,
    Measure.infinitePi_pi _ fun _ _ ↦ measurableSet_singleton _]
  rw [Finset.prod_congr rfl (g := fun _ ↦ (2 : ℝ≥0∞)⁻¹) fun j _ ↦ ?_, Finset.prod_const]
  cases c j
  · rw [ProbabilityTheory.bernoulliMeasure_apply_of_notMem_of_mem _ (measurableSet_singleton _)
      (by simp) rfl]
    have h : unitInterval.toNNReal (unitInterval.symm ⟨((1 / 2 : NNReal) : ℝ),
        (1 / 2 : NNReal).2, NNReal.coe_le_one.mpr (by norm_num)⟩) = 2⁻¹ := by
      ext
      simp [unitInterval.coe_symm_eq]
      norm_num
    rw [h, ENNReal.coe_inv two_ne_zero, ENNReal.coe_ofNat]
  · rw [ProbabilityTheory.bernoulliMeasure_apply_of_mem_of_notMem _ (measurableSet_singleton _)
      rfl (by simp)]
    have h : unitInterval.toNNReal ⟨((1 / 2 : NNReal) : ℝ),
        (1 / 2 : NNReal).2, NNReal.coe_le_one.mpr (by norm_num)⟩ = 2⁻¹ := by
      ext
      simp
    rw [h, ENNReal.coe_inv two_ne_zero, ENNReal.coe_ofNat]

/-- `2^{-e}` as a real power. -/
lemma ex55l_inv_two_pow (e : ℕ) :
    (2 : ℝ≥0∞)⁻¹ ^ e = ENNReal.ofReal ((2 : ℝ) ^ (-(e : ℝ))) := by
  rw [Real.rpow_neg (by norm_num), Real.rpow_natCast, ← inv_pow, ENNReal.ofReal_pow (by norm_num),
    ENNReal.ofReal_inv_of_pos (by norm_num), ENNReal.ofReal_ofNat]

/-- The information of `2^{-e}` is at most `e`. -/
lemma ex55l_infoBits_inv_two_pow_le (e : ℕ) : infoBits ((2 : ℝ≥0∞)⁻¹ ^ e) ≤ e :=
  (infoBits_two_inv_pow e).le

/-! ### The windows -/

/-- The window `[N_k, N_k + k + 1)` of `x` is all zero. -/
def ex55l_Z (k : ℕ) : Set (ℕ → Bool) :=
  {x | ∀ j ∈ Finset.Ico (ex55l_N k) (ex55l_N k + k + 1), x j = (fun _ ↦ false) j}

/-- The zero-window sets are measurable. -/
lemma ex55l_measurableSet_Z (k : ℕ) : MeasurableSet (ex55l_Z k) :=
  ex55l_measurableSet_finset _ _

/-- A window is zero with probability `2^{-(k+1)}`. -/
lemma ex55l_uniformMeasure_Z (k : ℕ) : uniformMeasure (ex55l_Z k) = 2⁻¹ ^ (k + 1) := by
  rw [ex55l_Z, ex55l_uniformMeasure_finset, Nat.card_Ico]
  congr 1
  omega

/-- Almost every sequence has only finitely many zero windows (Borel–Cantelli). -/
lemma ex55l_measure_frequently_Z :
    uniformMeasure {y : ℕ → Bool | ∃ᶠ k in atTop, y ∈ ex55l_Z k} = 0 := by
  refine measure_setOfPred_frequently_eq_zero (ne_top_of_le_ne_top (b := ∑' k : ℕ,
    (2 : ℝ≥0∞)⁻¹ ^ k) ?_ (ENNReal.tsum_le_tsum fun k ↦ ?_))
  · rw [ENNReal.tsum_geometric, ENNReal.one_sub_inv_two, inv_inv]
    exact ENNReal.ofNat_ne_top
  · change uniformMeasure (ex55l_Z k) ≤ _
    rw [ex55l_uniformMeasure_Z]
    exact pow_le_pow_right_of_le_one' (by norm_num) (Nat.le_succ k)

/-! ### The events `E_k` along `Ω` -/

variable (W : ℕ → ℕ → Bool)

/-- A sequence `y ≠ Ω` lies in only finitely many `E_k`. -/
lemma ex55l_eventually_not_in {Ω y : ℕ → Bool} (hconv : ∀ j, ∀ᶠ t in atTop, W t j = Ω j)
    (hy : y ≠ Ω) : ∀ᶠ k in atTop, ¬ ex55l_In W k y := by
  obtain ⟨p, hp⟩ : ∃ p, y p ≠ Ω p := by
    by_contra h
    push Not at h
    exact hy (funext h)
  have hT : ∀ᶠ t in atTop, ∀ j ∈ Finset.range (p + 1), W t j = Ω j :=
    (eventually_all_finset _).2 fun j _ ↦ hconv j
  obtain ⟨T, hT⟩ := eventually_atTop.1 hT
  refine eventually_atTop.2 ⟨(T + p + 2) ^ 2, fun k hk hin ↦ ?_⟩
  obtain ⟨htrig, hmatch⟩ := hin
  rw [ex55l_trig_eq_true] at htrig
  obtain ⟨hnt, hnew⟩ := htrig
  have hbound : k.unpair.1 < T + p + 2 ∧ k.unpair.2 < T + p + 2 := by
    by_cases hnp : p < k.unpair.1
    · have ht : k.unpair.2 < T := by
        by_contra hcon
        have := hT k.unpair.2 (by omega) p (Finset.mem_range.2 (by omega))
        exact hp ((hmatch p hnp).symm.trans this)
      omega
    · rcases hnew with h | ⟨j, hj, hne⟩
      · omega
      · have ht : k.unpair.2 - 1 < T := by
          by_contra hcon
          exact hne ((hT _ (by omega) j (Finset.mem_range.2 (by omega))).trans
            (hT _ (by omega) j (Finset.mem_range.2 (by omega))).symm)
        omega
  have hk' := Nat.pair_lt_max_add_one_sq k.unpair.1 k.unpair.2
  rw [Nat.pair_unpair] at hk'
  have : (max k.unpair.1 k.unpair.2 + 1) ^ 2 ≤ (T + p + 2) ^ 2 :=
    Nat.pow_le_pow_left (by omega) 2
  omega

/-- `Ω` lies in `E_k` for arbitrarily large `k`. -/
lemma ex55l_frequently_in {Ω : ℕ → Bool} (hconv : ∀ j, ∀ᶠ t in atTop, W t j = Ω j) (K : ℕ) :
    ∃ k ≥ K, ex55l_In W k Ω := by
  classical
  have hT : ∀ᶠ t in atTop, ∀ j ∈ Finset.range K, W t j = Ω j :=
    (eventually_all_finset _).2 fun j _ ↦ hconv j
  obtain ⟨T, hT⟩ := eventually_atTop.1 hT
  have hex : ∃ t, K < t ∧ ∀ s ≥ t, ∀ j < K, W s j = Ω j :=
    ⟨max T (K + 1), by omega, fun s hs j hj ↦ hT s (by omega) j (Finset.mem_range.2 hj)⟩
  obtain ⟨hKt, hstab⟩ := Nat.find_spec hex
  refine ⟨Nat.pair K (Nat.find hex), Nat.left_le_pair _ _, ?_, ?_⟩
  · rw [ex55l_trig_eq_true]
    simp only [Nat.unpair_pair]
    refine ⟨hKt, ?_⟩
    by_cases heq : Nat.find hex = K + 1
    · exact Or.inl heq
    · right
      have hmin := Nat.find_min hex (show Nat.find hex - 1 < Nat.find hex by omega)
      push Not at hmin
      obtain ⟨s, hs, j, hj, hne⟩ := hmin (by omega)
      have hs' : s = Nat.find hex - 1 := by
        by_contra h
        exact hne (hstab s (by omega) j hj)
      subst hs'
      exact ⟨j, hj, fun h ↦ hne (h.symm.trans (hstab _ le_rfl j hj))⟩
  · simp only [Nat.unpair_pair]
    exact fun j hj ↦ hstab _ le_rfl j hj

/-! ### The image measure -/

/-- The sequence map is measurable. -/
lemma ex55l_measurable_f : Measurable (ex55l_f W) :=
  cantorPres_measurable (ex55l_wordPrefix_f W)

/-- The cylinders are measurable. -/
lemma ex55l_measurableSet_cylinder (x : ℕ → Bool) (n : ℕ) :
    MeasurableSet (PiNat.cylinder x n) :=
  measurableSet_cantor_cylinder x n

/-- **The cylinder estimate off the zero windows.** If every window of `x` from the block `i₀` on
contains a `1`, then for `n` in the block `k`, `μ'[x↾n] ≤ 2^{-(n - (k+1) - N_{i₀})}`. -/
lemma ex55l_map_cylinder_le {x : ℕ → Bool} {i₀ : ℕ}
    (hx : ∀ k ≥ i₀, ∃ j, ex55l_N k ≤ j ∧ j < ex55l_N k + k + 1 ∧ x j = true)
    {k n : ℕ} (hn1 : ex55l_N k ≤ n) (hn2 : n < ex55l_N (k + 1)) :
    uniformMeasure.map (ex55l_f W) (PiNat.cylinder x n) ≤
      2⁻¹ ^ (n - (k + 1) - ex55l_N i₀) := by
  rw [Measure.map_apply (ex55l_measurable_f W) (ex55l_measurableSet_cylinder x n)]
  set n' := if ex55l_N k + k + 1 ≤ n then n else ex55l_N k with hn'
  have hn'n : n' ≤ n := by rw [hn']; split_ifs <;> omega
  have hn'ge : n - (k + 1) ≤ n' := by rw [hn']; split_ifs <;> omega
  have hsub : ex55l_f W ⁻¹' PiNat.cylinder x n ⊆
      {v | ∀ j ∈ Finset.Ico (ex55l_N i₀) n', v j = x j} := by
    intro v hv j hj
    rw [Finset.mem_Ico] at hj
    have hv' : ∀ i < n, ex55l_f W v i = x i := PiNat.mem_cylinder_iff.1 hv
    obtain ⟨k', hk'1, hk'2⟩ := ex55l_exists_block j
    have hik' : i₀ ≤ k' := ex55l_le_of_N hj.1 hk'2
    obtain ⟨j', hj'1, hj'2, hj'3⟩ := hx k' hik'
    have hj'n : j' < n := by
      by_cases hcase : ex55l_N k + k + 1 ≤ n
      · have hk'k : k' ≤ k := ex55l_le_of_N hk'1 (by omega)
        have := ex55l_N_strictMono.monotone hk'k
        omega
      · have hn'eq : n' = ex55l_N k := by simp [hn', hcase]
        have hk'k : k' + 1 ≤ k := by
          by_contra hcon
          have := ex55l_N_strictMono.monotone (show k ≤ k' by omega)
          omega
        have h1 := ex55l_N_window k'
        have h2 := ex55l_N_strictMono.monotone hk'k
        omega
    have hnotin : ¬ ex55l_In W k' v := fun hin ↦ by
      have h1 := ex55l_f_of_in W hin hj'1 (by have := ex55l_N_window k'; omega)
      rw [hv' j' hj'n, hj'3] at h1
      exact Bool.noConfusion h1
    rw [← ex55l_f_of_not_in W hnotin hk'1 hk'2]
    exact hv' j (by omega)
  calc uniformMeasure (ex55l_f W ⁻¹' PiNat.cylinder x n)
      ≤ uniformMeasure {v | ∀ j ∈ Finset.Ico (ex55l_N i₀) n', v j = x j} := measure_mono hsub
    _ = 2⁻¹ ^ (Finset.Ico (ex55l_N i₀) n').card := ex55l_uniformMeasure_finset _ _
    _ ≤ _ := by
      rw [Nat.card_Ico]
      exact pow_le_pow_right_of_le_one' (by norm_num) (by omega)

/-- The cylinder estimate gives, for every `δ > 0`, `μ'[x↾n] ≤ 2^{-(1-δ) n}` eventually. -/
lemma ex55l_eventually_le_rpow {x : ℕ → Bool} {i₀ : ℕ}
    (hx : ∀ k ≥ i₀, ∃ j, ex55l_N k ≤ j ∧ j < ex55l_N k + k + 1 ∧ x j = true)
    {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in atTop, uniformMeasure.map (ex55l_f W) (PiNat.cylinder x n) ≤
      ENNReal.ofReal ((2 : ℝ) ^ (-((1 - δ) * n))) := by
  obtain ⟨M₀, hM₀⟩ := exists_nat_ge (2 / δ)
  set M := M₀ + 2 with hM
  have hMδ : 2 ≤ δ * M := by
    have h1 : 2 / δ ≤ M := by rw [hM]; push_cast; linarith
    rwa [div_le_iff₀ hδ, mul_comm] at h1
  set a := ex55l_N i₀ with ha
  refine eventually_atTop.2 ⟨M * (M + 1) + M * a + a, fun n hn ↦ ?_⟩
  obtain ⟨k, hk1, hk2⟩ := ex55l_exists_block n
  have hle := ex55l_map_cylinder_le W hx hk1 hk2
  have hMk : M * (k + 1) ≤ n := by
    by_cases hkM : k ≤ M
    · have : M * (k + 1) ≤ M * (M + 1) := Nat.mul_le_mul_left _ (by omega)
      omega
    · have hsq := ex55l_sq_le_N (show 1 ≤ k by omega)
      have : M * (k + 1) ≤ k * k := by nlinarith
      omega
  have hMa : M * a ≤ n := by omega
  have hsum : k + 1 + a ≤ n := by nlinarith
  obtain ⟨e, he⟩ : ∃ e, n = k + 1 + a + e := ⟨n - (k + 1 + a), by omega⟩
  have hexp : n - (k + 1) - a = e := by omega
  rw [hexp] at hle
  refine hle.trans ?_
  rw [ex55l_inv_two_pow]
  refine ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow_of_exponent_le one_le_two ?_)
  have hreal : ((k + 1 + a : ℕ) : ℝ) * M ≤ (δ * n) * M := by
    have h1 : ((M * (k + 1) + M * a : ℕ) : ℝ) ≤ (2 * n : ℝ) := by
      have : M * (k + 1) + M * a ≤ 2 * n := by omega
      exact_mod_cast this
    push_cast at h1 ⊢
    nlinarith
  have hMpos : (0 : ℝ) < M := by rw [hM]; positivity
  have hka : ((k + 1 + a : ℕ) : ℝ) ≤ δ * n := le_of_mul_le_mul_right hreal hMpos
  have hn' : (n : ℝ) = ((k + 1 + a : ℕ) : ℝ) + e := by rw [he]; push_cast; ring
  rw [hn'] at hka ⊢
  nlinarith

/-- Off the zero windows the lower rate is at least `1`. -/
lemma ex55l_one_le_liminf {x : ℕ → Bool} {i₀ : ℕ}
    (hx : ∀ k ≥ i₀, ∃ j, ex55l_N k ≤ j ∧ j < ex55l_N k + k + 1 ∧ x j = true) :
    1 ≤ liminf (fun n : ℕ ↦
      infoBits (uniformMeasure.map (ex55l_f W) (PiNat.cylinder x n)) / n) atTop := by
  refine le_of_forall_lt_imp_le_of_dense fun c hc ↦ ?_
  have hct : c ≠ ⊤ := ne_top_of_lt hc
  have hc1 : c.toReal < 1 := by
    have := ENNReal.toReal_strict_mono ENNReal.one_ne_top hc
    simpa using this
  have hev := ex55l_eventually_le_rpow W hx (δ := 1 - c.toReal) (by linarith)
  refine le_liminf_of_le (by isBoundedDefault) ((hev.and (eventually_ge_atTop 1)).mono ?_)
  rintro n ⟨hn, hn1⟩
  have hs : 1 - (1 - c.toReal) = c.toReal := by ring
  rw [hs] at hn
  have hinfo := le_infoBits_of_le_rpow hn
  have hn0 : (n : ℝ≥0∞) ≠ 0 := by exact_mod_cast (Nat.one_pos.trans_le hn1).ne'
  rw [ENNReal.le_div_iff_mul_le (Or.inl hn0) (Or.inl (ENNReal.natCast_ne_top n))]
  refine le_trans (le_of_eq ?_) hinfo
  rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hct, ENNReal.ofReal_natCast]

/-- **`Φ_{μ'} = (1, 1)` almost everywhere.** Blueprint node `meas:examples`. -/
theorem ex55l_ae_localEntropy_eq_one {Ω : ℕ → Bool}
    (hconv : ∀ j, ∀ᶠ t in atTop, W t j = Ω j) :
    ∀ᵐ x ∂(uniformMeasure.map (ex55l_f W)),
      localEntropy (uniformMeasure.map (ex55l_f W)) shiftMap x = (1, 1) := by
  set μ' := uniformMeasure.map (ex55l_f W) with hμ'
  have hmeas := ex55l_measurable_f W
  -- the points with `μ'[x↾n] ≥ 2^{-n}` for all `n`
  set H := {x : ℕ → Bool | ∀ n, (2 : ℝ≥0∞)⁻¹ ^ n ≤ μ' (PiNat.cylinder x n)} with hH
  have hHm : MeasurableSet H := by
    have : H = ⋂ n, {x : ℕ → Bool | (2 : ℝ≥0∞)⁻¹ ^ n ≤ μ' (PiNat.cylinder x n)} := by
      ext x; simp [hH]
    rw [this]
    refine MeasurableSet.iInter fun n ↦ ?_
    simp_rw [← cantorPres_listCylinder_wordPrefix]
    exact PoincareAux.measurableSet_setOf_wordPrefix
      (fun w ↦ (2 : ℝ≥0∞)⁻¹ ^ n ≤ μ' (listCylinder w)) n
  have hfH : ∀ y, ex55l_f W y ∈ H := fun y n ↦
    pow_le_map_uniformMeasure_cylinder hmeas.aemeasurable
      (cantorPres_causal (ex55l_wordPrefix_f W)) y n
  have hHc : μ' Hᶜ = 0 := by
    rw [hμ', Measure.map_apply hmeas hHm.compl]
    exact measure_mono_null (fun y hy ↦ absurd (hfH y) hy) measure_empty
  -- the points with infinitely many zero windows
  set B := {x : ℕ → Bool | ∃ᶠ k in atTop, x ∈ ex55l_Z k} with hB
  have hBm : MeasurableSet B := by
    have : B = ⋂ a : ℕ, ⋃ b : ℕ, ⋃ (_ : a ≤ b), ex55l_Z b := by
      ext x; simp [hB, frequently_atTop]
    rw [this]
    exact .iInter fun a ↦ .iUnion fun b ↦ .iUnion fun _ ↦ ex55l_measurableSet_Z b
  have hBc : μ' B = 0 := by
    rw [hμ', Measure.map_apply hmeas hBm]
    have hsub : ex55l_f W ⁻¹' B ⊆ {Ω} ∪ {y | ∃ᶠ k in atTop, y ∈ ex55l_Z k} := by
      intro y hy
      have hy' : ∃ᶠ k in atTop, ex55l_In W k y ∨ y ∈ ex55l_Z k := by
        refine Frequently.mono hy fun k hk ↦ ?_
        by_cases hin : ex55l_In W k y
        · exact Or.inl hin
        · refine Or.inr fun j hj ↦ ?_
          rw [Finset.mem_Ico] at hj
          have h1 := ex55l_f_of_not_in W hin hj.1 (by have := ex55l_N_window k; omega)
          rw [← h1]
          exact hk j (Finset.mem_Ico.2 hj)
      rcases frequently_or_distrib.1 hy' with h | h
      · refine Or.inl (by_contra fun hne ↦ ?_)
        exact not_frequently.2 (ex55l_eventually_not_in W hconv hne) h
      · exact Or.inr h
    exact measure_mono_null hsub (measure_union_null (uniformMeasure_singleton Ω)
      ex55l_measure_frequently_Z)
  rw [ae_iff]
  refine measure_mono_null (fun x hx ↦ ?_) (measure_union_null hHc hBc)
  by_contra hcon
  simp only [mem_union, mem_compl_iff, not_or, not_not] at hcon
  obtain ⟨hxH, hxB⟩ := hcon
  have hev : ∀ᶠ k in atTop, x ∉ ex55l_Z k := not_frequently.1 hxB
  obtain ⟨i₀, hi₀⟩ := eventually_atTop.1 hev
  have hxw : ∀ k ≥ i₀, ∃ j, ex55l_N k ≤ j ∧ j < ex55l_N k + k + 1 ∧ x j = true := by
    intro k hk
    have h := hi₀ k hk
    simp only [ex55l_Z, mem_ofPred_eq, not_forall, Finset.mem_Ico] at h
    obtain ⟨j, ⟨hj1, hj2⟩, hj⟩ := h
    exact ⟨j, hj1, hj2, by simpa using hj⟩
  have hle := localEntropy_shiftMap_le_one_of_le_cylinder μ' x hxH
  have hge : 1 ≤ (localEntropy μ' shiftMap x).1 := by
    rw [localEntropy_shiftMap (by norm_num) (by norm_num) cantor_hd]
    exact ex55l_one_le_liminf W hxw
  have hfs : (localEntropy μ' shiftMap x).1 ≤ (localEntropy μ' shiftMap x).2 := by
    rw [localEntropy_shiftMap (by norm_num) (by norm_num) cantor_hd]
    exact liminf_le_limsup
  exact hx (Prod.ext (le_antisymm hle.1 hge) (le_antisymm hle.2 (hge.trans hfs)))

/-! ### The random point `f'(Ω)` -/

/-- If `Ω ∈ E_k`, then `μ'[f'(Ω)↾N_{k+1}] ≥ λ[Ω↾N_k] = 2^{-N_k}`. -/
lemma ex55l_pow_le_map_of_in {Ω : ℕ → Bool} {k : ℕ} (hk : ex55l_In W k Ω) :
    (2 : ℝ≥0∞)⁻¹ ^ ex55l_N k ≤
      uniformMeasure.map (ex55l_f W) (PiNat.cylinder (ex55l_f W Ω) (ex55l_N (k + 1))) := by
  rw [← uniformMeasure_cylinder Ω (ex55l_N k)]
  refine (measure_mono (t := ex55l_f W ⁻¹' PiNat.cylinder (ex55l_f W Ω) (ex55l_N (k + 1)))
    fun v hv ↦ ?_).trans (Measure.le_map_apply (ex55l_measurable_f W).aemeasurable _)
  have hcaus := cantorPres_causal (ex55l_wordPrefix_f W) Ω v (ex55l_N k) hv
  have hvΩ : ∀ j < ex55l_N k, v j = Ω j := PiNat.mem_cylinder_iff.1 hv
  have hin : ex55l_In W k v := (ex55l_In_congr W k hvΩ).2 hk
  refine PiNat.mem_cylinder_iff.2 fun j hj ↦ ?_
  by_cases hjk : j < ex55l_N k
  · exact PiNat.mem_cylinder_iff.1 hcaus j hjk
  · rw [ex55l_f_of_in W hin (by omega) hj, ex55l_f_of_in W hk (by omega) hj]

/-- **The lower rate at `f'(Ω)` vanishes.** Blueprint node `meas:examples`. -/
theorem ex55l_liminf_eq_zero {Ω : ℕ → Bool} (hconv : ∀ j, ∀ᶠ t in atTop, W t j = Ω j) :
    liminf (fun n : ℕ ↦ infoBits (uniformMeasure.map (ex55l_f W)
      (PiNat.cylinder (ex55l_f W Ω) n)) / n) atTop = 0 := by
  refine le_antisymm ?_ bot_le
  refine ge_of_tendsto' ENNReal.tendsto_inv_nat_nhds_zero fun m ↦ ?_
  refine liminf_le_of_frequently_le' (frequently_atTop.2 fun a ↦ ?_)
  obtain ⟨k, hk, hin⟩ := ex55l_frequently_in W hconv (max a m)
  refine ⟨ex55l_N (k + 1), by have := ex55l_le_N (k + 1); omega, ?_⟩
  have h1 : infoBits (uniformMeasure.map (ex55l_f W)
      (PiNat.cylinder (ex55l_f W Ω) (ex55l_N (k + 1)))) ≤ (ex55l_N k : ℝ≥0∞) :=
    (infoBits_antitone (ex55l_pow_le_map_of_in W hin)).trans (ex55l_infoBits_inv_two_pow_le _)
  refine (ENNReal.div_le_div_right h1 _).trans ?_
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  · refine ENNReal.div_le_of_le_mul ?_
    have hmul : ((m * ex55l_N k : ℕ) : ℝ≥0∞) ≤ (ex55l_N (k + 1) : ℝ≥0∞) := by
      exact_mod_cast ex55l_mul_N_le (show m ≤ k + 1 by omega)
    push_cast at hmul
    calc (ex55l_N k : ℝ≥0∞) = (m : ℝ≥0∞)⁻¹ * ((m : ℝ≥0∞) * ex55l_N k) := by
          rw [← mul_assoc, ENNReal.inv_mul_cancel (by exact_mod_cast hm.ne')
            (ENNReal.natCast_ne_top m), one_mul]
      _ ≤ (m : ℝ≥0∞)⁻¹ * (ex55l_N (k + 1) : ℝ≥0∞) := by gcongr

/-! ### Example 5.5(2) -/

/-- Example 5.5(2), core construction (proof of `exists_random_lowerLocalEntropy_eq_zero`). With
`Ω` the binary expansion of Chaitin's `Ω` and `f'` the causal map of `ex55l_f`, the measure
`μ' = λ ∘ f'⁻¹` is computable for the standard presentation `cantorPresentation`
(`cantorPres_isMeasureAdmissible_map_uniformMeasure`), `Φ_{μ'} = (1, 1)` `μ'`-almost everywhere
(`ex55l_ae_localEntropy_eq_one`), and `z' = f'(Ω)` is `μ'`-random with `h̲_{μ'}(σ, z') = 0`
(`ex55l_liminf_eq_zero`). Blueprint node `meas:examples`. -/
theorem exists_random_lowerLocalEntropy_eq_zero' :
    ∃ μ' : Measure (ℕ → Bool), IsProbabilityMeasure μ' ∧
      IsMeasureAdmissible cantorPresentation shiftMap μ' ∅ ∧
      (∀ᵐ x ∂μ', localEntropy μ' shiftMap x = (1, 1)) ∧
      ∃ z' ∈ randomPoints cantorPresentation ∅ μ', (localEntropy μ' shiftMap z').1 = 0 := by
  obtain ⟨Ω, W, hΩ, hW, hconv⟩ := ex55l_exists_omega
  have hF := ex55l_wordPrefix_f W
  have hFc := ex55l_computable_F hW
  refine ⟨uniformMeasure.map (ex55l_f W), inferInstance,
    cantorPres_isMeasureAdmissible_map_uniformMeasure ∅ hFc hF,
    ex55l_ae_localEntropy_eq_one W hconv, ex55l_f W Ω,
    cantorPres_map_mem_randomPoints_of_isMartinLofRandom hFc hF hΩ, ?_⟩
  rw [localEntropy_shiftMap (by norm_num) (by norm_num) cantor_hd]
  exact ex55l_liminf_eq_zero W hconv

end Kolmogorov.PointToSet
