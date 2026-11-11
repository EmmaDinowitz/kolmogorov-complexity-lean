/-
Copyright (c) 2026 Emma Dinowitz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emma Dinowitz
-/
import KolmogorovMathlib.PointToSet.Measure.LocalEntropy
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite

/-!
# Domination along Bowen balls (Lemma 7.1)

Let `μ` be a finite Borel measure and `ν` a Borel measure on a separable metric space, `T`
continuous and `ε > 0`. Then for `ν`-almost every `x`,

`μ(B_n(x, T, ε)) ≤ n² ν(B_n(x, T, 2ε))` for all sufficiently large `n`

(E. Dinowitz, *Entropy of non-invariant measures and orbit complexity of random points*,
Lemma 7.1). For fixed `n` the set `E_n` where the inequality fails contains a maximal subset
`S` whose points are pairwise at `d_n`-distance at least `2ε`; the Bowen balls of radius `ε`
about the points of `S` are disjoint, so `S` is countable and
`∑_{x ∈ S} ν(B_n(x, T, 2ε)) ≤ n^{-2} μ(X)`, while by maximality the Bowen balls of radius `2ε`
about `S` cover `E_n`. The Borel–Cantelli lemma finishes the proof.

* `ae_eventually_measure_bowenBall_le`: the lemma.
* `ae_localEntropy_le`: consequently `Φ_ν ≤ Φ_μ` coordinatewise, `ν`-almost everywhere: a
  measure has, almost everywhere, the smallest local entropies.

Blueprint node `meas:domination`.
-/

namespace Kolmogorov.PointToSet

open Filter Set MeasureTheory
open scoped Topology ENNReal

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [SecondCountableTopology X]

omit [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X] in
/-- Two Bowen balls of radius `ε` meet only if their centres are `2ε`-close. -/
private lemma mem_bowenBall_two_mul_of_mem {T : X → X} {n : ℕ} {x y z : X} {ε : ℝ}
    (hx : z ∈ bowenBall T n x ε) (hy : z ∈ bowenBall T n y ε) :
    y ∈ bowenBall T n x (2 * ε) := by
  refine mem_bowenBall_iff.2 fun k hk ↦ ?_
  have h1 := mem_bowenBall_iff.1 hx k hk
  have h2 := mem_bowenBall_iff.1 hy k hk
  rw [dist_comm] at h2
  calc dist (T^[k] x) (T^[k] y) ≤ dist (T^[k] x) (T^[k] z) + dist (T^[k] z) (T^[k] y) :=
        dist_triangle _ _ _
    _ < ε + ε := add_lt_add h1 h2
    _ = 2 * ε := by ring

/-- The packing estimate behind Lemma 7.1: the set where
`n² ν(B_n(x, T, 2ε)) < μ(B_n(x, T, ε))` has `ν`-measure at most `μ(X) / n²`. -/
private lemma measure_setOf_lt_le {T : X → X} (hT : Continuous T) (μ ν : Measure X)
    {ε : ℝ} (hε : 0 < ε) {n : ℕ} (hn : 1 ≤ n) :
    ν {x | (n : ℝ≥0∞) ^ 2 * ν (bowenBall T n x (2 * ε)) < μ (bowenBall T n x ε)} ≤
      μ univ / (n : ℝ≥0∞) ^ 2 := by
  set E := {x | (n : ℝ≥0∞) ^ 2 * ν (bowenBall T n x (2 * ε)) < μ (bowenBall T n x ε)}
  let 𝒮 : Set (Set X) :=
    {S | S ⊆ E ∧ ∀ x ∈ S, ∀ y ∈ S, x ≠ y → y ∉ bowenBall T n x (2 * ε)}
  obtain ⟨S, hSmax⟩ : ∃ S, Maximal (· ∈ 𝒮) S := by
    refine zorn_subset 𝒮 fun c hc hchain ↦ ⟨⋃₀ c, ⟨?_, ?_⟩, fun s hs ↦ subset_sUnion_of_mem hs⟩
    · exact sUnion_subset fun s hs ↦ (hc hs).1
    · rintro x ⟨s, hs, hxs⟩ y ⟨t, ht, hyt⟩ hxy
      rcases hchain.total hs ht with hst | hts
      · exact (hc ht).2 x (hst hxs) y hyt hxy
      · exact (hc hs).2 x hxs y (hts hyt) hxy
  have hS : S ∈ 𝒮 := hSmax.prop
  have hdisj : S.PairwiseDisjoint fun x ↦ bowenBall T n x ε := fun x hx y hy hxy ↦
    Set.disjoint_left.2 fun _ hzx hzy ↦ hS.2 x hx y hy hxy (mem_bowenBall_two_mul_of_mem hzx hzy)
  have hcount : S.Countable := hdisj.countable_of_isOpen
    (fun x _ ↦ bowen_ball_dense_open T hT n x ε) fun x _ ↦ ⟨x, self_mem_bowenBall T n x ε hε⟩
  have hcover : E ⊆ ⋃ x ∈ S, bowenBall T n x (2 * ε) := by
    intro e he
    by_cases heS : e ∈ S
    · exact mem_biUnion heS (self_mem_bowenBall T n e _ (by linarith))
    · have hnot : insert e S ∉ 𝒮 := fun h ↦ heS (hSmax.2 h (subset_insert _ _) (mem_insert _ _))
      have hsub : insert e S ⊆ E := insert_subset he hS.1
      simp only [𝒮, mem_ofPred_eq, hsub, true_and, not_forall, not_not] at hnot
      obtain ⟨x, hx, y, hy, hxy, h⟩ := hnot
      rcases mem_insert_iff.1 hx with rfl | hxS <;> rcases mem_insert_iff.1 hy with rfl | hyS
      · exact absurd rfl hxy
      · exact mem_biUnion hyS (mem_bowenBall_symm h)
      · exact mem_biUnion hxS h
      · exact absurd h (hS.2 x hxS y hyS hxy)
  have h0 : ((n : ℝ≥0∞) ^ 2) ≠ 0 := pow_ne_zero _ (by exact_mod_cast (by omega : n ≠ 0))
  have htop : ((n : ℝ≥0∞) ^ 2) ≠ ⊤ := ENNReal.pow_ne_top (ENNReal.natCast_ne_top n)
  calc ν E ≤ ν (⋃ x ∈ S, bowenBall T n x (2 * ε)) := measure_mono hcover
    _ ≤ ∑' x : S, ν (bowenBall T n x (2 * ε)) := measure_biUnion_le ν hcount _
    _ ≤ ∑' x : S, μ (bowenBall T n x ε) * ((n : ℝ≥0∞) ^ 2)⁻¹ := by
        refine ENNReal.tsum_le_tsum fun x ↦ ?_
        rw [← div_eq_mul_inv, ENNReal.le_div_iff_mul_le (Or.inl h0) (Or.inl htop), mul_comm]
        exact (hS.1 x.2).le
    _ = μ (⋃ x ∈ S, bowenBall T n x ε) / (n : ℝ≥0∞) ^ 2 := by
        rw [ENNReal.tsum_mul_right, measure_biUnion hcount hdisj
          (fun x _ ↦ (bowen_ball_dense_open T hT n x ε).measurableSet), div_eq_mul_inv]
    _ ≤ μ univ / (n : ℝ≥0∞) ^ 2 := by gcongr; exact subset_univ _

/-- Domination (Lemma 7.1): for `ν`-almost every `x`,
`μ(B_n(x, T, ε)) ≤ n² ν(B_n(x, T, 2ε))` for all sufficiently large `n`.
Blueprint node `meas:domination`. -/
theorem ae_eventually_measure_bowenBall_le {T : X → X} (hT : Continuous T) (μ ν : Measure X)
    [IsFiniteMeasure μ] {ε : ℝ} (hε : 0 < ε) :
    ∀ᵐ x ∂ν, ∀ᶠ n : ℕ in atTop,
      μ (bowenBall T n x ε) ≤ (n : ℝ≥0∞) ^ 2 * ν (bowenBall T n x (2 * ε)) := by
  set s : ℕ → Set X := fun n ↦
    {x | 1 ≤ n ∧ (n : ℝ≥0∞) ^ 2 * ν (bowenBall T n x (2 * ε)) < μ (bowenBall T n x ε)}
  have key : ∀ n, ν (s n) ≤ μ univ * ENNReal.ofReal (1 / (n : ℝ) ^ 2) := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [s]
    · calc ν (s n) ≤ ν {x | (n : ℝ≥0∞) ^ 2 * ν (bowenBall T n x (2 * ε)) <
            μ (bowenBall T n x ε)} := measure_mono fun x hx ↦ hx.2
        _ ≤ μ univ / (n : ℝ≥0∞) ^ 2 := measure_setOf_lt_le hT μ ν hε hn
        _ = μ univ * ENNReal.ofReal (1 / (n : ℝ) ^ 2) := by
          rw [div_eq_mul_inv, ENNReal.ofReal_div_of_pos (by positivity), ENNReal.ofReal_one,
            ENNReal.ofReal_pow (Nat.cast_nonneg _), ENNReal.ofReal_natCast, one_div]
  have hsum : ∑' n, ν (s n) ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum key)
    rw [ENNReal.tsum_mul_left, ← ENNReal.ofReal_tsum_of_nonneg (fun n ↦ by positivity)
      (Real.summable_one_div_nat_pow.2 one_lt_two)]
    exact ENNReal.mul_ne_top (measure_ne_top μ univ) ENNReal.ofReal_ne_top
  filter_upwards [ae_eventually_notMem hsum] with x hx
  filter_upwards [hx, eventually_ge_atTop 1] with n hn h1
  simpa [s, h1] using hn

/-- If `a n ≤ b n + d n` eventually and `d n → 0`, then `liminf a ≤ liminf b` and
`limsup a ≤ limsup b`. -/
private lemma liminf_limsup_le_of_eventually_le_add {a b d : ℕ → ℝ≥0∞}
    (hd : Tendsto d atTop (𝓝 0)) (h : ∀ᶠ n in atTop, a n ≤ b n + d n) :
    liminf a atTop ≤ liminf b atTop ∧ limsup a atTop ≤ limsup b atTop := by
  have hev : ∀ δ : NNReal, 0 < δ → ∀ᶠ n in atTop, a n ≤ b n + δ := by
    intro δ hδ
    filter_upwards [h, hd.eventually (gt_mem_nhds (by exact_mod_cast hδ : (0 : ℝ≥0∞) < δ))]
      with n h1 h2
    exact h1.trans (by gcongr)
  constructor <;> refine ENNReal.le_of_forall_pos_le_add fun δ hδ _ ↦ ?_
  · calc liminf a atTop ≤ liminf (fun n ↦ b n + δ) atTop := liminf_le_liminf (hev δ hδ)
      _ = liminf b atTop + δ := liminf_add_const atTop b _ (by isBoundedDefault)
          (by isBoundedDefault)
  · calc limsup a atTop ≤ limsup (fun n ↦ b n + δ) atTop := limsup_le_limsup (hev δ hδ)
      _ = limsup b atTop + δ := limsup_add_const atTop b _ (by isBoundedDefault)
          (by isBoundedDefault)

/-- `2 log₂ n / n → 0`, in `ℝ≥0∞`. -/
private lemma tendsto_ofReal_two_mul_logb_div :
    Tendsto (fun n : ℕ ↦ ENNReal.ofReal (2 * Real.logb 2 n) / n) atTop (𝓝 0) := by
  have hR : Tendsto (fun n : ℕ ↦ 2 * Real.logb 2 n / n) atTop (𝓝 0) := by
    have := (Real.tendsto_pow_logb_div_mul_add_atTop (b := 2) (1 / 2) 0 1
      (by norm_num)).comp tendsto_natCast_atTop_atTop
    refine this.congr fun n ↦ ?_
    simp only [Function.comp_apply, pow_one, add_zero]
    ring
  have := ENNReal.tendsto_ofReal hR
  rw [ENNReal.ofReal_zero] at this
  refine this.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  rw [ENNReal.ofReal_div_of_pos (by exact_mod_cast hn), ENNReal.ofReal_natCast]

/-- Lemma 7.1 at a fixed scale: `ν`-almost everywhere, the local entropies of `ν` at the scale
`2ε` are at most those of `μ` at the scale `ε`. Blueprint node `meas:domination`. -/
theorem ae_localEntropyAt_le {T : X → X} (hT : Continuous T) (μ ν : Measure X)
    [IsFiniteMeasure μ] {ε : ℝ} (hε : 0 < ε) :
    ∀ᵐ x ∂ν, (localEntropyAt ν T x (2 * ε)).1 ≤ (localEntropyAt μ T x ε).1 ∧
      (localEntropyAt ν T x (2 * ε)).2 ≤ (localEntropyAt μ T x ε).2 := by
  filter_upwards [ae_eventually_measure_bowenBall_le hT μ ν hε] with x hx
  refine liminf_limsup_le_of_eventually_le_add tendsto_ofReal_two_mul_logb_div ?_
  filter_upwards [hx, eventually_ge_atTop 1] with n hn h1
  unfold localEntropyRate
  rw [← ENNReal.add_div]
  gcongr
  have hc : (1 : ℝ) ≤ (n : ℝ) ^ 2 := one_le_pow₀ (by exact_mod_cast h1)
  refine (infoBits_le_infoBits_mul_add hc _).trans (add_le_add (infoBits_antitone ?_) ?_)
  · rwa [ENNReal.ofReal_pow (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
  · rw [Real.logb_pow]
    push_cast
    rfl

/-- Lemma 7.1, consequence: `Φ_ν ≤ Φ_μ` coordinatewise, `ν`-almost everywhere.
Blueprint node `meas:domination`. -/
theorem ae_localEntropy_le {T : X → X} (hT : Continuous T) (μ ν : Measure X)
    [IsFiniteMeasure μ] :
    ∀ᵐ x ∂ν, (localEntropy ν T x).1 ≤ (localEntropy μ T x).1 ∧
      (localEntropy ν T x).2 ≤ (localEntropy μ T x).2 := by
  have hpos : ∀ p : ℕ, 0 < dyadicRadius p := fun p ↦ by unfold dyadicRadius; positivity
  have hd : ∀ p : ℕ, dyadicRadius p = 2 * dyadicRadius (p + 1) := fun p ↦ by
    unfold dyadicRadius
    rw [pow_succ]
    ring
  have h := fun p : ℕ ↦ ae_localEntropyAt_le hT μ ν (hpos (p + 1))
  filter_upwards [ae_all_iff.2 h] with x hx
  simp only [localEntropy]
  constructor
  · refine iSup_le fun p ↦ le_iSup_of_le (p + 1) ?_
    rw [hd p]
    exact (hx p).1
  · refine iSup_le fun p ↦ le_iSup_of_le (p + 1) ?_
    rw [hd p]
    exact (hx p).2

end Kolmogorov.PointToSet
