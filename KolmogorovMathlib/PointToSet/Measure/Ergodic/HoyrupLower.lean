/-
Copyright (c) 2026 Emma Dinowitz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emma Dinowitz
-/
import KolmogorovMathlib.PointToSet.Measure.Ergodic.HoyrupBirkhoff
import KolmogorovMathlib.PointToSet.Measure.Ergodic.HoyrupEntropyLimit

/-!
# The lower half of the effective Shannon–McMillan–Breiman theorem

Theorem 4.1 of Hoyrup (STACS 2012), lower half, relativized: for an `A`-computable shift-invariant
ergodic probability measure `ν` on `ℕ → Bool` and a sequence `ω` that is `ν`-random relative to
`A`, `liminf_n -log₂ ν[ω↾n] / n ≥ h_ν(σ)`; with the lower half of Levin–Schnorr
(`exists_infoBits_le_wordComplexity_add`) this gives Hoyrup's theorem
`liminf_n K^A(ω↾n)/n ≥ h_ν(σ)` (`shiftEntropy_le_liminf_wordComplexity_bool` in
`SymbolicLowerBound`).

Proof. For `N, L`: `-log₂ ν[ω↾n] ≥ ∑_{k<n-N} min(g_N, L)(σ^k ω)`
(`sum_min_iInf_condInfo_le_infoBits`) and `min(g_N, L) = L - truncDefect ν N L`, a bounded lower
semicomputable function (`isLscFunIn_truncDefect`), so by the effective upper Birkhoff bound
(`limsup_shiftAverage_le_lintegral`) `liminf_n -log₂ ν[ω↾n]/n ≥ L - ∫ truncDefect = ∫ min(g_N, L)`.
Take suprema (`shiftEntropy_le_iSup_lintegral_min`).

Blueprint node `erg:hoyrup`.
-/

namespace Kolmogorov.PointToSet

open Filter Set MeasureTheory
open scoped Topology ENNReal Computability

/-- Effective Shannon–McMillan–Breiman, lower half: `liminf_n -log₂ ν[ω↾n]/n ≥ h_ν(σ)` at every
`ν`-random sequence. Blueprint node `erg:hoyrup`. -/
theorem shiftEntropy_le_liminf_infoBits {A : Set ℕ} {ν : Measure (ℕ → Bool)}
    [IsProbabilityMeasure ν] (hν : Ergodic shiftMap ν) (hc : IsComputableWordMeasureIn A ν)
    {ω : ℕ → Bool} (hω : ω ∈ wordRandomPoints A ν) :
    shiftEntropy ν ≤
      liminf (fun n : ℕ ↦ infoBits (ν (listCylinder (wordPrefix ω n))) / n) atTop := by
  have hmp := hν.toMeasurePreserving
  refine (shiftEntropy_le_iSup_lintegral_min hmp).trans (iSup₂_le fun N L ↦ ?_)
  set f : (ℕ → Bool) → ℝ≥0∞ := fun x ↦ min (⨅ j ≥ N, condInfo ν j x) (L : ℝ≥0∞)
  set d := truncDefect ν N L
  have hL : (L : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top L
  have hfd : ∀ x, f x + d x = L := min_iInf_condInfo_add_truncDefect ν N L
  have hdL : ∀ x, d x ≤ L := truncDefect_le ν N L
  have hdlsc : IsLscFunIn A d := isLscFunIn_truncDefect hmp hc N L
  -- `∫ f + ∫ d = L`
  have hint : ∫⁻ x, f x ∂ν + ∫⁻ x, d x ∂ν = L := by
    rw [← lintegral_add_right _ hdlsc.measurable]
    simp only [hfd, lintegral_const, measure_univ, mul_one]
  have hintd : ∫⁻ x, d x ∂ν ≠ ⊤ :=
    ne_top_of_le_ne_top hL (hint ▸ le_add_self)
  have hintf : ∫⁻ x, f x ∂ν = L - ∫⁻ x, d x ∂ν := ENNReal.eq_sub_of_add_eq hintd hint
  -- the Birkhoff averages of `f` are `L` minus those of `d`
  have havg : ∀ᶠ n : ℕ in atTop,
      L - shiftAverage d n ω = (∑ k ∈ Finset.range n, f (shiftMap^[k] ω)) / n := by
    refine eventually_atTop.2 ⟨1, fun n hn ↦ ?_⟩
    have hn0 : (n : ℝ≥0∞) ≠ 0 := by exact_mod_cast (Nat.one_le_iff_ne_zero.1 hn)
    have hsum : (∑ k ∈ Finset.range n, f (shiftMap^[k] ω)) / n + shiftAverage d n ω = L := by
      rw [shiftAverage, ← ENNReal.add_div, ← Finset.sum_add_distrib]
      simp only [hfd, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      rw [mul_comm]
      exact ENNReal.mul_div_cancel_right hn0 (ENNReal.natCast_ne_top n)
    have hdn : shiftAverage d n ω ≠ ⊤ :=
      ne_top_of_le_ne_top hL (hsum ▸ le_add_self)
    exact (ENNReal.eq_sub_of_add_eq hdn hsum).symm
  have hBirk : ∫⁻ x, f x ∂ν ≤
      liminf (fun n : ℕ ↦ (∑ k ∈ Finset.range n, f (shiftMap^[k] ω)) / n) atTop := by
    rw [← liminf_congr havg, ENNReal.liminf_const_sub _ _ hL, hintf]
    exact tsub_le_tsub_left (limsup_shiftAverage_le_lintegral hν hc hdlsc hL hdL hω) _
  -- the shift `n - N` costs at most `N L`
  have hcmp : ∀ n : ℕ, (∑ k ∈ Finset.range n, f (shiftMap^[k] ω)) / n ≤
      infoBits (ν (listCylinder (wordPrefix ω n))) / n + ((N * L : ℕ) : ℝ≥0∞) / n := by
    intro n
    rw [← ENNReal.add_div]
    gcongr
    rw [← Finset.sum_range_add_sum_Ico _ (Nat.sub_le n N)]
    gcongr
    · exact sum_min_iInf_condInfo_le_infoBits hmp ω N L n
    · refine (Finset.sum_le_card_nsmul _ _ (L : ℝ≥0∞) fun k _ ↦ min_le_right _ _).trans ?_
      rw [Nat.card_Ico, nsmul_eq_mul]
      push_cast
      gcongr
      exact_mod_cast (by omega : n - (n - N) ≤ N)
  have hlim : Tendsto (fun n : ℕ ↦ ((N * L : ℕ) : ℝ≥0∞) / n) atTop (𝓝 0) := by
    have := ENNReal.Tendsto.const_mul ENNReal.tendsto_inv_nat_nhds_zero
      (Or.inr (ENNReal.natCast_ne_top (N * L)))
    simpa [div_eq_mul_inv] using this
  calc ∫⁻ x, f x ∂ν
      ≤ liminf (fun n : ℕ ↦ (∑ k ∈ Finset.range n, f (shiftMap^[k] ω)) / n) atTop := hBirk
    _ ≤ liminf ((fun n : ℕ ↦ infoBits (ν (listCylinder (wordPrefix ω n))) / n) +
          fun n : ℕ ↦ ((N * L : ℕ) : ℝ≥0∞) / n) atTop :=
        liminf_le_liminf (Eventually.of_forall hcmp)
    _ = _ := ENNReal.liminf_add_of_right_tendsto_zero hlim _

/-- Hoyrup's theorem, relativized (the statement of `shiftEntropy_le_liminf_wordComplexity_bool`):
`liminf_n K^A(ω↾n)/n ≥ h_ν(σ)` at every `ν`-random sequence. Blueprint node `erg:hoyrup`. -/
theorem shiftEntropy_le_liminf_wordComplexity_bool_of_hoyrup (A : Set ℕ)
    (ν : Measure (ℕ → Bool)) [IsProbabilityMeasure ν] (hν : Ergodic shiftMap ν)
    (hc : IsComputableWordMeasureIn A ν) {ω : ℕ → Bool} (hω : ω ∈ wordRandomPoints A ν) :
    shiftEntropy ν ≤ liminf (fun n : ℕ ↦ (wordComplexity A ω n : ℝ≥0∞) / n) atTop := by
  obtain ⟨c, hcK⟩ := exists_infoBits_le_wordComplexity_add hc hω
  have hlim : Tendsto (fun n : ℕ ↦ (c : ℝ≥0∞) / n) atTop (𝓝 0) := by
    have := ENNReal.Tendsto.const_mul ENNReal.tendsto_inv_nat_nhds_zero
      (Or.inr (ENNReal.natCast_ne_top c))
    simpa [div_eq_mul_inv] using this
  have hcmp : ∀ n : ℕ, infoBits (ν (listCylinder (wordPrefix ω n))) / n ≤
      ((fun n : ℕ ↦ (wordComplexity A ω n : ℝ≥0∞) / n) + fun n : ℕ ↦ (c : ℝ≥0∞) / n) n := by
    intro n
    rw [Pi.add_apply, ← ENNReal.add_div]
    gcongr
    exact_mod_cast hcK n
  calc shiftEntropy ν
      ≤ liminf (fun n : ℕ ↦ infoBits (ν (listCylinder (wordPrefix ω n))) / n) atTop :=
        shiftEntropy_le_liminf_infoBits hν hc hω
    _ ≤ liminf ((fun n : ℕ ↦ (wordComplexity A ω n : ℝ≥0∞) / n) +
          fun n : ℕ ↦ (c : ℝ≥0∞) / n) atTop :=
        liminf_le_liminf (Eventually.of_forall hcmp)
    _ = _ := ENNReal.liminf_add_of_right_tendsto_zero hlim _

end Kolmogorov.PointToSet
