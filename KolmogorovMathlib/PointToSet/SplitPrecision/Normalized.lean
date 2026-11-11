/-
Copyright (c) 2026 Emma Dinowitz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emma Dinowitz
-/
import KolmogorovMathlib.PointToSet.SplitPrecision.Information
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Normalized forms

The comparison and symmetry theorems carry an error `O(budget₁ r + budget₂ s)`, which is
negligible only against a scale that dominates both budgets.  This file records the normalized
consequences for located families along sequences of precisions:

* `LocatedFamily.tendsto_minInfo_sub_splitInfo_div`: if `budget₁ (r k) / N k → 0` and
  `budget₂ (s k) / N k → 0`, then `(J - I) / N k → 0` (Corollary 1.11 of the notes);
* `LocatedFamily.tendsto_splitInfo_sub_symmetry_div`: under the same hypotheses the normalized
  mutual information and the normalized symmetry expression have the same limit behaviour
  (Corollary 6.2).

For points the budget is `(Nat.bits r).length ≤ log₂ r + 1`, so the hypotheses hold as soon as
`log (s k) / r k → 0` (`LogComparablyDivergent`, Definition 6.1), in particular for comparably
divergent sequences, `0 < liminf r/s ≤ limsup r/s < ∞` (`ComparablyDivergent`, Definition 1.10),
stated here through eventual two-sided bounds on the ratio
(`tendsto_bits_length_div_of_log_div`, `ComparablyDivergent.logComparablyDivergent`).
Blueprint nodes `split:normalized`, `split:comparable`.
-/

namespace Kolmogorov.PointToSet

open Filter Topology

/-! ### Divergence conditions on sequences of precisions -/

/-- Two sequences of precisions are **comparably divergent** (Definition 1.10 of the notes) when
both tend to infinity and their ratio is eventually bounded above and below by positive
constants. Blueprint node `split:comparable`. -/
def ComparablyDivergent (r s : ℕ → ℕ) : Prop :=
  Tendsto r atTop atTop ∧ Tendsto s atTop atTop ∧
    ∃ c C : ℝ, 0 < c ∧ ∀ᶠ k in atTop, c ≤ (r k : ℝ) / s k ∧ (r k : ℝ) / s k ≤ C

/-- Two sequences of precisions are **log-comparably divergent** (Definition 6.1 of the notes)
when both tend to infinity and the logarithm of each is negligible against the other.
Blueprint node `split:comparable`. -/
def LogComparablyDivergent (r s : ℕ → ℕ) : Prop :=
  Tendsto r atTop atTop ∧ Tendsto s atTop atTop ∧
    Tendsto (fun k => Real.log (s k) / r k) atTop (𝓝 0) ∧
    Tendsto (fun k => Real.log (r k) / s k) atTop (𝓝 0)

/-- The logarithm of a sequence tending to infinity is negligible against the sequence. -/
theorem tendsto_log_div_self_nat {r : ℕ → ℕ} (hr : Tendsto r atTop atTop) :
    Tendsto (fun k => Real.log (r k) / r k) atTop (𝓝 0) := by
  have h : Tendsto (fun k => ((r k : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hr
  have h0 := (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp h
  refine h0.congr' (Eventually.of_forall fun k => ?_)
  simp [Function.comp]

/-- Comparable divergence implies log-comparable divergence. Blueprint node `split:comparable`. -/
theorem ComparablyDivergent.logComparablyDivergent {r s : ℕ → ℕ} (h : ComparablyDivergent r s) :
    LogComparablyDivergent r s := by
  obtain ⟨hr, hs, c, C, hc, hev⟩ := h
  refine ⟨hr, hs, ?_, ?_⟩
  · -- `log s / r = (log s / s) · (s / r)`, and `s / r ≤ 1 / c` eventually.
    have hlog := tendsto_log_div_self_nat hs
    have hbound : ∀ᶠ k in atTop, |Real.log (s k) / r k| ≤ |Real.log (s k) / s k| * (1 / c) := by
      filter_upwards [hev, hs.eventually_gt_atTop 0, hr.eventually_gt_atTop 0] with k hk hsk hrk
      have hsk' : (0 : ℝ) < s k := by exact_mod_cast hsk
      have hrk' : (0 : ℝ) < r k := by exact_mod_cast hrk
      have hratio : (s k : ℝ) / r k ≤ 1 / c := by
        rw [div_le_div_iff₀ hrk' hc]
        have := hk.1
        rw [le_div_iff₀ hsk'] at this
        linarith
      have heq : Real.log (s k) / r k = Real.log (s k) / s k * ((s k : ℝ) / r k) := by
        field_simp
      rw [heq, abs_mul, abs_of_pos (div_pos hsk' hrk')]
      exact mul_le_mul_of_nonneg_left hratio (abs_nonneg _)
    refine squeeze_zero_norm' hbound ?_
    simpa using (hlog.abs).mul_const (1 / c)
  · have hlog := tendsto_log_div_self_nat hr
    have hbound : ∀ᶠ k in atTop, |Real.log (r k) / s k| ≤ |Real.log (r k) / r k| * C := by
      filter_upwards [hev, hs.eventually_gt_atTop 0, hr.eventually_gt_atTop 0] with k hk hsk hrk
      have hsk' : (0 : ℝ) < s k := by exact_mod_cast hsk
      have hrk' : (0 : ℝ) < r k := by exact_mod_cast hrk
      have heq : Real.log (r k) / s k = Real.log (r k) / r k * ((r k : ℝ) / s k) := by
        field_simp
      rw [heq, abs_mul, abs_of_pos (div_pos hrk' hsk')]
      exact mul_le_mul_of_nonneg_left hk.2 (abs_nonneg _)
    refine squeeze_zero_norm' hbound ?_
    simpa using (hlog.abs).mul_const C

/-- The binary length is at most `log₂ n + 1` for positive `n`. -/
theorem bits_length_le_logb (n : ℕ) (hn : 0 < n) :
    ((Nat.bits n).length : ℝ) ≤ Real.logb 2 n + 1 := by
  rw [Nat.size_eq_bits_len]
  have hpos : 0 < n.size := Nat.size_pos.mpr hn
  have h2 : 2 ^ (n.size - 1) ≤ n := Nat.lt_size.mp (by omega)
  have h2' : ((2 : ℝ) ^ (n.size - 1)) ≤ n := by exact_mod_cast h2
  have hlogpow : Real.logb 2 ((2 : ℝ) ^ (n.size - 1)) = ((n.size - 1 : ℕ) : ℝ) := by
    rw [Real.logb_pow, Real.logb_self_eq_one (by norm_num), mul_one]
  have hlog : ((n.size - 1 : ℕ) : ℝ) ≤ Real.logb 2 n := by
    rw [← hlogpow]
    exact Real.logb_le_logb_of_le (by norm_num) (by positivity) h2'
  have hcast : ((n.size - 1 : ℕ) : ℝ) = (n.size : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]; simp
  linarith

/-- Along a sequence with `log (s k) / N k → 0` and `N k → ∞`, the binary lengths of `s k` are
negligible against `N k`. Blueprint node `split:comparable`. -/
theorem tendsto_bits_length_div_of_log_div {s : ℕ → ℕ} {N : ℕ → ℝ} (hN : Tendsto N atTop atTop)
    (hs : Tendsto s atTop atTop) (h : Tendsto (fun k => Real.log (s k) / N k) atTop (𝓝 0)) :
    Tendsto (fun k => ((Nat.bits (s k)).length : ℝ) / N k) atTop (𝓝 0) := by
  have hinv : Tendsto (fun k => 1 / N k) atTop (𝓝 0) := tendsto_const_nhds.div_atTop hN
  have hlim : Tendsto (fun k => (Real.log (s k) / N k) / Real.log 2 + 1 / N k) atTop (𝓝 0) := by
    simpa using (h.div_const (Real.log 2)).add hinv
  have hbound : ∀ᶠ k in atTop, |((Nat.bits (s k)).length : ℝ) / N k| ≤
      (Real.log (s k) / N k) / Real.log 2 + 1 / N k := by
    filter_upwards [hs.eventually_gt_atTop 0, hN.eventually_gt_atTop 0] with k hsk hNk
    have hb := bits_length_le_logb (s k) hsk
    rw [abs_of_nonneg (div_nonneg (Nat.cast_nonneg _) hNk.le)]
    have heq : Real.log (s k) / N k / Real.log 2 + 1 / N k = (Real.logb 2 (s k) + 1) / N k := by
      rw [Real.logb, add_div, div_div, div_div, mul_comm]
    rw [heq]
    exact div_le_div_of_nonneg_right hb hNk.le
  exact squeeze_zero_norm' hbound hlim

/-! ### Normalized comparison for located families -/

namespace LocatedFamily

variable {A : Set ℕ} {ι₁ ι₂ : Type*} (L₁ : LocatedFamily A ι₁) (L₂ : LocatedFamily A ι₂)

/-- A quantity bounded by a multiple of the budgets is negligible against a scale dominating
both budgets. -/
theorem tendsto_div_of_budget_bound {r : ℕ → ι₁} {s : ℕ → ι₂} {N : ℕ → ℝ}
    (hN : Tendsto N atTop atTop)
    (h₁ : Tendsto (fun k => (L₁.budget (r k) : ℝ) / N k) atTop (𝓝 0))
    (h₂ : Tendsto (fun k => (L₂.budget (s k) : ℝ) / N k) atTop (𝓝 0))
    (f : ℕ → ℤ) (c : ℕ) (hf : ∀ k, |f k| ≤ c * (L₁.budget (r k) + L₂.budget (s k) + 1)) :
    Tendsto (fun k => (f k : ℝ) / N k) atTop (𝓝 0) := by
  have hinv : Tendsto (fun k => 1 / N k) atTop (𝓝 0) := tendsto_const_nhds.div_atTop hN
  have hlim : Tendsto (fun k => (c : ℝ) * ((L₁.budget (r k) : ℝ) / N k +
      (L₂.budget (s k) : ℝ) / N k + 1 / N k)) atTop (𝓝 0) := by
    simpa using ((h₁.add h₂).add hinv).const_mul (c : ℝ)
  refine squeeze_zero_norm' ?_ hlim
  filter_upwards [hN.eventually_gt_atTop 0] with k hNk
  have hfk := hf k
  have hfk' : |(f k : ℝ)| ≤ c * ((L₁.budget (r k) : ℝ) + L₂.budget (s k) + 1) := by
    have : ((|f k| : ℤ) : ℝ) ≤ ((c * (L₁.budget (r k) + L₂.budget (s k) + 1) : ℕ) : ℝ) := by
      exact_mod_cast hfk
    push_cast at this
    simpa using this
  rw [Real.norm_eq_abs, abs_div, abs_of_pos hNk, div_le_iff₀ hNk]
  calc |(f k : ℝ)| ≤ c * ((L₁.budget (r k) : ℝ) + L₂.budget (s k) + 1) := hfk'
    _ = (c : ℝ) * ((L₁.budget (r k) : ℝ) / N k + (L₂.budget (s k) : ℝ) / N k + 1 / N k) * N k := by
      field_simp

/-- **Normalized comparison** (Corollary 1.11 of the notes): along precisions whose budgets are
negligible against the scale `N`, `(J - I) / N → 0`. Blueprint node `split:normalized`. -/
theorem tendsto_minInfo_sub_splitInfo_div (hA : OracleSymmetryLower A) {r : ℕ → ι₁} {s : ℕ → ι₂}
    {N : ℕ → ℝ} (hN : Tendsto N atTop atTop)
    (h₁ : Tendsto (fun k => (L₁.budget (r k) : ℝ) / N k) atTop (𝓝 0))
    (h₂ : Tendsto (fun k => (L₂.budget (s k) : ℝ) / N k) atTop (𝓝 0)) :
    Tendsto (fun k => ((L₁.minInfo L₂ (r k) (s k) - L₁.splitInfo L₂ (r k) (s k) : ℤ) : ℝ) / N k)
      atTop (𝓝 0) := by
  obtain ⟨c, hc⟩ := L₁.minInfo_le_splitInfo_add L₂ hA
  refine L₁.tendsto_div_of_budget_bound L₂ hN h₁ h₂ _ c fun k => ?_
  have h1 := hc (r k) (s k)
  have h2 := L₁.splitInfo_le_minInfo L₂ (r k) (s k)
  rw [abs_le]
  constructor <;> omega

/-- **Normalized symmetry of information** (Corollary 6.2 of the notes): along precisions whose
budgets are negligible against the scale `N`,
`(I - (K₁ + K₂ - K₁₂)) / N → 0`. Blueprint node `split:normalized`. -/
theorem tendsto_splitInfo_sub_symmetry_div (hA : OracleSymmetryLower A) {r : ℕ → ι₁}
    {s : ℕ → ι₂} {N : ℕ → ℝ} (hN : Tendsto N atTop atTop)
    (h₁ : Tendsto (fun k => (L₁.budget (r k) : ℝ) / N k) atTop (𝓝 0))
    (h₂ : Tendsto (fun k => (L₂.budget (s k) : ℝ) / N k) atTop (𝓝 0)) :
    Tendsto (fun k => ((L₁.splitInfo L₂ (r k) (s k) -
      ((L₁.complexity (r k) : ℤ) + L₂.complexity (s k) -
        (L₁.prod hA L₂).complexity (r k, s k)) : ℤ) : ℝ) / N k) atTop (𝓝 0) := by
  obtain ⟨c, hc⟩ := L₁.splitInfo_symmetry L₂ hA
  refine L₁.tendsto_div_of_budget_bound L₂ hN h₁ h₂ _ c fun k => ?_
  obtain ⟨h1, h2⟩ := hc (r k) (s k)
  rw [abs_le]
  constructor <;> omega

end LocatedFamily

end Kolmogorov.PointToSet
