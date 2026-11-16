/-
Copyright (c) 2026 Emma Dinowitz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emma Dinowitz
-/
import KolmogorovMathlib.AlgorithmicRandomness.VanLambalgen.Metric.Countable.Defs

/-!
# The mixture dominates its members

`μ i ≤ 2^{i+1} • mixMeasure μ` for every `i` (`le_two_pow_smul_mixMeasure`), with no
measurability assumption. It is the one fact shared by the mixture and the product-basis files:
a boundary cover of mixture-measure `≤ 2^{-(n+i+1)}` has `μ i`-measure `≤ 2^{-n}`.

## Main declarations

* `le_two_pow_smul_mixMeasure` (blueprint node `vlm:mix`).

Used by `Metric/Countable/Mixture.lean` and `Metric/Countable/Basis.lean`.
-/

namespace Kolmogorov.PointToSet

open MeasureTheory
open scoped ENNReal

variable {X : Type*} [MeasurableSpace X]

/-- Each member of a sequence of measures is at most `2^{i+1}` times the mixture.
Blueprint node `vlm:mix`. -/
theorem le_two_pow_smul_mixMeasure (μ : ℕ → Measure X) (i : ℕ) :
    μ i ≤ (2 : ℝ≥0∞) ^ (i + 1) • mixMeasure μ := by
  rw [Measure.le_iff']
  intro s
  have h := Measure.le_iff'.1
    (Measure.le_sum (fun j => ((2 : ℝ≥0∞)⁻¹ ^ (j + 1)) • μ j) i) s
  rw [Measure.smul_apply, smul_eq_mul] at h
  rw [Measure.smul_apply, smul_eq_mul]
  calc μ i s = (2 : ℝ≥0∞) ^ (i + 1) * ((2 : ℝ≥0∞)⁻¹ ^ (i + 1) * μ i s) := by
        rw [← mul_assoc, ← mul_pow, ENNReal.mul_inv_cancel (by norm_num) (by norm_num),
          one_pow, one_mul]
    _ ≤ (2 : ℝ≥0∞) ^ (i + 1) * mixMeasure μ s := by
        gcongr
        exact h

end Kolmogorov.PointToSet
