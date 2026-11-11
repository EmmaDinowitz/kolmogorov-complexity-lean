/-
Copyright (c) 2026 Emma Dinowitz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emma Dinowitz
-/
import KolmogorovMathlib.PointToSet.SplitPrecision.Euclidean
import KolmogorovMathlib.PointToSet.SplitPrecision.Theorems

/-!
# Mutual information at split precisions in Euclidean space

The theorems of `KolmogorovMathlib.PointToSet.SplitPrecision.Theorems` for points
`x ∈ ℝⁿ`, `y ∈ ℝᵗ` (as `Fin n → ℝ`, `Fin t → ℝ` with the sup metric and rational ideal points,
`euclidPresentation`): the geometric hypotheses are discharged by `euclidNets` and
`hasLinearGrowth_euclid`, so the theorems hold for every oracle without further hypotheses.

* `euclid_minimizerMutualInfo_le_splitMutualInfo_add`: Theorem 1.8 of the notes,
  `J_{r,s}(x : y) ≤ I_{r,s}(x : y) + O(log r) + O(log s)`;
* `euclid_splitMutualInfo_symmetry`: Theorem 4.4 for two points,
  `I_{r,s}(x : y) = K_r(x) + K_s(y) - K_{r,s}(x, y) + O(log r) + O(log s)`.

Blueprint node `split:euclidean`.
-/

namespace Kolmogorov.PointToSet

variable {n t : ℕ} {A : Set ℕ} (x : Fin n → ℝ) (y : Fin t → ℝ)

/-- **Theorem 1.8 in Euclidean space**: for `x ∈ ℝⁿ`, `y ∈ ℝᵗ` and every oracle `A`,
`J_{r,s}(x : y) ≤ I_{r,s}(x : y) + O(log r) + O(log s)`. Blueprint node `split:euclidean`. -/
theorem euclid_minimizerMutualInfo_le_splitMutualInfo_add :
    ∃ c : ℕ, ∀ r s : ℕ,
      minimizerMutualInfo (euclidPresentation n) (euclidPresentation t) A x y r s ≤
        splitMutualInfo (euclidPresentation n) (euclidPresentation t) A x y r s +
          c * ((Nat.bits r).length + (Nat.bits s).length + 1) :=
  minimizerMutualInfo_le_splitMutualInfo_add (euclidNets n A) (euclidNets t A)
    (hasLinearGrowth_euclid n A x) (hasLinearGrowth_euclid t A y)

/-- **Theorem 4.4 in Euclidean space**: for `x ∈ ℝⁿ`, `y ∈ ℝᵗ` and every oracle `A`,
`I_{r,s}(x : y) = K_r(x) + K_s(y) - K_{r,s}(x, y) + O(log r) + O(log s)`.
Blueprint node `split:euclidean`. -/
theorem euclid_splitMutualInfo_symmetry :
    ∃ c : ℕ, ∀ r s : ℕ,
      splitMutualInfo (euclidPresentation n) (euclidPresentation t) A x y r s ≤
        (precisionComplexityNat (euclidPresentation n) A x (dyadicRadius r) : ℤ) +
          precisionComplexityNat (euclidPresentation t) A y (dyadicRadius s) -
          jointPrecisionComplexity (euclidPresentation n) (euclidPresentation t) A x y r s +
          c * ((Nat.bits r).length + (Nat.bits s).length + 1) ∧
      (precisionComplexityNat (euclidPresentation n) A x (dyadicRadius r) : ℤ) +
          precisionComplexityNat (euclidPresentation t) A y (dyadicRadius s) -
          jointPrecisionComplexity (euclidPresentation n) (euclidPresentation t) A x y r s ≤
        splitMutualInfo (euclidPresentation n) (euclidPresentation t) A x y r s +
          c * ((Nat.bits r).length + (Nat.bits s).length + 1) :=
  splitMutualInfo_symmetry (euclidNets n A) (euclidNets t A)
    (hasLinearGrowth_euclid n A x) (hasLinearGrowth_euclid t A y)

end Kolmogorov.PointToSet
