/-
Copyright (c) 2026 Emma Dinowitz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emma Dinowitz
-/
import KolmogorovMathlib.Oracle.PrefixComplexity.SymmetryLower

/-!
# The asymmetric convention for mutual information

Case and Lutz define the mutual information of two strings as `I(p : q) = K(q) - K(q | p)`:
the *second* argument is described, the first is the condition.  This file records that
convention (`oracleMutualInfoCL`), compares it with the symmetric convention
`oracleMutualInfo u v = K(u) + K(v) - K(⟨u, v⟩)` of
`KolmogorovMathlib.Oracle.PrefixComplexity.Information`, and proves Case–Lutz's Corollary 4.7
in their orientation,
`I(x : y) ≥ K(z) - K(z | x, K(x)) - K(z | y, K(y)) - K(K(x)) - K(K(z)) - O(1)`
(`oracleMutualInfoCL_ge_common`).

The two conventions satisfy `I_CL(u : v) ≤ I(u : v) + O(1)` and
`I(u : v) ≤ I_CL(u : v) + K(K(u)) + O(1)`, so they agree up to `K(K(u))`; at `K`-minimizers of
balls of radius `2⁻ʳ` this is `O(log r)`.  With the roles of the arguments swapped, i.e. for
`K(u) - K(u | v)`, the Case–Lutz inequality fails (the difference to the symmetric convention is
then `K(K(v) | v)`, which is unbounded by Gács's theorem), which is why the split-precision
theory uses the symmetric convention.  Blueprint node `split:mutual-information`.
-/

namespace Kolmogorov.PointToSet

variable (A : Set ℕ)

/-- Mutual information in the Case–Lutz convention: `I(u : v) = K(v) - K(v | u)`.
Blueprint node `split:mutual-information`. -/
noncomputable def oracleMutualInfoCL (u v : BitString) : ℤ :=
  (oracleComplexity A v : ℤ) - oraclePrefixComplexityNat A v u

/-- The Case–Lutz mutual information is at most the symmetric one, up to a constant.
Blueprint node `split:mutual-information`. -/
theorem oracleMutualInfoCL_le :
    ∃ c : ℕ, ∀ u v : BitString, oracleMutualInfoCL A u v ≤ oracleMutualInfo A u v + c := by
  obtain ⟨c₁, h₁⟩ := oraclePrefixComplexityNat_context_le A
  obtain ⟨c₂, h₂⟩ := oracleMutualInfo_ge_cond A
  refine ⟨c₁ + c₂, fun u v => ?_⟩
  have a1 := h₁ v u (oracleComplexity A u)
  have a2 := h₂ u v
  unfold oracleMutualInfoCL
  omega

/-- The symmetric mutual information exceeds the Case–Lutz one by at most `K(K(u)) + O(1)`.
Blueprint node `split:mutual-information`. -/
theorem oracleMutualInfo_le_CL_add :
    ∃ c : ℕ, ∀ u v : BitString,
      oracleMutualInfo A u v ≤
        oracleMutualInfoCL A u v + oracleComplexity A (natCode (oracleComplexity A u)) + c := by
  obtain ⟨c₁, h₁⟩ := oraclePrefixComplexityNat_le_context_add A
  obtain ⟨c₂, h₂⟩ := oracleMutualInfo_le_cond A (oracleSymmetryLower A)
  refine ⟨c₁ + c₂, fun u v => ?_⟩
  have a1 := h₁ v u (oracleComplexity A u)
  have a2 := h₂ u v
  unfold oracleMutualInfoCL
  omega

/-- **Case–Lutz, Corollary 4.7** (in their orientation): for all strings `x, y, z`,
`I(x : y) ≥ K(z) - K(z | x, K(x)) - K(z | y, K(y)) - K(K(x)) - K(K(z)) - O(1)` where
`I(x : y) = K(y) - K(y | x)`. Blueprint node `split:mutual-information`. -/
theorem oracleMutualInfoCL_ge_common :
    ∃ c : ℕ, ∀ x y z : BitString,
      (oracleComplexity A z : ℤ) -
        oraclePrefixComplexityNat A z (prefixComplexityContext x (oracleComplexity A x)) -
        oraclePrefixComplexityNat A z (prefixComplexityContext y (oracleComplexity A y)) -
        oracleComplexity A (natCode (oracleComplexity A x)) -
        oracleComplexity A (natCode (oracleComplexity A z)) - c ≤
          oracleMutualInfoCL A x y := by
  obtain ⟨c₁, h₁⟩ := oracleComplexity_pair_le_cond_context A
  obtain ⟨c₂, h₂⟩ := (oracleSymmetryLower A).bound
  obtain ⟨c₃, h₃⟩ := oracleComplexity_pair_swap_le A
  obtain ⟨c₄, h₄⟩ := oraclePrefixComplexityNat_triangle A
  obtain ⟨c₅, h₅⟩ := oraclePrefixComplexityNat_le_context_add A
  refine ⟨c₁ + c₂ + c₃ + c₄ + 2 * c₅, fun x y z => ?_⟩
  -- `K(y) ≤ K(z) + K(y | z, K(z)) - K(z | y, K(y)) + O(1)` by both directions of symmetry.
  have a1 := h₁ y z
  have a2 := h₂ z y
  have a3 := h₃ y z
  -- `K(y | x) ≤ K(z | x, K(x)) + K(K(x)) + K(y | z, K(z)) + K(K(z)) + O(1)` by the chain rule.
  have a4 := h₄ y z x
  have a5 := h₅ y z (oracleComplexity A z)
  have a6 := h₅ z x (oracleComplexity A x)
  unfold oracleMutualInfoCL
  omega

end Kolmogorov.PointToSet
