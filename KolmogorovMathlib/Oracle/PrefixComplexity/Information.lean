/-
Copyright (c) 2026 Emma Dinowitz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emma Dinowitz
-/
import KolmogorovMathlib.Oracle.PrefixComplexity.Conditional
import KolmogorovMathlib.Prefix.ConditionalSymmetry

/-!
# Symmetry of information and mutual information for `K^A`

The coding direction of symmetry of information, `K(⟨x, y⟩) ≤ K(x) + K(y | x, K(x)) + O(1)`,
is `oracleComplexity_pair_le_cond_context`.  The reverse (Levin–Gács) direction,
`K(x) + K(y | x, K(x)) ≤ K(⟨x, y⟩) + O(1)`, is packaged here as the predicate
`OracleSymmetryLower A` on the oracle.  It is proved for every oracle in
`KolmogorovMathlib.Oracle.PrefixComplexity.SymmetryLower` (`oracleSymmetryLower`, through the
relative coding theorem and a context-uniform Kraft–Chaitin theorem); this file gives the direct
transport of the unrelativized theorem `KPPair_chain_lower` for oracles with a partial recursive
characteristic function (`OracleSymmetryLower.of_partrec`), in particular the empty oracle.

The mutual information of two strings is taken in the symmetric form
`I(u : v) = K(u) + K(v) - K(⟨u, v⟩)` (`oracleMutualInfo`).  With this convention

* `I(u : v) ≥ -O(1)` and `I(u : v) = I(v : u) + O(1)`;
* `I(u : v) = K(v) - K(v | u, K(u)) + O(1)` (`oracleMutualInfo_ge_cond`, the coding direction
  alone, and `oracleMutualInfo_le_cond`, which needs `OracleSymmetryLower A`);
* `I(u : v) ≥ K(z) - K(z | u, K(u)) - K(z | v, K(v)) - O(1)` for every `z`
  (`oracleMutualInfo_ge_common`), the form of Case–Lutz's Corollary 4.7 in which no
  `K(K(·))` terms appear.

The asymmetric convention `K(u) - K(u | v)` differs from the symmetric one by at most
`K(K(v) | v) + O(1)`, which is unbounded; the symmetric convention is the one under which the
string facts used by the split-precision theory hold with constant error.
Blueprint nodes `split:symmetry-lower`, `split:mutual-information`.
-/

namespace Kolmogorov.PointToSet

open scoped Computability

/-! ### The lower direction of symmetry of information -/

/-- The lower (Levin–Gács) direction of symmetry of information for the oracle `A`:
`K(x) + K(y | x, K(x)) ≤ K(⟨x, y⟩) + O(1)`. Blueprint node `split:symmetry-lower`. -/
structure OracleSymmetryLower (A : Set ℕ) : Prop where
  /-- The inequality, with its constant. -/
  bound : ∃ c : ℕ, ∀ x y : BitString,
    oracleComplexity A x +
      oraclePrefixComplexityNat A y (prefixComplexityContext x (oracleComplexity A x)) ≤
        oracleComplexity A (pairCode x y) + c

/-- For an oracle with partial recursive characteristic function the optimal oracle prefix
machine is an optimal prefix decompressor in the unrelativized sense, so the unrelativized
theorem `KPPair_chain_lower` transfers. Blueprint node `split:symmetry-lower`. -/
theorem OracleSymmetryLower.of_partrec (A : Set ℕ) (hA : Partrec (charOracle A)) :
    OracleSymmetryLower A := by
  obtain ⟨hUd, hUp, hopt⟩ := exists_optimalOraclePrefix_spec A
  set U := optimalOraclePrefix A with hUdef
  have hUpartrec : isDecompressor U := by
    have h : PartrecIn {charOracle A} U := (isDecompressorIn_iff_partrecIn _ _).mp hUd
    exact RecursiveIn.partrec_of_oracle
      (fun g hg => by rw [Set.mem_singleton_iff.mp hg]; exact hA) h
  have hopt' : IsOptimalPrefixConditional U := by
    refine ⟨⟨hUpartrec, hUp⟩, fun M hM => ?_⟩
    exact hopt M ((isDecompressorIn_iff_partrecIn _ _).mpr
      (relative_closure A M hM.isDecompressor)) hM.isPrefixMachine
  obtain ⟨c, hc⟩ := KPPair_chain_lower U hopt'
  refine ⟨c, fun x y => ?_⟩
  have hval : HasPrefixComplexityValue U x (oracleComplexity A x) :=
    oraclePrefixComplexity_coe A x []
  have h := hc x y _ hval
  have h1 : KPPlain U x = (oracleComplexity A x : ENat) :=
    (oraclePrefixComplexity_coe A x []).symm
  have h2 : KP U y (prefixComplexityContext x (oracleComplexity A x)) =
      (oraclePrefixComplexityNat A y (prefixComplexityContext x (oracleComplexity A x)) :
        ENat) :=
    (oraclePrefixComplexity_coe A y _).symm
  have h3 : KPPair U x y = (oracleComplexity A (pairCode x y) : ENat) :=
    (oraclePrefixComplexity_coe A (pairCode x y) []).symm
  rw [h1, h2, h3] at h
  exact_mod_cast h

/-- The empty oracle satisfies the lower direction of symmetry of information.
Blueprint node `split:symmetry-lower`. -/
theorem oracleSymmetryLower_empty : OracleSymmetryLower (∅ : Set ℕ) := by
  refine OracleSymmetryLower.of_partrec ∅ ?_
  have h : charOracle (∅ : Set ℕ) = ((fun _ => 0 : ℕ → ℕ) : ℕ →. ℕ) := by
    funext n
    simp [charOracle]
  rw [h]
  exact Computable.const 0

/-! ### Mutual information -/

variable (A : Set ℕ)

/-- Mutual information of two strings relative to `A`, in the symmetric convention
`I(u : v) = K(u) + K(v) - K(⟨u, v⟩)`. Blueprint node `split:mutual-information`. -/
noncomputable def oracleMutualInfo (u v : BitString) : ℤ :=
  (oracleComplexity A u : ℤ) + oracleComplexity A v - oracleComplexity A (pairCode u v)

/-- Mutual information is bounded below by a constant. Blueprint node
`split:mutual-information`. -/
theorem neg_le_oracleMutualInfo :
    ∃ c : ℕ, ∀ u v : BitString, -(c : ℤ) ≤ oracleMutualInfo A u v := by
  obtain ⟨c, hc⟩ := oracleComplexity_pair_le_add A
  refine ⟨c, fun u v => ?_⟩
  have := hc u v
  unfold oracleMutualInfo
  omega

/-- Mutual information is symmetric up to a constant. Blueprint node
`split:mutual-information`. -/
theorem oracleMutualInfo_le_symm :
    ∃ c : ℕ, ∀ u v : BitString, oracleMutualInfo A u v ≤ oracleMutualInfo A v u + c := by
  obtain ⟨c, hc⟩ := oracleComplexity_pair_swap_le A
  refine ⟨c, fun u v => ?_⟩
  have := hc u v
  unfold oracleMutualInfo
  omega

/-- The coding direction of symmetry of information gives
`K(v) - K(v | u, K(u)) - O(1) ≤ I(u : v)`. Blueprint node `split:mutual-information`. -/
theorem oracleMutualInfo_ge_cond :
    ∃ c : ℕ, ∀ u v : BitString,
      (oracleComplexity A v : ℤ) -
        oraclePrefixComplexityNat A v (prefixComplexityContext u (oracleComplexity A u)) - c ≤
          oracleMutualInfo A u v := by
  obtain ⟨c, hc⟩ := oracleComplexity_pair_le_cond_context A
  refine ⟨c, fun u v => ?_⟩
  have := hc u v
  unfold oracleMutualInfo
  omega

/-- The lower direction of symmetry of information gives
`I(u : v) ≤ K(v) - K(v | u, K(u)) + O(1)`. Blueprint node `split:mutual-information`. -/
theorem oracleMutualInfo_le_cond (hA : OracleSymmetryLower A) :
    ∃ c : ℕ, ∀ u v : BitString,
      oracleMutualInfo A u v ≤
        (oracleComplexity A v : ℤ) -
          oraclePrefixComplexityNat A v (prefixComplexityContext u (oracleComplexity A u)) + c := by
  obtain ⟨c, hc⟩ := hA.bound
  refine ⟨c, fun u v => ?_⟩
  have := hc u v
  unfold oracleMutualInfo
  omega

/-- **Common information lower bound** (Case–Lutz, Corollary 4.7, in the symmetric convention):
for every `z`, `I(u : v) ≥ K(z) - K(z | u, K(u)) - K(z | v, K(v)) - O(1)`.
Blueprint node `split:mutual-information`. -/
theorem oracleMutualInfo_ge_common (hA : OracleSymmetryLower A) :
    ∃ c : ℕ, ∀ u v z : BitString,
      (oracleComplexity A z : ℤ) -
        oraclePrefixComplexityNat A z (prefixComplexityContext u (oracleComplexity A u)) -
        oraclePrefixComplexityNat A z (prefixComplexityContext v (oracleComplexity A v)) - c ≤
          oracleMutualInfo A u v := by
  obtain ⟨c₁, hc₁⟩ := oracleComplexity_pair_le_cond_context A
  obtain ⟨c₂, hc₂⟩ := oracleComplexity_snd_le_pair A
  obtain ⟨c₃, hc₃⟩ := oraclePrefixComplexityNat_pair_le_add A
  obtain ⟨c₄, hc₄⟩ := hA.bound
  obtain ⟨c₅, hc₅⟩ := oracleComplexity_pair_swap_le A
  refine ⟨c₁ + c₂ + c₃ + 2 * (c₄ + c₅ + c₁), fun u v z => ?_⟩
  -- `K(⟨u, v⟩) ≤ K(z) + K(u | z, K(z)) + K(v | z, K(z)) + O(1)`.
  have hA1 := hc₁ z (pairCode u v)
  have hA2 := hc₂ z (pairCode u v)
  have hA3 := hc₃ u v (prefixComplexityContext z (oracleComplexity A z))
  -- `K(z) + K(u | z, K(z)) ≤ K(u) + K(z | u, K(u)) + O(1)`, and the same with `v`.
  have hBu1 := hc₄ z u
  have hBu2 := hc₅ u z
  have hBu3 := hc₁ u z
  have hBv1 := hc₄ z v
  have hBv2 := hc₅ v z
  have hBv3 := hc₁ v z
  unfold oracleMutualInfo
  omega

end Kolmogorov.PointToSet
