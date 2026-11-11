# Mutual information at split precisions: blueprint and its Lean formalization

This file maps the statements of the note *Mutual information at split precisions* (the
appendix of the second point-to-set paper and the outline of the standalone note, Emma
Dinowitz, 2026) to the Lean declarations that formalize them.  The Lean docstrings carry the
same references (search for `Blueprint node \`split:` in `KolmogorovMathlib/Oracle/PrefixComplexity`
and `KolmogorovMathlib/PointToSet/SplitPrecision`).

## Conventions

* Paths are relative to `KolmogorovMathlib/`; every declaration lives in the namespace
  `Kolmogorov.PointToSet`.
* `K(x | y)` is `oraclePrefixComplexityNat A x y`, `K(x)` is `oracleComplexity A x`, for the
  fixed optimal oracle prefix machine `optimalOraclePrefix A` of an arbitrary oracle `A : Set ℕ`.
  The context "`x, K(x)`" is `prefixComplexityContext x (K(x)) = pairCode x (natCode (K(x)))`.
* **Convention for mutual information (decision, see Open decision 3 of the outline).**
  `I(u : v) = K(u) + K(v) - K(⟨u, v⟩)` (`oracleMutualInfo`, symmetric).  Case and Lutz define
  `I(p : q) = K(q) - K(q | p)`, with the *second* argument described; in that orientation their
  Corollary 4.7, `I(x : y) ≥ K(z) - K(z | x, K(x)) - K(z | y, K(y)) - K(K(x)) - K(K(z)) - O(1)`,
  is correct and is proved here as `oracleMutualInfoCL_ge_common`
  (`Oracle/PrefixComplexity/AsymmetricInformation.lean`, convention `oracleMutualInfoCL`).  The
  outline's convention `I(u : v) = K(u) - K(u | v)` has the roles swapped relative to the way
  inequality (2) is transcribed from Corollary 4.7, and under that swapped reading (2) is
  **false**: with `z = u` and `u = natCode (K(v))` it would bound `K(K(v) | v)` by
  `O(log log |v|)`, contradicting Gács's theorem.  The symmetric convention makes every string
  fact exact (`oracleMutualInfo_ge_common` has no `K(K(·))` term) and the comparison theorem
  needs neither (2) nor Step 2 of the appendix's proof.  The symmetric and Case–Lutz conventions
  differ by at most `K(K(u)) + O(1)` (`oracleMutualInfoCL_le`, `oracleMutualInfo_le_CL_add`),
  i.e. by `O(log r)` at minimizers, so every statement about points holds in either.
* **Symmetry of information for the oracle machine.** The lower (Levin–Gács) direction,
  `K(x) + K(y | x, K(x)) ≤ K(⟨x, y⟩) + O(1)`, is the predicate `OracleSymmetryLower A`, proved
  for every oracle by `oracleSymmetryLower` (`Oracle/PrefixComplexity/SymmetryLower.lean`): the
  marginal coding bound `oracle_pairMarginal_coding_bound` (the mass of the programs producing
  pairs with first component `x` is at most `2^{c} 2^{-K(x)}`, via a relatively enumerable
  threshold set and `oracle_kraftChaitin_bound`) and the context-uniform relative Kraft–Chaitin
  theorem `oracle_kraftChaitin_cond` (`Oracle/KraftChaitin.lean`).  The located-family layer
  still takes the predicate as a parameter (`LocatedFamily.prod`, `pointFamily`); the point and
  tuple theorems discharge it.
* **Error terms** are written `c * (budget₁ r + budget₂ s + 1)` with an existential constant
  `c`; for a point at precision `r` the budget is `(Nat.bits r).length`, the `O(log r)` of the
  note, and for a tuple it is the sum over the coordinates.  No step produces a joint term.
* **Ambient spaces.** Points live in presented metric spaces (`Presentation X`, a fixed dense
  sequence of ideal points) as in the rest of `PointToSet/`; names are codes `natBits i` of
  ideal points in dyadic balls.  The geometric input of the transfer lemmas is a
  `PrecisionNets` structure (an `A`-computable bounded family of candidates containing a
  canonical point of every ball) together with linear growth `K_r(x) ≤ C (r + 1)`.  Euclidean
  space is the instance of `SplitPrecision/Euclidean.lean`; a doubling space with computable
  nets is another instance, so Section 5 of the outline (pull-back along an Assouad embedding)
  is not needed.

## 1. String layer (`Oracle/PrefixComplexity/`)

* **`split:two-stage`** — the two-stage machine `twoStageMachine U g h` (`TwoStage.lean`):
  `TwoStageSpec`, `TwoStageSpec.eq_of_prefix`, `mem_twoStageMachine_iff`,
  `twoStageMachine_isPrefixMachine`, `twoStageMachine_produces`,
  `twoStageMachine_isDecompressorIn`; the bound `oraclePrefixComplexityNat_twoStage_le`.
* **`split:chain-rule`** — `oraclePrefixComplexityNat_triangle`
  (`K(x | z) ≤ K(y | z) + K(x | y) + O(1)`), `_triangle_pair`,
  `oraclePrefixComplexityNat_pair_le_cond_context` and `oracleComplexity_pair_le_cond_context`
  (coding direction of symmetry of information), `oraclePrefixComplexityNat_pair_le_add`
  (conditional concatenation).
* **`split:recoding`** — `oraclePrefixComplexityNat_cond_le_of_partrecIn`,
  `oraclePrefixComplexityNat_map_le_of_partrecIn`, `oraclePrefixComplexityNat_map_cond_le`.
* **`split:conditional-calculus`** (`Conditional.lean`) — dropping, projecting and swapping
  conditions, the complexity-value context (`oraclePrefixComplexityNat_context_le`,
  `_le_context_add`, `_context_self_le`), pairs, self-information, and the logarithmic bounds
  `oracleNatComplexity_le_bits`, `oracleComplexity_natCode_le`.
* **`split:symmetry-lower`** (`Information.lean`, `SymmetryLower.lean`) — `OracleSymmetryLower`,
  `OracleSymmetryLower.of_partrec`, `oracleSymmetryLower_empty`; for every oracle:
  `oracle_pairMarginal_coding_bound`, `oracleSymmetryLower`, with `oracle_kraftChaitin_cond`
  (`Oracle/KraftChaitin.lean`, node `oracle:kc`).
* **`split:mutual-information`** — `oracleMutualInfo`, `neg_le_oracleMutualInfo`,
  `oracleMutualInfo_le_symm`, `oracleMutualInfo_ge_cond`, `oracleMutualInfo_le_cond`
  (string fact (1) of the outline), `oracleMutualInfo_ge_common` (string fact (2)); the
  Case–Lutz convention and their Corollary 4.7 itself (`AsymmetricInformation.lean`):
  `oracleMutualInfoCL`, `oracleMutualInfoCL_ge_common`, `oracleMutualInfoCL_le`,
  `oracleMutualInfo_le_CL_add`.

## 2. Located families (`PointToSet/SplitPrecision/Located.lean`)

* **`split:located`** — `IsMinName`, `minComplexity`, `exists_isMinName`,
  `IsMinName.minComplexity_eq`, the structure `LocatedFamily` (names, budget, `transfer`,
  `bits_le`) and `LocatedFamily.complexity`.
* **`split:transfer`** (Lemmas 1.3–1.5 / 3.1–3.3 of the notes, Remark 1.7: one-sided, the
  described object unconstrained) — `LocatedFamily.transfer_cond` (with the riding string
  `w`), `_transfer_cond'`, `_transfer_context` (decorated transfer), `_natCode_complexity_le`.
* **`split:product`** (Lemma 3.5 coordinatewise iteration and Lemma 4.3 joint versus marginal
  minimizers) — `LocatedFamily.prod`, `mem_prod_names`, `prod_budget`,
  `LocatedFamily.complexity_pair_min_le`, `LocatedFamily.prod_complexity_le`.

## 3. Mutual information at split precisions (`SplitPrecision/Information.lean`)

* **`split:definition`** (Definition 1.1 / 2.4, Notation 1.2 / 2.5, inequality (1)) —
  `LocatedFamily.splitInfo`, `minInfo`, `exists_splitInfo_eq`, `exists_minInfo_eq`,
  `splitInfo_le_minInfo`.
* **`split:comparison`** (Theorem 1.8 / 4.1) — `LocatedFamily.minInfo_le_splitInfo_add`.
* **`split:symmetry`** (Theorem 4.4, Corollary 4.5) — `LocatedFamily.splitInfo_symmetry`,
  `LocatedFamily.splitInfo_comm_le`.

## 4. Points and tuples

* **`split:point-family`**, **`split:nets`**, **`split:transfer-geometric`** (`Point.lean`) —
  `ballNames`, `minComplexity_ballNames`, `isMinName_ballNames_iff`, `PrecisionNets`,
  `HasLinearGrowth` (Observation 1.6 / 2.3), `PrecisionNets.canonical_cond_le`,
  `transfer_ballNames`, `pointFamily`, `pointFamily_complexity`.
* **`split:point-definition`**, **`split:point-comparison`**, **`split:point-symmetry`**,
  **`split:point-normalized`** (`Theorems.lean`) — `splitMutualInfo`, `minimizerMutualInfo`,
  `jointPrecisionComplexity`, `splitMutualInfo_le_minimizerMutualInfo`,
  `minimizerMutualInfo_le_splitMutualInfo_add` (Theorem 1.8), `splitMutualInfo_symmetry`
  (Theorem 4.4 for two points), `splitMutualInfo_comm_le` (Corollary 4.5),
  `tendsto_minimizerMutualInfo_sub_splitMutualInfo_div` (Corollary 1.11),
  `tendsto_splitMutualInfo_sub_symmetry_div` (Corollary 6.2).
* **`split:normalized`**, **`split:comparable`** (`Normalized.lean`) — `ComparablyDivergent`
  (Definition 1.10, through eventual bounds on the ratio), `LogComparablyDivergent`
  (Definition 6.1), `ComparablyDivergent.logComparablyDivergent`,
  `tendsto_bits_length_div_of_log_div`, `LocatedFamily.tendsto_minInfo_sub_splitInfo_div`,
  `LocatedFamily.tendsto_splitInfo_sub_symmetry_div`.
* **`split:pi`**, **`split:tuple-theorems`** (`Tuples.lean`) — `LocatedFamily.reindex`, `unit`,
  `pi`, `mem_pi_names`, `pi_budget`; `tupleNames`, `tuplePrecisionComplexity` (Definition 2.1),
  `tupleFamily`, `tupleSplitMutualInfo`, `tupleMinimizerMutualInfo`, `tupleJointComplexity`,
  `tupleMinimizerMutualInfo_le_tupleSplitMutualInfo_add` (Theorem 4.1),
  `tupleSplitMutualInfo_symmetry` (Theorem 4.4).
* **`split:euclidean`** (`Euclidean.lean`, `EuclideanTheorems.lean`) — `ℝⁿ` as `Fin n → ℝ`
  with the sup metric and the rational points (`ratPoint`, `ratPointIndex`) as ideal points:
  `euclidPresentation`, the exact rational distance table `ratSupDist` and
  `computablePresentationIn_euclid`, the dyadic truncation `dyadicTrunc` with the candidate
  function `euclidCand` and `euclidNets`, the linear bound `hasLinearGrowth_euclid`
  (Observation 1.6, through `oracle_tuple_bounds_composition` on the list of coordinate
  integers); the theorems for `x ∈ ℝⁿ`, `y ∈ ℝᵗ`:
  `euclid_minimizerMutualInfo_le_splitMutualInfo_add` (Theorem 1.8) and
  `euclid_splitMutualInfo_symmetry` (Theorem 4.4).

## 5. Not formalized

* Corollary 4.6 (the conditional form `K_{r̄,s̄}(x̄ | ȳ)` à la Lutz–Stull): its convention is an
  open decision of the outline.
* Section 5 of the outline (Assouad embeddings): replaced by the `PrecisionNets` interface,
  which any doubling space with computable nets satisfies directly.
