/-
Copyright (c) 2026 Emma Dinowitz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emma Dinowitz
-/
import KolmogorovMathlib.AlgorithmicRandomness.VanLambalgen.Countable.Defs
import KolmogorovMathlib.AlgorithmicRandomness.Relative.Basic

/-!
# Splitting one coordinate off an infinite join

The countable van Lambalgen theorem reduces to the binary one by splitting the `i`-th coordinate
off: the infinite join `⊕ⱼ xⱼ` and the pair `(⊕_{j ≠ i} xⱼ) ⊕ xᵢ` are related by a computable
permutation of positions that carries `piJoinMeasure μ` to the joined product of the product of
the other measures with `μ i`, so one is random exactly when the other is. The oracle of the other
coordinates, reindexed (`cantorPiJoinSkip`), is Turing equivalent to the infinite join with the
`i`-th coordinate blanked (`cantorPiJoinExcept`), which in turn computes the coordinates below `i`
(`cantorPiJoinBelow`).

## Conventions

The measures `μ i` are probability measures, so that `Measure.infinitePi μ` is their product.
Randomness is `IsMartinLofRandomIn`, relative to an arbitrary oracle `A`.

## Main declarations

* `exists_cantorPiJoin_eq` (blueprint node `vl:pi-join`): every sequence is an infinite join.
* `isProbabilityMeasure_piJoinMeasure` (blueprint node `vl:pi-join-measure`): the countable product
  of probability measures is a probability measure.
* `isMartinLofRandomIn_cantorPiJoin_iff_split` (blueprint node `vl:pi-split`): `⊕ⱼ xⱼ` is random for
  `piJoinMeasure μ` exactly when `(⊕_{j ≠ i} xⱼ) ⊕ xᵢ` is random for the joined product.
* `isMartinLofRandomIn_oracleJoin_cantorPiJoinSkip_iff`,
  `charOracle_oracleJoin_cantorPiJoinBelow_le` (blueprint node `vl:pi-oracles`): the reindexed and
  the blanked oracles of the other coordinates give the same relative randomness, and the oracle
  of the earlier coordinates is reducible to them.

Used by `AlgorithmicRandomness/VanLambalgen/MainResults.lean`.
-/

namespace Kolmogorov

open MeasureTheory
open PointToSet (oracleJoin)
open scoped Computability

variable {A : Set ℕ} {μ : ℕ → Measure CantorSeq} {x : ℕ → CantorSeq}

/-- Every sequence is an infinite join: of its columns `j ↦ (k ↦ z (pair j k))`.
Blueprint node `vl:pi-join`. -/
theorem exists_cantorPiJoin_eq (z : CantorSeq) : ∃ x, cantorPiJoin x = z := by
  sorry -- blueprint node `vl:pi-join`

/-- The countable product of probability measures, carried by the infinite join, is a probability
measure. Blueprint node `vl:pi-join-measure`. -/
instance isProbabilityMeasure_piJoinMeasure [∀ i, IsProbabilityMeasure (μ i)] :
    IsProbabilityMeasure (piJoinMeasure μ) := by
  sorry -- blueprint node `vl:pi-join-measure`

/-- Splitting the `i`-th coordinate off: `⊕ⱼ xⱼ` is random for `piJoinMeasure μ` relative to `A`
exactly when `(⊕_{j ≠ i} xⱼ) ⊕ xᵢ` is random relative to `A` for the joined product of the
product of the other measures with `μ i`. Blueprint node `vl:pi-split`. -/
theorem isMartinLofRandomIn_cantorPiJoin_iff_split [∀ i, IsProbabilityMeasure (μ i)] (i : ℕ) :
    IsMartinLofRandomIn A (piJoinMeasure μ) (cantorPiJoin x) ↔
      IsMartinLofRandomIn A (joinMeasure (piJoinMeasure fun j => μ (skipIndex i j)) (μ i))
        (cantorJoin (cantorPiJoinSkip x i) (x i)) := by
  sorry -- blueprint node `vl:pi-split`

/-- The reindexed and the blanked oracles of the coordinates other than the `i`-th are Turing
equivalent, so randomness relative to `A` joined with either is the same.
Blueprint node `vl:pi-oracles`. -/
theorem isMartinLofRandomIn_oracleJoin_cantorPiJoinSkip_iff {ν : Measure CantorSeq}
    {w : CantorSeq} (i : ℕ) :
    IsMartinLofRandomIn (oracleJoin A (seqOracle (cantorPiJoinSkip x i))) ν w ↔
      IsMartinLofRandomIn (oracleJoin A (seqOracle (cantorPiJoinExcept x i))) ν w := by
  sorry -- blueprint node `vl:pi-oracles`

/-- The coordinates before the `i`-th are computable from the coordinates other than the `i`-th:
`A ⊕ (⊕_{j < i} xⱼ)` is Turing reducible to `A ⊕ (⊕_{j ≠ i} xⱼ)`.
Blueprint node `vl:pi-oracles`. -/
theorem charOracle_oracleJoin_cantorPiJoinBelow_le (i : ℕ) :
    charOracle (oracleJoin A (seqOracle (cantorPiJoinBelow x i))) ≤ᵀ
      charOracle (oracleJoin A (seqOracle (cantorPiJoinExcept x i))) := by
  sorry -- blueprint node `vl:pi-oracles`

end Kolmogorov
