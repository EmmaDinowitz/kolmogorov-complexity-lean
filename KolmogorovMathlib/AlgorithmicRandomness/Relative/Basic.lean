/-
Copyright (c) 2026 Emma Dinowitz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emma Dinowitz
-/
import KolmogorovMathlib.AlgorithmicRandomness.Relative.Defs

/-!
# Basic properties of relative Martin-Löf randomness

This module proves the facts about `IsMartinLofRandomIn` that every use of it needs: randomness
relative to a stronger oracle implies randomness relative to a weaker one, randomness relative to
the empty oracle is the unrelativized `IsMartinLofRandom`, and almost every sequence is random.

## Conventions

Oracles are sets of natural numbers compared by Turing reducibility of their characteristic
functions, `charOracle A ≤ᵀ charOracle B`. Measures are arbitrary measures on `CantorSeq`; the
statements below need no finiteness.

## Main declarations

* `IsMartinLofRandomIn.mono_oracle` (blueprint node `vl:random-in-anti`): if `A ≤_T B`, every
  sequence random relative to `B` is random relative to `A`.
* `isMartinLofRandomIn_empty_iff` (blueprint node `vl:random-in-empty`): randomness relative to
  the empty oracle is `IsMartinLofRandom`.
* `measure_setOf_not_isMartinLofRandomIn` (blueprint node `vl:ae-random`): the non-random
  sequences form a `μ`-null set, for every measure `μ` and every oracle.
* `IsComputableMeasure.isComputableCantorMeasureIn`, `IsComputableCantorMeasureIn.isFiniteMeasure`
  (blueprint node `vl:computable-measure-in`): a computable measure is computable relative to
  every oracle, and a relatively computable measure is finite.

## Blind randomness

`IsMartinLofRandomIn A μ` quantifies over `A`-c.e. tests whose `μ`-measures are small; the tests
have no access to `μ`. When `μ` is not computable relative to `A` this is blind (Hippocratic)
randomness, not the notion in which tests may also query a representation of `μ`. When `μ` is
`A`-computable the two agree.

Used by `AlgorithmicRandomness/VanLambalgen/`.
-/

namespace Kolmogorov

open MeasureTheory ENNReal
open scoped Computability

variable {A B : Set ℕ} {μ : Measure CantorSeq}

/-- Randomness relative to a Turing-stronger oracle implies randomness relative to a weaker one.
Blueprint node `vl:random-in-anti`. -/
theorem IsMartinLofRandomIn.mono_oracle {w : CantorSeq} (hw : IsMartinLofRandomIn B μ w)
    (hAB : charOracle A ≤ᵀ charOracle B) : IsMartinLofRandomIn A μ w := by
  sorry -- blueprint node `vl:random-in-anti`

/-- Joining the empty oracle on the left does not change randomness: `∅ ⊕ B` and `B` are Turing
equivalent. Blueprint node `vl:random-in-anti`. -/
theorem isMartinLofRandomIn_oracleJoin_empty_left {w : CantorSeq} :
    IsMartinLofRandomIn (PointToSet.oracleJoin ∅ B) μ w ↔ IsMartinLofRandomIn B μ w := by
  sorry -- blueprint node `vl:random-in-anti`

/-- Randomness relative to the empty oracle is unrelativized Martin-Löf randomness.
Blueprint node `vl:random-in-empty`. -/
theorem isMartinLofRandomIn_empty_iff {w : CantorSeq} :
    IsMartinLofRandomIn ∅ μ w ↔ IsMartinLofRandom μ w := by
  sorry -- blueprint node `vl:random-in-empty`

/-- For every measure and every oracle, the sequences that are not random relative to the oracle
form a null set. Blueprint node `vl:ae-random`. -/
theorem measure_setOf_not_isMartinLofRandomIn (A : Set ℕ) (μ : Measure CantorSeq) :
    μ {w | ¬ IsMartinLofRandomIn A μ w} = 0 := by
  sorry -- blueprint node `vl:ae-random`

/-! ### Computable measures relative to an oracle -/

/-- A computable measure is computable relative to every oracle.
Blueprint node `vl:computable-measure-in`. -/
theorem IsComputableMeasure.isComputableCantorMeasureIn (hμ : IsComputableMeasure μ)
    (A : Set ℕ) : IsComputableCantorMeasureIn A μ := by
  sorry -- blueprint node `vl:computable-measure-in`

/-- A measure computable relative to some oracle is finite: the mass of the empty cylinder,
which is the whole space, is within `1` of a dyadic rational.
Blueprint node `vl:computable-measure-in`. -/
theorem IsComputableCantorMeasureIn.isFiniteMeasure (hμ : IsComputableCantorMeasureIn A μ) :
    IsFiniteMeasure μ := by
  sorry -- blueprint node `vl:computable-measure-in`

end Kolmogorov
