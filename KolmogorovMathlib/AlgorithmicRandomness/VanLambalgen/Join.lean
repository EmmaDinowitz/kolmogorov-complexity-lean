/-
Copyright (c) 2026 Emma Dinowitz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emma Dinowitz
-/
import KolmogorovMathlib.AlgorithmicRandomness.Relative.Basic
import KolmogorovMathlib.AlgorithmicRandomness.VanLambalgen.Defs

/-!
# Interleaving: oracles, the uniform measure and the swap

This module records how the interleaving `cantorJoin` interacts with oracles and measures:
the oracle of `x ⊕ y` is the oracle join of the oracles of `x` and `y`; the joined product of two
uniform measures is the uniform measure; and exchanging the two factors preserves randomness.

## Conventions

`cantorJoin x y` puts `x` on even positions, as `PointToSet.oracleJoin` puts its first argument
on even queries. The swap statement compares `joinMeasure μ ν` at `x ⊕ y` with `joinMeasure ν μ`
at `y ⊕ x`; it uses s-finiteness of both factors, which is what Mathlib's `Measure.prod_swap`
needs.

## Main declarations

* `seqOracle_cantorJoin` (blueprint node `vl:join-oracle`): `seqOracle (x ⊕ y)` is the oracle join
  of `seqOracle x` and `seqOracle y`.
* `exists_cantorJoin_eq` (blueprint node `vl:join`): every sequence is an interleaving.
* `joinMeasure_univ` (blueprint node `vl:join-measure`): the total mass of `joinMeasure μ ν` is
  `μ(univ) ν(univ)`.
* `joinMeasure_uniformMeasure` (blueprint node `vl:join-uniform`): the joined product of two
  uniform measures is the uniform measure.
* `isMartinLofRandomIn_joinMeasure_swap` (blueprint node `vl:swap`): `x ⊕ y` is random for
  `joinMeasure μ ν` relative to `A` if and only if `y ⊕ x` is random for `joinMeasure ν μ`.

Used by `AlgorithmicRandomness/VanLambalgen/MainResults.lean`.
-/

namespace Kolmogorov

open MeasureTheory
open PointToSet (oracleJoin)

variable {A : Set ℕ} {μ ν : Measure CantorSeq}

/-- The oracle of an interleaving is the oracle join of the oracles of its two halves.
Blueprint node `vl:join-oracle`. -/
theorem seqOracle_cantorJoin (x y : CantorSeq) :
    seqOracle (cantorJoin x y) = oracleJoin (seqOracle x) (seqOracle y) := by
  sorry -- blueprint node `vl:join-oracle`

/-- Every sequence is an interleaving: of its even-indexed and its odd-indexed subsequences.
Blueprint node `vl:join`. -/
theorem exists_cantorJoin_eq (z : CantorSeq) : ∃ x y, cantorJoin x y = z := by
  sorry -- blueprint node `vl:join`

/-- The total mass of the joined product is the product of the total masses.
Blueprint node `vl:join-measure`. -/
theorem joinMeasure_univ [SFinite ν] :
    joinMeasure μ ν Set.univ = μ Set.univ * ν Set.univ := by
  sorry -- blueprint node `vl:join-measure`

/-- The joined product of two uniform measures is the uniform measure.
Blueprint node `vl:join-uniform`. -/
theorem joinMeasure_uniformMeasure :
    joinMeasure uniformMeasure uniformMeasure = uniformMeasure := by
  sorry -- blueprint node `vl:join-uniform`

/-- Exchanging the two factors preserves randomness: `x ⊕ y` is random for `joinMeasure μ ν`
relative to `A` exactly when `y ⊕ x` is random for `joinMeasure ν μ` relative to `A`.
Blueprint node `vl:swap`. -/
theorem isMartinLofRandomIn_joinMeasure_swap [SFinite μ] [SFinite ν] {x y : CantorSeq} :
    IsMartinLofRandomIn A (joinMeasure μ ν) (cantorJoin x y) ↔
      IsMartinLofRandomIn A (joinMeasure ν μ) (cantorJoin y x) := by
  sorry -- blueprint node `vl:swap`

end Kolmogorov
