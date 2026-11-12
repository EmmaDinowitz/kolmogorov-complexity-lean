/-
Copyright (c) 2026 Emma Dinowitz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emma Dinowitz
-/
import KolmogorovMathlib.AlgorithmicRandomness.Relative.Basic
import KolmogorovMathlib.AlgorithmicRandomness.VanLambalgen.Defs

/-!
# The three directions of the van Lambalgen theorem

For an oracle `A`, measures `μ`, `ν` on Cantor space and sequences `x`, `y`, the van Lambalgen
theorem compares randomness of the interleaving `x ⊕ y = cantorJoin x y` for the joined product
measure `joinMeasure μ ν` with randomness of `x` for `μ` relative to `A` and of `y` for `ν`
relative to `A ⊕ x = oracleJoin A (seqOracle x)`. This module proves the three implications
separately, each with the hypotheses it uses.

* `IsMartinLofRandomIn.left_of_cantorJoin` (blueprint node `vl:fst`): if `x ⊕ y` is random then
  `x` is. A test `U` for `x` gives the test `{x' ⊕ y' | x' ∈ U_n}` (shifted by a constant
  bounding `ν(univ)`).
* `IsMartinLofRandomIn.right_of_cantorJoin` (blueprint node `vl:snd`): if `x ⊕ y` is random then
  `y` is random relative to `A ⊕ x`. A test relative to `A ⊕ x` is trimmed uniformly in the oracle
  to a family `T^z` that is a `ν`-test for every oracle `z`; by the use principle
  `{z ⊕ y' | y' ∈ T^z_n}` is effectively open relative to `A`, and by Fubini its measure is at
  most `μ(univ) 2^{-n}`.
* `IsMartinLofRandomIn.cantorJoin` (blueprint node `vl:converse`): if `x` is random relative to
  `A` and `y` relative to `A ⊕ x`, then `x ⊕ y` is random. For a test `W`, the sets
  `U_n = {x' | ν(W_{2n}^{x'}) > 2^{-n}}` of large sections form a test relative to `A` (Markov's
  inequality and Fubini), `x` avoids `U_n` for all large `n`, and the sections of `W` at `x`,
  trimmed relative to `A ⊕ x`, form a test that `y` would fail.

## Hypotheses

Mathlib's `Measure.prod_prod` and `Measure.prod_apply` need s-finiteness of the second factor
only. Accordingly `vl:fst` assumes `ν` finite, `vl:converse` assumes `ν` computable relative to `A`
(which makes it finite), and `vl:snd` assumes in addition `μ` finite. No direction assumes `μ`
computable.

Used by `AlgorithmicRandomness/VanLambalgen/MainResults.lean`.
-/

namespace Kolmogorov

open MeasureTheory ENNReal
open PointToSet (oracleJoin)

variable {A : Set ℕ} {μ ν : Measure CantorSeq} {x y : CantorSeq}

/-- If the interleaving `x ⊕ y` is random for `joinMeasure μ ν` relative to `A`, then `x` is
random for `μ` relative to `A`. Blueprint node `vl:fst`. -/
theorem IsMartinLofRandomIn.left_of_cantorJoin [IsFiniteMeasure ν]
    (h : IsMartinLofRandomIn A (joinMeasure μ ν) (cantorJoin x y)) :
    IsMartinLofRandomIn A μ x := by
  sorry -- blueprint node `vl:fst`

/-- If the interleaving `x ⊕ y` is random for `joinMeasure μ ν` relative to `A`, then `y` is
random for `ν` relative to `A ⊕ x`. Blueprint node `vl:snd`. -/
theorem IsMartinLofRandomIn.right_of_cantorJoin [IsFiniteMeasure μ]
    (hν : IsComputableCantorMeasureIn A ν)
    (h : IsMartinLofRandomIn A (joinMeasure μ ν) (cantorJoin x y)) :
    IsMartinLofRandomIn (oracleJoin A (seqOracle x)) ν y := by
  sorry -- blueprint node `vl:snd`

/-- If `x` is random for `μ` relative to `A` and `y` is random for `ν` relative to `A ⊕ x`, then
the interleaving `x ⊕ y` is random for `joinMeasure μ ν` relative to `A`.
Blueprint node `vl:converse`. -/
theorem IsMartinLofRandomIn.cantorJoin (hν : IsComputableCantorMeasureIn A ν)
    (hx : IsMartinLofRandomIn A μ x) (hy : IsMartinLofRandomIn (oracleJoin A (seqOracle x)) ν y) :
    IsMartinLofRandomIn A (joinMeasure μ ν) (cantorJoin x y) := by
  sorry -- blueprint node `vl:converse`

end Kolmogorov
