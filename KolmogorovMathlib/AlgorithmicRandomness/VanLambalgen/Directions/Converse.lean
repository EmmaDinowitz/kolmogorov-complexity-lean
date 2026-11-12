/-
Copyright (c) 2026 Emma Dinowitz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emma Dinowitz
-/
import KolmogorovMathlib.AlgorithmicRandomness.Relative.Basic
import KolmogorovMathlib.AlgorithmicRandomness.VanLambalgen.Defs

/-!
# van Lambalgen: relatively random coordinates make a random pair

`IsMartinLofRandomIn.cantorJoin` (blueprint node `vl:converse`): if `x` is random for `μ` relative
to `A`, `y` is random for `ν` relative to `A ⊕ x` and `ν` is computable relative to `A`, then
`x ⊕ y` is random for `joinMeasure μ ν` relative to `A`. For a test `W` for pairs, the sets
`U_n = {x' | ν(W_{2n}^{x'}) > 2^{-n}}` of large sections form a test relative to `A` (Markov's
inequality and Fubini); `x` avoids `U_n` for all large `n`, and the sections of `W` at `x`,
trimmed relative to `A ⊕ x`, form a test that `y` would fail. No hypothesis on `μ`.

Used by `AlgorithmicRandomness/VanLambalgen/MainResults.lean`.
-/

namespace Kolmogorov

open MeasureTheory ENNReal
open PointToSet (oracleJoin)

variable {A : Set ℕ} {μ ν : Measure CantorSeq} {x y : CantorSeq}

/-- If `x` is random for `μ` relative to `A` and `y` is random for `ν` relative to `A ⊕ x`, then
the interleaving `x ⊕ y` is random for `joinMeasure μ ν` relative to `A`.
Blueprint node `vl:converse`. -/
theorem IsMartinLofRandomIn.cantorJoin (hν : IsComputableCantorMeasureIn A ν)
    (hx : IsMartinLofRandomIn A μ x) (hy : IsMartinLofRandomIn (oracleJoin A (seqOracle x)) ν y) :
    IsMartinLofRandomIn A (joinMeasure μ ν) (cantorJoin x y) := by
  sorry -- blueprint node `vl:converse`

end Kolmogorov
