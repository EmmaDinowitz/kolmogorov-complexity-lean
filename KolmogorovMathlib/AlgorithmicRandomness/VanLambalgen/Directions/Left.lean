/-
Copyright (c) 2026 Emma Dinowitz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emma Dinowitz
-/
import KolmogorovMathlib.AlgorithmicRandomness.Relative.Basic
import KolmogorovMathlib.AlgorithmicRandomness.VanLambalgen.Defs

/-!
# van Lambalgen: a random pair has a random first coordinate

`IsMartinLofRandomIn.left_of_cantorJoin` (blueprint node `vl:fst`): if `x ⊕ y` is random for
`joinMeasure μ ν` relative to `A` and `ν` is finite, then `x` is random for `μ` relative to `A`.
A test `U` for `x` gives the test `{x' ⊕ y' | x' ∈ U_{n+c}}` for pairs, where `2^c` bounds
`ν(univ)`: its measure is `μ(U_{n+c}) ν(univ)` by `Measure.prod_prod`. No hypothesis on `μ`.

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

end Kolmogorov
