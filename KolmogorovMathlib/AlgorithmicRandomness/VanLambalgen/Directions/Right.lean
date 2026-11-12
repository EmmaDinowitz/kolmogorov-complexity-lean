/-
Copyright (c) 2026 Emma Dinowitz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emma Dinowitz
-/
import KolmogorovMathlib.AlgorithmicRandomness.Relative.Basic
import KolmogorovMathlib.AlgorithmicRandomness.VanLambalgen.Defs

/-!
# van Lambalgen: a random pair has a second coordinate random relative to the first

`IsMartinLofRandomIn.right_of_cantorJoin` (blueprint node `vl:snd`): if `x ⊕ y` is random for
`joinMeasure μ ν` relative to `A`, `μ` is finite and `ν` is computable relative to `A`, then `y`
is random for `ν` relative to `A ⊕ x`. A test relative to `A ⊕ x` is trimmed uniformly in the
oracle to a family `T^z` that is a `ν`-test for every oracle `z`; by the use principle
`{z ⊕ y' | y' ∈ T^z_n}` is effectively open relative to `A`, and by Fubini its measure is at most
`μ(univ) 2^{-n}`.

Used by `AlgorithmicRandomness/VanLambalgen/MainResults.lean`.
-/

namespace Kolmogorov

open MeasureTheory ENNReal
open PointToSet (oracleJoin)

variable {A : Set ℕ} {μ ν : Measure CantorSeq} {x y : CantorSeq}

/-- If the interleaving `x ⊕ y` is random for `joinMeasure μ ν` relative to `A`, then `y` is
random for `ν` relative to `A ⊕ x`. Blueprint node `vl:snd`. -/
theorem IsMartinLofRandomIn.right_of_cantorJoin [IsFiniteMeasure μ]
    (hν : IsComputableCantorMeasureIn A ν)
    (h : IsMartinLofRandomIn A (joinMeasure μ ν) (cantorJoin x y)) :
    IsMartinLofRandomIn (oracleJoin A (seqOracle x)) ν y := by
  sorry -- blueprint node `vl:snd`

end Kolmogorov
