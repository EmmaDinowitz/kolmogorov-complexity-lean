/-
Copyright (c) 2026 Emma Dinowitz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emma Dinowitz
-/
import KolmogorovMathlib.AlgorithmicRandomness.Relative.Defs

/-!
# Interleaving of sequences and the joined product measure

The van Lambalgen theorem is about the interleaving `x ⊕ y` of two sequences, which places `x` on
the even positions and `y` on the odd positions (`cantorJoin`), and about the image of the product
measure `μ ⊗ ν` under interleaving (`joinMeasure`). The convention matches the oracle join
`PointToSet.oracleJoin`, which places its first argument on even queries, so that
`seqOracle (cantorJoin x y) = oracleJoin (seqOracle x) (seqOracle y)`.

## Conventions

`joinMeasure μ ν` is `Measure.map` of `μ.prod ν` along `(x, y) ↦ cantorJoin x y`. It is defined
for all measures; Mathlib's `Measure.prod` is only well behaved for s-finite factors, and the
theorems using `joinMeasure` state the finiteness they need. For the uniform measure,
`joinMeasure uniformMeasure uniformMeasure = uniformMeasure`, so the textbook statement about the
fair-coin measure is a special case.

## Main definitions

* `cantorJoin` (blueprint node `vl:join`): the interleaving of two sequences.
* `joinMeasure` (blueprint node `vl:join-measure`): the product measure carried to Cantor space by
  interleaving.

Used by `AlgorithmicRandomness/VanLambalgen/`.
-/

namespace Kolmogorov

open MeasureTheory

/-- The interleaving `x ⊕ y` of two sequences: `x` on the even positions, `y` on the odd ones.
Blueprint node `vl:join`. -/
def cantorJoin (x y : CantorSeq) : CantorSeq := fun n => if n % 2 = 0 then x (n / 2) else y (n / 2)

/-- The product measure `μ ⊗ ν` carried to Cantor space by interleaving: the image of
`μ.prod ν` under `(x, y) ↦ cantorJoin x y`. For non-s-finite factors Mathlib's `Measure.prod` is
still defined, and so is this measure. Blueprint node `vl:join-measure`. -/
noncomputable def joinMeasure (μ ν : Measure CantorSeq) : Measure CantorSeq :=
  (μ.prod ν).map fun p : CantorSeq × CantorSeq => cantorJoin p.1 p.2

end Kolmogorov
