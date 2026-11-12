/-
Copyright (c) 2026 Emma Dinowitz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emma Dinowitz
-/
import KolmogorovMathlib.AlgorithmicRandomness.VanLambalgen.Defs
import Mathlib.Probability.ProductMeasure

/-!
# Infinite joins of sequences and countable product measures

The countable form of the van Lambalgen theorem is about a sequence `x : ℕ → CantorSeq` of
sequences, encoded as one sequence `⊕ᵢ xᵢ` by Cantor pairing (`cantorPiJoin`: position `n` carries
bit `(unpair n).2` of `x (unpair n).1`), and about the product of a sequence of measures carried
by this encoding (`piJoinMeasure`). The oracle "all coordinates except the `i`-th" is the infinite
join with the `i`-th coordinate replaced by the all-`false` sequence (`cantorPiJoinExcept`); the
oracle "the coordinates before the `i`-th" blanks every coordinate from `i` on
(`cantorPiJoinBelow`). For the proofs, `skipIndex i` enumerates the indices other than `i`, and
`cantorPiJoinSkip x i` is the infinite join of the other coordinates, reindexed by `skipIndex i`.

## Conventions

`piJoinMeasure μ` is `Measure.map cantorPiJoin (Measure.infinitePi μ)`. Mathlib's
`Measure.infinitePi` is the product measure when every `μ i` is a probability measure and the zero
measure otherwise; the theorems using `piJoinMeasure` assume probability measures. The pairing is
Mathlib's `Nat.pair`/`Nat.unpair`.

## Main definitions

* `cantorPiJoin` (blueprint node `vl:pi-join`): the infinite join of a sequence of sequences.
* `piJoinMeasure` (blueprint node `vl:pi-join-measure`): the countable product measure carried to
  Cantor space by the infinite join.
* `cantorPiJoinExcept`, `cantorPiJoinBelow` (blueprint node `vl:pi-join`): the oracles of all
  coordinates but one, and of the coordinates below an index.
* `skipIndex`, `cantorPiJoinSkip` (blueprint node `vl:pi-split`): the other coordinates, reindexed.

Used by `AlgorithmicRandomness/VanLambalgen/Countable/` and
`AlgorithmicRandomness/VanLambalgen/MainResults.lean`.
-/

namespace Kolmogorov

open MeasureTheory

/-- The infinite join `⊕ᵢ xᵢ` of a sequence of sequences: position `n` carries bit `(unpair n).2`
of the sequence `x (unpair n).1`. Blueprint node `vl:pi-join`. -/
def cantorPiJoin (x : ℕ → CantorSeq) : CantorSeq := fun n => x (Nat.unpair n).1 (Nat.unpair n).2

/-- The countable product of the measures `μ i`, carried to Cantor space by the infinite join: the
image of `Measure.infinitePi μ` under `cantorPiJoin`. It is the zero measure unless every `μ i` is
a probability measure. Blueprint node `vl:pi-join-measure`. -/
noncomputable def piJoinMeasure (μ : ℕ → Measure CantorSeq) : Measure CantorSeq :=
  (Measure.infinitePi μ).map cantorPiJoin

/-- All coordinates except the `i`-th, as one sequence: the infinite join with the `i`-th
coordinate replaced by the all-`false` sequence. Blueprint node `vl:pi-join`. -/
def cantorPiJoinExcept (x : ℕ → CantorSeq) (i : ℕ) : CantorSeq :=
  cantorPiJoin (Function.update x i fun _ => false)

/-- The coordinates before the `i`-th, as one sequence: the infinite join with every coordinate
`j ≥ i` replaced by the all-`false` sequence. For `i = 0` this is the all-`false` sequence.
Blueprint node `vl:pi-join`. -/
def cantorPiJoinBelow (x : ℕ → CantorSeq) (i : ℕ) : CantorSeq :=
  cantorPiJoin fun j => if j < i then x j else fun _ => false

/-- The enumeration of the indices other than `i` in increasing order: `j ↦ j` below `i` and
`j ↦ j + 1` from `i` on. Blueprint node `vl:pi-split`. -/
def skipIndex (i j : ℕ) : ℕ := if j < i then j else j + 1

/-- The infinite join of the coordinates other than the `i`-th, reindexed by `skipIndex i`.
Blueprint node `vl:pi-split`. -/
def cantorPiJoinSkip (x : ℕ → CantorSeq) (i : ℕ) : CantorSeq :=
  cantorPiJoin fun j => x (skipIndex i j)

end Kolmogorov
