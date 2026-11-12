/-
Copyright (c) 2026 Emma Dinowitz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emma Dinowitz
-/
import KolmogorovMathlib.AlgorithmicRandomness.MartinLof
import KolmogorovMathlib.Oracle.Joins

/-!
# Martin-Löf randomness on Cantor space relative to an oracle

This module relativizes the Cantor-space notions of `AlgorithmicRandomness/EffectiveOpen.lean`,
`ComputableMeasure.lean` and `MartinLof.lean` to an oracle `A : Set ℕ`. Every notion is the
unrelativized one with `Computable` replaced by `ComputableIn {charOracle A}`, the convention of
`KolmogorovMathlib/Oracle/` (an oracle is a set of natural numbers, queried through its total
characteristic function `charOracle A`).

A sequence `x : CantorSeq` is used as an oracle through `seqOracle x = {n | x n = true}`; the
oracle `A ⊕ x` of the van Lambalgen theorem is `PointToSet.oracleJoin A (seqOracle x)`.

## Conventions

* Measures are arbitrary Borel measures on `CantorSeq`; measures of sets are in `ℝ≥0∞`, and the
  test bound `2^{-n}` is written `dyadicValue 1 n`, as in `IsMartinLofTest`.
* A test relative to `A` is indexed by its level `n : ℕ`, and its cylinders by a stage `i : ℕ`;
  the enumeration is a single function of `(n, i)` computable in `A`.
* No finiteness or computability of the measure is built into `IsMartinLofTestIn` or
  `IsMartinLofRandomIn`; theorems state what they use.

## Main definitions

* `seqOracle` (blueprint node `vl:seq-oracle`): a sequence read as an oracle.
* `IsUniformlyEffectiveOpenIn` (blueprint node `vl:effective-open-in`): a sequence of unions of
  cylinders enumerated by one function computable in `A`.
* `IsComputableCantorMeasureIn` (blueprint node `vl:computable-measure-in`): cylinder masses
  uniformly approximable in `A`, with two-sided error `2^{-s}`.
* `IsMartinLofTestIn`, `IsMartinLofRandomIn` (blueprint nodes `vl:test-in`, `vl:random-in`):
  Martin-Löf tests and randomness relative to `A`.

## Notions not to be conflated

`IsComputableCantorMeasureIn A μ` is the Cantor-space notion with cylinders; the notion
`PointToSet.IsComputableMeasureIn P A μ` of `PointToSet/Measure/Computable.lean` is stated for a
presented metric space and balls. Likewise `IsMartinLofRandomIn A μ` is not identified with
`PointToSet.randomPoints P A μ` here: no presentation of Cantor space is fixed in this module.

These definitions are used by `AlgorithmicRandomness/Relative/Basic.lean` and by the van Lambalgen
theorem in `AlgorithmicRandomness/VanLambalgen/`.
-/

namespace Kolmogorov

open MeasureTheory ENNReal

/-- A sequence read as an oracle: the set of positions where it takes the value `true`.
Blueprint node `vl:seq-oracle`. -/
def seqOracle (x : CantorSeq) : Set ℕ := {n | x n = true}

/-- A sequence of subsets of Cantor space is uniformly effectively open relative to `A` when the
cylinders making up its members are enumerated by a single function of the level and the stage,
computable in `A`; the value `none` enumerates nothing. Blueprint node `vl:effective-open-in`. -/
def IsUniformlyEffectiveOpenIn (A : Set ℕ) (U : ℕ → Set CantorSeq) : Prop :=
  ∃ f : ℕ → ℕ → Option BitString, ComputableIn₂ {charOracle A} f ∧
    ∀ n, U n = ⋃ i, (f n i).elim ∅ cantorCylinder

/-- A measure on Cantor space is computable relative to `A` when the masses of all cylinders have
one family of dyadic approximations, computable in `A`, whose `s`-th member is accurate to
`2^{-s}` on both sides. This is `IsComputableMeasure` with `Computable₂` replaced by
`ComputableIn₂ {charOracle A}`. Blueprint node `vl:computable-measure-in`. -/
def IsComputableCantorMeasureIn (A : Set ℕ) (μ : Measure CantorSeq) : Prop :=
  ∃ a : BitString → ℕ → ℕ, ComputableIn₂ {charOracle A} a ∧ ∀ x s,
    dyadicValue (a x s) s ≤ cantorMass μ x + dyadicValue 1 s ∧
      cantorMass μ x ≤ dyadicValue (a x s) s + dyadicValue 1 s

/-- A Martin-Löf test for `μ` relative to `A`: a uniformly effectively open sequence relative to
`A` whose `n`-th member has measure at most `2^{-n}`. Blueprint node `vl:test-in`. -/
def IsMartinLofTestIn (A : Set ℕ) (μ : Measure CantorSeq) (U : ℕ → Set CantorSeq) : Prop :=
  IsUniformlyEffectiveOpenIn A U ∧ ∀ n, μ (U n) ≤ dyadicValue 1 n

/-- A sequence is Martin-Löf random for `μ` relative to `A` when it lies in the intersection of no
Martin-Löf test for `μ` relative to `A`. For the zero measure no sequence is random (the constant
test `univ` witnesses this). Blueprint node `vl:random-in`. -/
def IsMartinLofRandomIn (A : Set ℕ) (μ : Measure CantorSeq) (w : CantorSeq) : Prop :=
  ∀ U, IsMartinLofTestIn A μ U → w ∉ ⋂ n, U n

end Kolmogorov
