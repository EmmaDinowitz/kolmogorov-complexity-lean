/-
Copyright (c) 2026 Emma Dinowitz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emma Dinowitz
-/
import KolmogorovMathlib.AlgorithmicRandomness.VanLambalgen.Directions
import KolmogorovMathlib.AlgorithmicRandomness.VanLambalgen.Join

/-!
# The van Lambalgen theorem

For an oracle `A`, a finite measure `μ` and a measure `ν` computable relative to `A`, a pair of
sequences is random for the product measure exactly when its first coordinate is random and its
second coordinate is random relative to the first:

`x ⊕ y` is random for `joinMeasure μ ν` relative to `A` if and only if `x` is random for `μ`
relative to `A` and `y` is random for `ν` relative to `A ⊕ x`.

The pair is encoded by interleaving, `x ⊕ y = cantorJoin x y`, and `A ⊕ x` is
`PointToSet.oracleJoin A (seqOracle x)`.

## Conventions

* Randomness is `IsMartinLofRandomIn`: Martin-Löf tests that are c.e. in the oracle, with
  `μ`-measure at most `2^{-n}` at level `n`. When `μ` is not computable relative to `A` this is
  blind randomness (the tests have no access to `μ`); the theorem holds in that generality.
* The constants of the theorem are not quantitative; every statement is an equivalence or an
  implication between randomness notions, with no `O(1)` terms.
* Hypotheses: `ν` computable relative to `A` (`IsComputableCantorMeasureIn`) and `μ` finite.
  The symmetric forms swap the roles, so they need `μ` computable relative to `A`.

## Main declarations

* `isMartinLofRandomIn_cantorJoin_iff` (blueprint node `vl:main`): the van Lambalgen theorem.
* `isMartinLofRandomIn_cantorJoin_iff_swap` (blueprint node `vl:symm`): the same with the roles of
  the coordinates exchanged.
* `isMartinLofRandomIn_cantorJoin_iff_mutual` (blueprint node `vl:mutual`): for two relatively
  computable measures, the pair is random exactly when each coordinate is random relative to `A`
  joined with the other.
* `isMartinLofRandom_cantorJoin_uniformMeasure_iff` (blueprint node `vl:uniform`): the textbook
  statement for the uniform measure without oracle.
* `exists_isMartinLofRandomIn_cantorJoin` (blueprint node `vl:nonvacuous`): for nonzero measures
  both sides of `vl:main` hold for some pair.

## References

M. van Lambalgen, *Random sequences*, PhD thesis, University of Amsterdam, 1987.
A. Nies, *Computability and Randomness*, Oxford University Press, 2009, Section 3.4.
-/

namespace Kolmogorov

open MeasureTheory
open PointToSet (oracleJoin)

variable {A : Set ℕ} {μ ν : Measure CantorSeq} {x y : CantorSeq}

/-- **van Lambalgen's theorem.** For a finite measure `μ` and a measure `ν` computable relative to
`A`, the interleaving `x ⊕ y` is random for `joinMeasure μ ν` relative to `A` if and only if `x`
is random for `μ` relative to `A` and `y` is random for `ν` relative to `A ⊕ x`.
Blueprint node `vl:main`. -/
theorem isMartinLofRandomIn_cantorJoin_iff [IsFiniteMeasure μ]
    (hν : IsComputableCantorMeasureIn A ν) :
    IsMartinLofRandomIn A (joinMeasure μ ν) (cantorJoin x y) ↔
      IsMartinLofRandomIn A μ x ∧ IsMartinLofRandomIn (oracleJoin A (seqOracle x)) ν y := by
  have := hν.isFiniteMeasure
  exact ⟨fun h ↦ ⟨h.left_of_cantorJoin, h.right_of_cantorJoin hν⟩,
    fun h ↦ h.1.cantorJoin hν h.2⟩

/-- **van Lambalgen's theorem, coordinates exchanged.** For `μ` computable relative to `A` and a
finite measure `ν`, the interleaving `x ⊕ y` is random for `joinMeasure μ ν` relative to `A` if
and only if `y` is random for `ν` relative to `A` and `x` is random for `μ` relative to `A ⊕ y`.
Blueprint node `vl:symm`. -/
theorem isMartinLofRandomIn_cantorJoin_iff_swap [IsFiniteMeasure ν]
    (hμ : IsComputableCantorMeasureIn A μ) :
    IsMartinLofRandomIn A (joinMeasure μ ν) (cantorJoin x y) ↔
      IsMartinLofRandomIn A ν y ∧ IsMartinLofRandomIn (oracleJoin A (seqOracle y)) μ x := by
  have := hμ.isFiniteMeasure
  rw [isMartinLofRandomIn_joinMeasure_swap]
  exact isMartinLofRandomIn_cantorJoin_iff hμ

/-- **Mutual relative randomness.** For measures `μ`, `ν` computable relative to `A`, the
interleaving `x ⊕ y` is random for `joinMeasure μ ν` relative to `A` if and only if `x` is random
for `μ` relative to `A ⊕ y` and `y` is random for `ν` relative to `A ⊕ x`.
Blueprint node `vl:mutual`. -/
theorem isMartinLofRandomIn_cantorJoin_iff_mutual (hμ : IsComputableCantorMeasureIn A μ)
    (hν : IsComputableCantorMeasureIn A ν) :
    IsMartinLofRandomIn A (joinMeasure μ ν) (cantorJoin x y) ↔
      IsMartinLofRandomIn (oracleJoin A (seqOracle y)) μ x ∧
        IsMartinLofRandomIn (oracleJoin A (seqOracle x)) ν y := by
  have := hμ.isFiniteMeasure
  have := hν.isFiniteMeasure
  refine ⟨fun h ↦ ⟨((isMartinLofRandomIn_cantorJoin_iff_swap hμ).1 h).2,
    ((isMartinLofRandomIn_cantorJoin_iff hν).1 h).2⟩, fun h ↦ ?_⟩
  exact (isMartinLofRandomIn_cantorJoin_iff hν).2
    ⟨h.1.mono_oracle (PointToSet.oracle_joins A _), h.2⟩

/-- **van Lambalgen's theorem for the uniform measure** (the textbook form, without oracle): the
interleaving `x ⊕ y` is Martin-Löf random for the uniform measure if and only if `x` is, and `y`
is Martin-Löf random relative to `x`. Blueprint node `vl:uniform`. -/
theorem isMartinLofRandom_cantorJoin_uniformMeasure_iff :
    IsMartinLofRandom uniformMeasure (cantorJoin x y) ↔
      IsMartinLofRandom uniformMeasure x ∧
        IsMartinLofRandomIn (seqOracle x) uniformMeasure y := by
  have hν := isComputableMeasure_uniform.isComputableCantorMeasureIn (∅ : Set ℕ)
  have := hν.isFiniteMeasure
  have h := isMartinLofRandomIn_cantorJoin_iff (A := ∅) (μ := uniformMeasure) (x := x) (y := y) hν
  rw [joinMeasure_uniformMeasure] at h
  simp only [isMartinLofRandomIn_empty_iff, isMartinLofRandomIn_oracleJoin_empty_left] at h
  exact h

/-- **Non-vacuousness of van Lambalgen's theorem.** For a nonzero finite measure `μ` and a nonzero
measure `ν` computable relative to `A`, some pair `(x, y)` has `x` random for `μ` relative to `A`
and `y` random for `ν` relative to `A ⊕ x`. Blueprint node `vl:nonvacuous`. -/
theorem exists_isMartinLofRandomIn_cantorJoin [IsFiniteMeasure μ]
    (hν : IsComputableCantorMeasureIn A ν) (hμ0 : μ ≠ 0) (hν0 : ν ≠ 0) :
    ∃ x y, IsMartinLofRandomIn A μ x ∧ IsMartinLofRandomIn (oracleJoin A (seqOracle x)) ν y := by
  have := hν.isFiniteMeasure
  have hpos : joinMeasure μ ν Set.univ ≠ 0 := by
    rw [joinMeasure_univ]
    exact mul_ne_zero (Measure.measure_univ_ne_zero.2 hμ0) (Measure.measure_univ_ne_zero.2 hν0)
  obtain ⟨z, hz⟩ : ∃ z, IsMartinLofRandomIn A (joinMeasure μ ν) z := by
    by_contra hcon
    push Not at hcon
    refine hpos (measure_mono_null (fun w _ ↦ hcon w) ?_)
    exact measure_setOf_not_isMartinLofRandomIn A (joinMeasure μ ν)
  obtain ⟨x, y, rfl⟩ := exists_cantorJoin_eq z
  exact ⟨x, y, (isMartinLofRandomIn_cantorJoin_iff hν).1 hz⟩

end Kolmogorov
