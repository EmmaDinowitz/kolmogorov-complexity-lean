/-
Copyright (c) 2026 Emma Dinowitz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emma Dinowitz
-/
import KolmogorovMathlib.PointToSet.Measure.Ergodic.CantorPresentation
import KolmogorovMathlib.PointToSet.Measure.RemarksShift

/-!
# Proposition 7.10 and Remarks 3.4, 6.6, 7.11 for the standard presentation of Cantor space

Proposition 7.10 and Remarks 3.4, 6.6 and 7.11 of E. Dinowitz, *Entropy of non-invariant
measures and orbit complexity of random points*, are stated in `Ergodic/Proposition710.lean` and
`RemarksShift.lean` for an arbitrary presentation `P` of the shift space, with the added
hypothesis `hP` that the symbols of the ideal points are computable relative to the oracle. The
paper tacitly uses the standard computable presentation. This file instantiates those results on
Cantor space `ℕ → Bool` with the metric `cantorMetricSpace` (a local instance,
`d(x, y) = (1/2)^{firstDiff x y}`) and its standard presentation `cantorPresentation`, for which
`hP` holds relative to every oracle (`cantorPres_computableIn_symbols`). The results are then
stated as printed, for every oracle `A`; only the admissibility hypotheses remain.

* Proposition 7.10: `upperOrbitComplexity_le_shiftEntropy_cantor` (i) and
  `orbitComplexities_eq_shiftEntropy_cantor` (ii).
* Remark 3.4: `oracleComplexity_cantorPrefix_le_infoBits_cantor`,
  `infoBits_le_oracleComplexity_cantorPrefix_of_mem_randomPoints_cantor` and
  `abs_oracleComplexity_cantorPrefix_sub_infoBits_le_cantor`
  (`K^A(x↾n) = -log₂ μ[x↾n] + O(log n)` at the `μ`-random points).
* Remark 6.6: `abs_infoBits_universalMeasure_cylinder_sub_oracleComplexity_le_cantor`
  (`-log₂ m^A[w] = K^A(w) + O(log |w|)`) and `orbitComplexities_eq_rates_KA_cantor`
  (`Ψ^∅` is the pair of growth rates of `KA`, with no hypothesis left).
* Remark 7.11: `exists_isGenericPoint_of_mem_randomPoints_cantor` (V'yugin) and
  `exists_isGenericPoint_upperOrbitComplexity_le_cantor` (`K̄^{A'}(x, σ) ≤ h_{Q_x}(σ)` for every
  oracle `A'`).

Blueprint nodes `erg:prop710`, `meas:remarks`.
-/

namespace Kolmogorov.PointToSet

open Filter Set MeasureTheory
open scoped Topology ENNReal Computability

attribute [local instance] cantorMetricSpace

/-! ### Proposition 7.10 -/

/-- Proposition 7.10(i) on Cantor space with its standard presentation: if `x` is generic for a
shift-invariant probability measure `ν`, then `K̄^A(x, σ) ≤ h_ν(σ)` for every oracle `A`.
Instance of `upperOrbitComplexity_le_shiftEntropy`. Blueprint node `erg:prop710`. -/
theorem upperOrbitComplexity_le_shiftEntropy_cantor (A : Set ℕ) (ν : Measure (ℕ → Bool))
    [IsProbabilityMeasure ν] (hν : MeasurePreserving shiftMap ν ν) {x : ℕ → Bool}
    (hx : IsGenericPoint ν x) :
    (orbitComplexities cantorPresentation shiftMap A x).2 ≤ shiftEntropy ν :=
  upperOrbitComplexity_le_shiftEntropy (β := 1 / 2) (by norm_num) (by norm_num)
    cantor_hd cantorPresentation A (cantorPres_computableIn_symbols A) ν hν hx

/-- Proposition 7.10(ii) on Cantor space with its standard presentation: if `ν` is ergodic and
`x` is `ν`-random relative to an oracle `B` admissible for `ν`, then
`K̲^A(x, σ) = K̄^A(x, σ) = h_ν(σ)` for every oracle `A ≤_T B`.
Instance of `orbitComplexities_eq_shiftEntropy`. Blueprint node `erg:prop710`. -/
theorem orbitComplexities_eq_shiftEntropy_cantor (ν : Measure (ℕ → Bool))
    [IsProbabilityMeasure ν] (hν : Ergodic shiftMap ν) {B : Set ℕ}
    (hB : IsMeasureAdmissible cantorPresentation shiftMap ν B) {x : ℕ → Bool}
    (hx : x ∈ randomPoints cantorPresentation B ν) {A : Set ℕ}
    (hAB : charOracle A ≤ᵀ charOracle B) :
    orbitComplexities cantorPresentation shiftMap A x = (shiftEntropy ν, shiftEntropy ν) :=
  orbitComplexities_eq_shiftEntropy (β := 1 / 2) (by norm_num) (by norm_num) cantor_hd
    cantorPresentation ν hν hB hx hAB (cantorPres_computableIn_symbols A)

/-! ### Remark 3.4 -/

/-- Remark 3.4(b), coding direction, for the standard presentation of Cantor space: if `A`
computes a measure `μ` of mass at most one, then `K^A(x↾n) ≤ -log₂ μ[x↾n] + O(log n)` for every
point `x` and every `n ≥ 1` with `μ[x↾n] > 0`. Instance of
`oracleComplexity_cantorPrefix_le_infoBits`. Blueprint node `meas:remarks`. -/
theorem oracleComplexity_cantorPrefix_le_infoBits_cantor (A : Set ℕ) (μ : Measure (ℕ → Bool))
    [IsFiniteMeasure μ] (hμ : μ univ ≤ 1)
    (hA : IsMeasureAdmissible cantorPresentation shiftMap μ A) :
    ∃ c : ℝ, ∀ (x : ℕ → Bool) (n : ℕ), 1 ≤ n → μ (PiNat.cylinder x n) ≠ 0 →
      (oracleComplexity A (cantorPrefix x n) : ℝ) ≤
        (infoBits (μ (PiNat.cylinder x n))).toReal + c * Real.logb 2 n + c :=
  oracleComplexity_cantorPrefix_le_infoBits cantorPresentation A
    (cantorPres_computableIn_symbols A) μ hμ hA

/-- Remark 3.4(b), incompressibility direction, for the standard presentation of Cantor space:
if `A` is admissible for a probability measure `μ`, then at every `x ∈ R_A^μ`,
`-log₂ μ[x↾n] ≤ K^A(x↾n) + O(log n)`. Instance of
`infoBits_le_oracleComplexity_cantorPrefix_of_mem_randomPoints`. Blueprint node
`meas:remarks`. -/
theorem infoBits_le_oracleComplexity_cantorPrefix_of_mem_randomPoints_cantor (A : Set ℕ)
    (μ : Measure (ℕ → Bool)) [IsProbabilityMeasure μ]
    (hA : IsMeasureAdmissible cantorPresentation shiftMap μ A) {x : ℕ → Bool}
    (hx : x ∈ randomPoints cantorPresentation A μ) :
    ∃ c : ℝ, ∀ n : ℕ, 1 ≤ n →
      (infoBits (μ (PiNat.cylinder x n))).toReal ≤
        oracleComplexity A (cantorPrefix x n) + c * Real.logb 2 n + c :=
  infoBits_le_oracleComplexity_cantorPrefix_of_mem_randomPoints cantorPresentation A
    (cantorPres_computableIn_symbols A) μ hA hx

/-- Remark 3.4 for the standard presentation of Cantor space: for every oracle `A` admissible
for a probability measure `μ`, the Levin–Schnorr estimate `K^A(x↾n) = -log₂ μ[x↾n] + O(log n)`
holds at every `x ∈ R_A^μ`. Instance of `abs_oracleComplexity_cantorPrefix_sub_infoBits_le`.
Blueprint node `meas:remarks`. -/
theorem abs_oracleComplexity_cantorPrefix_sub_infoBits_le_cantor (A : Set ℕ)
    (μ : Measure (ℕ → Bool)) [IsProbabilityMeasure μ]
    (hA : IsMeasureAdmissible cantorPresentation shiftMap μ A) {x : ℕ → Bool}
    (hx : x ∈ randomPoints cantorPresentation A μ) :
    ∃ c : ℝ, ∀ n : ℕ, 1 ≤ n →
      |(oracleComplexity A (cantorPrefix x n) : ℝ) - (infoBits (μ (PiNat.cylinder x n))).toReal|
        ≤ c * Real.logb 2 n + c :=
  abs_oracleComplexity_cantorPrefix_sub_infoBits_le cantorPresentation A
    (cantorPres_computableIn_symbols A) μ hA hx

/-! ### Remark 6.6 -/

/-- Remark 6.6 at the level of words, for the standard presentation of Cantor space: for every
oracle `A`, the information `-log₂ m^A[w]` of a cylinder under the universal measure is
`K^A(w) + O(log |w|)`, for every word `w = x↾n`. Instance of
`abs_infoBits_universalMeasure_cylinder_sub_oracleComplexity_le`. Blueprint node
`meas:remarks`. -/
theorem abs_infoBits_universalMeasure_cylinder_sub_oracleComplexity_le_cantor (A : Set ℕ) :
    ∃ c : ℝ, ∀ (x : ℕ → Bool) (n : ℕ), 1 ≤ n →
      |(infoBits (universalMeasure cantorPresentation A (PiNat.cylinder x n))).toReal -
          oracleComplexity A (cantorPrefix x n)| ≤ c * Real.logb 2 n + c :=
  abs_infoBits_universalMeasure_cylinder_sub_oracleComplexity_le cantorPresentation A
    (cantorPres_computableIn_symbols A)

/-- Remark 6.6 for the empty oracle, second sentence, for the standard presentation of Cantor
space: at every point `x`, `K̲(x, σ) = liminf_n KA(x↾n) / n` and
`K̄(x, σ) = limsup_n KA(x↾n) / n`, with `KA(w) = -log₂ M(w)` the a priori complexity. All the
hypotheses of `orbitComplexities_eq_rates_KA` (computable metric table, represented shift,
computable symbols) hold for `cantorPresentation`. Blueprint node `meas:remarks`. -/
theorem orbitComplexities_eq_rates_KA_cantor (x : ℕ → Bool) :
    orbitComplexities cantorPresentation shiftMap ∅ x =
      (liminf (fun n : ℕ ↦ ENNReal.ofReal (KA (cantorPrefix x n)) / n) atTop,
        limsup (fun n : ℕ ↦ ENNReal.ofReal (KA (cantorPrefix x n)) / n) atTop) :=
  orbitComplexities_eq_rates_KA cantorPresentation (cantorPres_computablePresentationIn ∅)
    (cantorPres_isRepresentedMapIn_shiftMap ∅) (cantorPres_computableIn_symbols ∅) x

/-! ### Remark 7.11 -/

/-- Remark 7.11, first bullet (V'yugin's effective ergodic theorem), for the standard
presentation of Cantor space: if `μ` is a shift-invariant probability measure and `A` is
admissible for `μ`, then every `x ∈ R_A^μ` is generic for some shift-invariant probability
measure `Q_x`. Instance of `exists_isGenericPoint_of_mem_randomPoints`. Blueprint node
`meas:remarks`. -/
theorem exists_isGenericPoint_of_mem_randomPoints_cantor (A : Set ℕ) (μ : Measure (ℕ → Bool))
    [IsProbabilityMeasure μ] (hμ : MeasurePreserving shiftMap μ μ)
    (hA : IsMeasureAdmissible cantorPresentation shiftMap μ A) {x : ℕ → Bool}
    (hx : x ∈ randomPoints cantorPresentation A μ) :
    ∃ ν : Measure (ℕ → Bool), IsProbabilityMeasure ν ∧ MeasurePreserving shiftMap ν ν ∧
      IsGenericPoint ν x :=
  exists_isGenericPoint_of_mem_randomPoints (β := 1 / 2) (by norm_num) (by norm_num)
    cantor_hd cantorPresentation A (cantorPres_computableIn_symbols A) μ hμ hA hx

/-- Remark 7.11, first bullet ("half of the statement is unconditional"), for the standard
presentation of Cantor space: under the hypotheses of
`exists_isGenericPoint_of_mem_randomPoints_cantor`, a `μ`-random point `x` is generic for a
shift-invariant probability measure `Q_x` with `K̄^{A'}(x, σ) ≤ h_{Q_x}(σ)` for every oracle
`A'`. Instance of `exists_isGenericPoint_upperOrbitComplexity_le`. Blueprint node
`meas:remarks`. -/
theorem exists_isGenericPoint_upperOrbitComplexity_le_cantor (A : Set ℕ)
    (μ : Measure (ℕ → Bool)) [IsProbabilityMeasure μ] (hμ : MeasurePreserving shiftMap μ μ)
    (hA : IsMeasureAdmissible cantorPresentation shiftMap μ A) {x : ℕ → Bool}
    (hx : x ∈ randomPoints cantorPresentation A μ) :
    ∃ ν : Measure (ℕ → Bool), IsProbabilityMeasure ν ∧ MeasurePreserving shiftMap ν ν ∧
      IsGenericPoint ν x ∧ ∀ A' : Set ℕ,
        (orbitComplexities cantorPresentation shiftMap A' x).2 ≤ shiftEntropy ν := by
  obtain ⟨ν, hν, hνinv, hgen, hle⟩ := exists_isGenericPoint_upperOrbitComplexity_le (β := 1 / 2)
    (by norm_num) (by norm_num) cantor_hd cantorPresentation A
    (cantorPres_computableIn_symbols A) μ hμ hA hx
  exact ⟨ν, hν, hνinv, hgen, fun A' ↦ hle A' (cantorPres_computableIn_symbols A')⟩

end Kolmogorov.PointToSet
