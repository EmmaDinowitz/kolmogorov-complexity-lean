/-
Copyright (c) 2026 Emma Dinowitz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emma Dinowitz
-/
import Mathlib
import KolmogorovMathlib.Trusted.Statements

/-!
# Trusted statements: shifts (Proposition 7.10, Example 5.5) and the companion Theorem 1(a), (b)

Continuation of `KolmogorovMathlib.Trusted.Statements` (the pilot), whose definitions are reused:
`bowenBall`, `IsAdmissible`, `MLRandom`, `orbitComplexityN`, `lowerOrbitComplexity`,
`upperOrbitComplexity`, `lowerLocalEntropy`, `upperLocalEntropy`, `ksEntropy`. This file adds,
in textbook style, the one-sided shift over a finite alphabet ([N, §7.4]) and Cantor space with
its standard computable structure (left implicit in [N, Example 5.5]), and states as `Prop`s,
without proofs:

* `Proposition7_10_i`, `Proposition7_10_ii` ([N, Prop. 7.10]): on a one-sided shift with a
  first-difference metric, `K̄^A(y, σ) ≤ h_ν(σ)` at a generic point `y` of an invariant `ν`, and
  `K̲^A(y, σ) = K̄^A(y, σ) = h_ν(σ)` at a random point of an ergodic `ν`;
* `Proposition7_10_i_cantor`, `Proposition7_10_ii_cantor`: the same on Cantor space with its
  standard presentation, where the extra hypothesis on the symbols of the ideal points holds;
* `Proposition7_10_i_ks`, `Proposition7_10_ii_ks`: the same with the Kolmogorov–Sinai entropy
  `ksEntropy ν shift` of the pilot in place of `h_ν(σ) = inf_k H_ν(ξᵏ) / k`;
* `Example5_5_1`, `Example5_5_2` ([N, Example 5.5]): a computable purely atomic measure with a
  random non-atom `z` of upper complexity `1`, and a computable measure with `Φ = (1, 1)` almost
  everywhere and a random point `z'` of lower complexity `0`;
* `Theorem1_a`, `Theorem1_b` ([C, Thm. 1(a), (b)]): the two halves of the pilot's `Theorem1`,
  with (a) also at every fixed scale `ε > 0`.

The proofs are in `KolmogorovMathlib.Trusted.BridgeShift`, which also proves that every new
definition agrees with the library's.

## What is trusted

Besides Mathlib, only the pilot `KolmogorovMathlib.Trusted.Statements` and, through it, the
library's computability foundations (`ComputableIn`, `IsREIn`, `oracleNatComplexity`; see the
pilot's module docstring). Import closure (checked with a script that follows `import` lines):
`Mathlib`, the pilot, `KolmogorovMathlib.Oracle.Basic` and
`KolmogorovMathlib.Oracle.PrefixComplexity.Basic`: the pilot's closure of 234 foundation modules
plus the two `Trusted` statement files, 236 library modules in all; no module under
`KolmogorovMathlib/PointToSet/` or `KolmogorovMathlib/Ergodic/`.

## Conventions

As in the pilot (`log` base 2, values in `[0, ∞]`, limits `ε → 0` as suprema over `ε > 0`).
Probability and invariance are stated with Mathlib's `IsProbabilityMeasure`,
`MeasurePreserving shift ν ν` (`ν` is shift-invariant) and `Ergodic shift ν` (which includes
invariance).
-/

namespace Kolmogorov.Trusted

open MeasureTheory Filter Set
open scoped ENNReal Computability Topology

universe u

/-! ### The one-sided shift over a finite alphabet -/

section Shift

variable {α : Type*}

/-- The left shift `σ` on one-sided sequences: `(σ y)ⱼ = y_{j+1}` ([N, §7.4]). -/
def shift (y : ℕ → α) : ℕ → α :=
  fun j ↦ y (j + 1)

/-- The cylinder `[w] = {y : yᵢ = wᵢ for i < k}` of a word `w = w₀ ⋯ w_{k-1}`. -/
def cylinder {k : ℕ} (w : Fin k → α) : Set (ℕ → α) :=
  {y | ∀ i : Fin k, y i = w i}

/-- The oracle `A` computes the symbols of the ideal points `(xᵢ)` of the shift: the map
`(i, j) ↦ (xᵢ)ⱼ` is `A`-computable. This hypothesis is not in [N]: there the shift carries its
standard computable structure implicitly, and for it the hypothesis holds for every oracle (see
`Proposition7_10_i_cantor`). It cannot be dropped for an arbitrary dense sequence of ideal
points: relabelling the ideal points by a noncomputable isometry can make every prefix
expensive. -/
def HasComputableSymbols [Primcodable α] (x : ℕ → ℕ → α) (A : Set ℕ) : Prop :=
  ComputableIn {charOracle A} fun q : ℕ × ℕ ↦ x q.1 q.2

variable [MeasurableSpace (ℕ → α)]

/-- `y` is generic for `ν` ([N, §7.4]): for every word `w` of length `k`, the frequency
`#{j < n : y_j ⋯ y_{j+k-1} = w} / n` of the occurrences of `w` in `y` tends to `ν[w]`. -/
def IsGeneric (ν : Measure (ℕ → α)) (y : ℕ → α) : Prop :=
  ∀ (k : ℕ) (w : Fin k → α), Tendsto
    (fun n : ℕ ↦ (({j | j < n ∧ ∀ i : Fin k, y (j + i) = w i} : Set ℕ).ncard : ℝ) / n)
    atTop (𝓝 (ν (cylinder w)).toReal)

variable [Fintype α]

/-- The block entropy in bits `H_ν(ξᵏ) = -∑_{|w| = k} ν[w] log₂ ν[w]`, the Shannon entropy of the
partition `ξᵏ` of the shift into the cylinders of length `k` (with `0 log 0 = 0`). -/
noncomputable def blockEntropy (ν : Measure (ℕ → α)) (k : ℕ) : ℝ :=
  ∑ w : Fin k → α, -(ν (cylinder w)).toReal * Real.logb 2 (ν (cylinder w)).toReal

/-- The entropy of the shift `h_ν(σ) = inf_{k ≥ 1} H_ν(ξᵏ) / k` in bits ([N, §7.4]). For a
shift-invariant probability measure `ν` the sequence `H_ν(ξᵏ)` is subadditive, so this infimum is
the limit `lim_k H_ν(ξᵏ) / k`; for a first-difference metric with its Borel σ-algebra (the
setting of `Proposition7_10_i`) it is the Kolmogorov–Sinai entropy `ksEntropy ν shift`, since the
partition by the first symbol generates (`shiftEntropy_eq_ksEntropy` in the bridge). The
infimum is over `k ≥ 1`: at `k = 0` the quotient would be `0`. -/
noncomputable def shiftEntropy (ν : Measure (ℕ → α)) : ℝ≥0∞ :=
  ⨅ (k : ℕ) (_ : 1 ≤ k), ENNReal.ofReal (blockEntropy ν k / k)

end Shift

/-! ### Proposition 7.10 on a shift with a first-difference metric -/

/-- [N, Proposition 7.10(i)]: on a one-sided shift `ℕ → α` over a finite alphabet, if `y` is
generic for a shift-invariant probability measure `ν`, then `K̄^A(y, σ) ≤ h_ν(σ)`.

The shift space carries a first-difference metric `d(y, z) = β^{firstDiff y z}` for `y ≠ z`
(`0 < β < 1`; `PiNat.firstDiff y z` is the first index where `y` and `z` differ, used only for
`y ≠ z`) and its Borel σ-algebra; such a space is compact. Its ideal points `(xᵢ)` are any dense
sequence. Hypotheses not in [N]: the alphabet has a computable coding (`Primcodable α`) and the
oracle `A` computes the symbols of the ideal points (`HasComputableSymbols`, which explains why it
is needed); for the standard structure of Cantor space this holds for every `A`
(`Proposition7_10_i_cantor`). -/
def Proposition7_10_i : Prop :=
  ∀ (α : Type u) [Fintype α] [Primcodable α] [MetricSpace (ℕ → α)] [MeasurableSpace (ℕ → α)]
    [BorelSpace (ℕ → α)] (β : ℝ), 0 < β → β < 1 →
    (∀ y z : ℕ → α, y ≠ z → dist y z = β ^ PiNat.firstDiff y z) →
    ∀ (x : ℕ → ℕ → α) (A : Set ℕ), DenseRange x → HasComputableSymbols x A →
    ∀ (ν : Measure (ℕ → α)) [IsProbabilityMeasure ν], MeasurePreserving shift ν ν →
    ∀ y : ℕ → α, IsGeneric ν y → upperOrbitComplexity x shift A y ≤ shiftEntropy ν

/-- [N, Proposition 7.10(ii)]: in the setting of `Proposition7_10_i`, if `ν` is an ergodic
probability measure and `y` is `ν`-random relative to an oracle `B` computing `ν`, then
`K̲^A(y, σ) = K̄^A(y, σ) = h_ν(σ)` for every `A ≤_T B`.

"`B` computes `ν`" is read as `B` admissible for `(ℕ → α, d, σ, ν)` (`IsAdmissible`: `B` also
computes the metric structure and `σ`). Genericity of `y` is not assumed (it follows from
randomness). Hypotheses not in [N]: `Primcodable α` and `A` computes the symbols of the ideal
points (`HasComputableSymbols`), as in `Proposition7_10_i`. -/
def Proposition7_10_ii : Prop :=
  ∀ (α : Type u) [Fintype α] [Primcodable α] [MetricSpace (ℕ → α)] [MeasurableSpace (ℕ → α)]
    [BorelSpace (ℕ → α)] (β : ℝ), 0 < β → β < 1 →
    (∀ y z : ℕ → α, y ≠ z → dist y z = β ^ PiNat.firstDiff y z) →
    ∀ (x : ℕ → ℕ → α) (ν : Measure (ℕ → α)) [IsProbabilityMeasure ν], Ergodic shift ν →
    ∀ A B : Set ℕ, IsAdmissible x shift ν B → charOracle A ≤ᵀ charOracle B →
    HasComputableSymbols x A → ∀ y ∈ MLRandom x B ν,
      lowerOrbitComplexity x shift A y = shiftEntropy ν ∧
        upperOrbitComplexity x shift A y = shiftEntropy ν

/-- [N, Proposition 7.10(i)] with the Kolmogorov–Sinai entropy `h_ν(σ) = ksEntropy ν shift` of the
pilot. Same hypotheses as `Proposition7_10_i`; the alphabet is only required to be finite. -/
def Proposition7_10_i_ks : Prop :=
  ∀ (α : Type u) [Finite α] [Primcodable α] [MetricSpace (ℕ → α)] [MeasurableSpace (ℕ → α)]
    [BorelSpace (ℕ → α)] (β : ℝ), 0 < β → β < 1 →
    (∀ y z : ℕ → α, y ≠ z → dist y z = β ^ PiNat.firstDiff y z) →
    ∀ (x : ℕ → ℕ → α) (A : Set ℕ), DenseRange x → HasComputableSymbols x A →
    ∀ (ν : Measure (ℕ → α)) [IsProbabilityMeasure ν], MeasurePreserving shift ν ν →
    ∀ y : ℕ → α, IsGeneric ν y → upperOrbitComplexity x shift A y ≤ ksEntropy ν shift

/-- [N, Proposition 7.10(ii)] with the Kolmogorov–Sinai entropy `h_ν(σ) = ksEntropy ν shift` of
the pilot. Same hypotheses as `Proposition7_10_ii`; the alphabet is only required to be
finite. -/
def Proposition7_10_ii_ks : Prop :=
  ∀ (α : Type u) [Finite α] [Primcodable α] [MetricSpace (ℕ → α)] [MeasurableSpace (ℕ → α)]
    [BorelSpace (ℕ → α)] (β : ℝ), 0 < β → β < 1 →
    (∀ y z : ℕ → α, y ≠ z → dist y z = β ^ PiNat.firstDiff y z) →
    ∀ (x : ℕ → ℕ → α) (ν : Measure (ℕ → α)) [IsProbabilityMeasure ν], Ergodic shift ν →
    ∀ A B : Set ℕ, IsAdmissible x shift ν B → charOracle A ≤ᵀ charOracle B →
    HasComputableSymbols x A → ∀ y ∈ MLRandom x B ν,
      lowerOrbitComplexity x shift A y = ksEntropy ν shift ∧
        upperOrbitComplexity x shift A y = ksEntropy ν shift

/-! ### Cantor space with its standard computable structure -/

section Cantor

/-- The Cantor metric `d(y, z) = 2^{-firstDiff y z}` (for `y ≠ z`) on `ℕ → Bool`, Mathlib's
first-difference metric `PiNat.metricSpaceOfDiscreteUniformity` (`cantorMetric_dist_eq`). Its
topology is the product topology, so the product σ-algebra is its Borel σ-algebra. Used as a
local instance in this section only. -/
@[reducible] noncomputable def cantorMetric : MetricSpace (ℕ → Bool) :=
  PiNat.metricSpaceOfDiscreteUniformity fun _ ↦ rfl

/-- The standard ideal points of Cantor space: the eventually-`false` sequences `w 0^∞`, the
`n`-th being `w 0^∞` for the binary word `w` with code `n` (Mathlib's `Encodable` coding of
`List Bool`; the empty word when `n` codes no word). [N, Example 5.5] leaves the computable
structure of `{0, 1}^ℕ` implicit ("computable measure", "random"); this is our reading of it, the
usual one. -/
def cantorIdeal (n : ℕ) : ℕ → Bool :=
  fun i ↦ ((Encodable.decode n : Option (List Bool)).getD []).getD i false

attribute [local instance] cantorMetric

/-- Sanity check: the Cantor metric is `2^{-firstDiff}`. -/
theorem cantorMetric_dist_eq {y z : ℕ → Bool} (h : y ≠ z) :
    dist y z = (1 / 2 : ℝ) ^ PiNat.firstDiff y z :=
  PiNat.dist_eq_of_ne h

/-- [N, Proposition 7.10(i)] on Cantor space `ℕ → Bool` with the Cantor metric and its standard
ideal points `cantorIdeal`, as printed: if `y` is generic for a shift-invariant probability
measure `ν`, then `K̄^A(y, σ) ≤ h_ν(σ)` for every oracle `A`. -/
def Proposition7_10_i_cantor : Prop :=
  ∀ (A : Set ℕ) (ν : Measure (ℕ → Bool)) [IsProbabilityMeasure ν], MeasurePreserving shift ν ν →
    ∀ y : ℕ → Bool, IsGeneric ν y → upperOrbitComplexity cantorIdeal shift A y ≤ shiftEntropy ν

/-- [N, Proposition 7.10(ii)] on Cantor space with its standard ideal points, as printed: if `ν`
is an ergodic probability measure and `y` is `ν`-random relative to an oracle `B` computing `ν`
(read as: admissible, `IsAdmissible`), then `K̲^A(y, σ) = K̄^A(y, σ) = h_ν(σ)` for every
`A ≤_T B`. -/
def Proposition7_10_ii_cantor : Prop :=
  ∀ (ν : Measure (ℕ → Bool)) [IsProbabilityMeasure ν], Ergodic shift ν →
    ∀ A B : Set ℕ, IsAdmissible cantorIdeal shift ν B → charOracle A ≤ᵀ charOracle B →
    ∀ y ∈ MLRandom cantorIdeal B ν,
      lowerOrbitComplexity cantorIdeal shift A y = shiftEntropy ν ∧
        upperOrbitComplexity cantorIdeal shift A y = shiftEntropy ν

/-- [N, Example 5.5(1)]: on Cantor space with its standard computable structure there is a
probability measure `μ`, computable (admissible relative to the empty oracle), carried by a
countable set (so purely atomic), with `h̲_μ(σ, ·) = h̄_μ(σ, ·) = 0` almost everywhere, and a
`μ`-random point `z` (relative to the empty oracle) that is not an atom, with `h̄_μ(σ, z) = 1`
and `K̄(z, σ) = 1` (`K` relative to the empty oracle).

In [N], `μ = λ ∘ f⁻¹` for the fair-coin measure `λ` and a computable map `f` built from a
left-c.e. random real `Ω`, and `z = f(Ω)`. The statement only asserts that such `μ` and `z`
exist, so `λ` does not appear in it. -/
def Example5_5_1 : Prop :=
  ∃ μ : Measure (ℕ → Bool), IsProbabilityMeasure μ ∧ IsAdmissible cantorIdeal shift μ ∅ ∧
    (∃ S : Set (ℕ → Bool), S.Countable ∧ μ Sᶜ = 0) ∧
    (∀ᵐ y ∂μ, lowerLocalEntropy μ shift y = 0 ∧ upperLocalEntropy μ shift y = 0) ∧
    ∃ z ∈ MLRandom cantorIdeal ∅ μ, μ {z} = 0 ∧ upperLocalEntropy μ shift z = 1 ∧
      upperOrbitComplexity cantorIdeal shift ∅ z = 1

/-- [N, Example 5.5(2)]: on Cantor space with its standard computable structure there is a
computable probability measure `μ'` (admissible relative to the empty oracle) with
`h̲_{μ'}(σ, ·) = h̄_{μ'}(σ, ·) = 1` almost everywhere, and a `μ'`-random point `z'` (relative to
the empty oracle) with `h̲_{μ'}(σ, z') = 0` and `K̲(z', σ) = 0`.

In [N], `μ' = λ ∘ f'⁻¹` for the fair-coin measure `λ`; as in `Example5_5_1`, `λ` does not appear
in the statement. -/
def Example5_5_2 : Prop :=
  ∃ μ : Measure (ℕ → Bool), IsProbabilityMeasure μ ∧ IsAdmissible cantorIdeal shift μ ∅ ∧
    (∀ᵐ y ∂μ, lowerLocalEntropy μ shift y = 1 ∧ upperLocalEntropy μ shift y = 1) ∧
    ∃ z ∈ MLRandom cantorIdeal ∅ μ, lowerLocalEntropy μ shift z = 0 ∧
      lowerOrbitComplexity cantorIdeal shift ∅ z = 0

end Cantor

/-! ### The companion Theorem 1(a), (b) -/

/-- [C, Theorem 1(a)]: in the setting of the pilot's `Theorem1` (compact `X`, `A` computes the
metric structure, `T` and the ergodic invariant probability measure `μ`), at every point `y`
that is `μ`-random relative to `A`, `limsup_n K_n^A(y, T, ε) / n ≤ h_μ(T)` for every `ε > 0`, and
hence `K̄^A(y, T) ≤ h_μ(T)`. `Continuous T` is listed separately, as in `Theorem1`. -/
def Theorem1_a : Prop :=
  ∀ (X : Type u) [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
    (x : ℕ → X) (T : X → X) (A : Set ℕ) (μ : Measure X) [IsProbabilityMeasure μ],
    Continuous T → IsAdmissible x T μ A → Ergodic T μ → ∀ y ∈ MLRandom x A μ,
      (∀ ε : ℝ, 0 < ε →
        limsup (fun n : ℕ ↦ (orbitComplexityN x T A y n ε : ℝ≥0∞) / n) atTop ≤ ksEntropy μ T) ∧
      upperOrbitComplexity x T A y ≤ ksEntropy μ T

/-- [C, Theorem 1(b)], in the limit `ε → 0`: in the setting of `Theorem1_a`,
`h_μ(T) ≤ K̲^A(y, T)` at every point `y` that is `μ`-random relative to `A`. -/
def Theorem1_b : Prop :=
  ∀ (X : Type u) [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
    (x : ℕ → X) (T : X → X) (A : Set ℕ) (μ : Measure X) [IsProbabilityMeasure μ],
    Continuous T → IsAdmissible x T μ A → Ergodic T μ → ∀ y ∈ MLRandom x A μ,
      ksEntropy μ T ≤ lowerOrbitComplexity x T A y

end Kolmogorov.Trusted
