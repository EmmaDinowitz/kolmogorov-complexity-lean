/-
Copyright (c) 2026 Emma Dinowitz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emma Dinowitz
-/
import Mathlib
import KolmogorovMathlib.Oracle.Basic
import KolmogorovMathlib.Oracle.PrefixComplexity.Basic

/-!
# Trusted statements: Theorem 3.3 and the companion Theorem 1

This file is meant to be read by a human, top to bottom, instead of the library's internal
definitions. It defines, in textbook style, the notions used by

* [N] *Entropy of non-invariant measures and orbit complexity of random points* (§§2–3), and
* [C] *Orbit complexity of Martin-Löf random points equals entropy* (companion note),

and states their main theorems as `Prop`s, without proofs:

* `Theorem3_3_upper` ([N, Thm. 3.3], first half): `K̲^A(x, T) ≤ h̲_μ(T, x)` and
  `K̄^A(x, T) ≤ h̄_μ(T, x)` at every point;
* `Theorem3_3` ([N, Thm. 3.3]): equality at every point that is `μ`-random relative to `A`;
* `Theorem1` ([C, Thm. 1]): for an ergodic invariant `μ` on a compact space, both orbit
  complexities equal the Kolmogorov–Sinai entropy at every random point.

The proofs are in `KolmogorovMathlib.Trusted.Bridge`, which also proves that every definition
below agrees with the library's (`*_iff_*` and `*_eq_*` lemmas there): unconditionally, except
that the orbit complexities agree for continuous `T` and the Kolmogorov–Sinai entropy agrees
for an invariant probability measure; both conditions are hypotheses of the statements.

## What is trusted

Besides Mathlib, this file uses only the library's computability foundations:

* `ComputableIn {charOracle A} f`: `f` is computable with oracle `A` (Mathlib's `RecursiveIn`
  on `Primcodable` types, with the total characteristic function `charOracle A` as oracle);
* `IsREIn A F`: the predicate `F` is the domain of a partial function computable in `A`;
* `oracleNatComplexity A i`: the prefix-free Kolmogorov complexity `K^A(i)` of `i : ℕ`
  relative to `A` (for a fixed optimal prefix-free oracle machine).

Import closure (checked with a script that follows `import` lines): `Mathlib`,
`KolmogorovMathlib.Oracle.Basic` and `KolmogorovMathlib.Oracle.PrefixComplexity.Basic`, whose
closure is 234 library modules in `Foundation`, `Interface`, `Core`, `Prefix`, `Complexity`,
`Encoding`, `AlgorithmicProbability`, `AlgorithmicRandomness`, `AlgorithmicStatistics`,
`CommonInformation`, `MonotoneComplexity`, `Restricted` and `Oracle`; no module under
`KolmogorovMathlib/PointToSet/` or `KolmogorovMathlib/Ergodic/`.

## Conventions

* `log` is base 2 and all entropies and complexities are in bits, valued in `[0, ∞]`
  (`ℝ≥0∞`), since each of them can be infinite.
* Limits as `ε → 0` of quantities that are nondecreasing as `ε ↓ 0` are written as suprema
  over `ε > 0`, which is the same thing and needs no existence proof.
* Rational balls `B(xᵢ, q)` are allowed for every `q : ℚ`; for `q ≤ 0` the ball is empty, so
  this gives the same c.e. open sets as `q ∈ ℚ_{>0}` in [N].
-/

namespace Kolmogorov.Trusted

open MeasureTheory Filter Set
open scoped ENNReal Computability
open Kolmogorov.PointToSet (IsREIn oracleNatComplexity)

universe u

section Metric

variable {X : Type*} [MetricSpace X]

/-! ### Bowen balls -/

/-- The Bowen ball `B_n(x, T, ε) = {y : d(Tᵏx, Tᵏy) < ε for 0 ≤ k < n}` ([N, §2.1]).
For `n = 0` it is the whole space. -/
def bowenBall (T : X → X) (n : ℕ) (x : X) (ε : ℝ) : Set X :=
  {y | ∀ k < n, dist (T^[k] x) (T^[k] y) < ε}

/-! ### Computable metric spaces, open sets, maps and measures relative to an oracle -/

/-- `(xᵢ)` is a computable metric structure on `X` relative to `A` ([N, §2.1], [Din, Def. 2.6]):
the ideal points `xᵢ` are dense and the distances `d(xᵢ, xⱼ)` are computable in `A`, uniformly:
an `A`-computable rational `r(i, j, p)` is within `2⁻ᵖ` of `d(xᵢ, xⱼ)`. -/
def IsComputablePresentation (x : ℕ → X) (A : Set ℕ) : Prop :=
  DenseRange x ∧ ∃ r : (ℕ × ℕ) × ℕ → ℚ, ComputableIn {charOracle A} r ∧
    ∀ i j p, |(r ((i, j), p) : ℝ) - dist (x i) (x j)| < (2 : ℝ)⁻¹ ^ p

/-- `U` is `A`-c.e. open ([N, §2.2]): the union of an `A`-c.e. set of rational balls
`B(xᵢ, q)` about ideal points. -/
def IsCeOpen (x : ℕ → X) (A : Set ℕ) (U : Set X) : Prop :=
  ∃ E : ℕ × ℚ → Prop, IsREIn A E ∧ U = ⋃ (i : ℕ) (q : ℚ) (_ : E (i, q)), Metric.ball (x i) q

/-- A family `(U_k)` indexed by a computably encoded type is `A`-c.e. open uniformly in `k`:
one `A`-c.e. set of triples `(k, i, q)` lists, for each `k`, the rational balls whose union is
`U_k` ([N, §2.2]). -/
def IsCeOpenFamily {κ : Type*} [Primcodable κ] (x : ℕ → X) (A : Set ℕ) (U : κ → Set X) :
    Prop :=
  ∃ E : κ × ℕ × ℚ → Prop, IsREIn A E ∧
    ∀ k, U k = ⋃ (i : ℕ) (q : ℚ) (_ : E (k, i, q)), Metric.ball (x i) q

/-- `T` is `A`-computable ([N, §2.1]): the preimages `T⁻¹ B(xⱼ, q)` of the rational balls are
`A`-c.e. open, uniformly in `(j, q)`. This is the usual effective-continuity form of
computability of a map (Hoyrup–Rojas; [N] cites [Din, Def. 2.6]). The library's form, a sound
and complete `A`-c.e. relation between balls (`IsRepresentedMapIn`), is equivalent
(`isComputableMap_iff` in the bridge).
It implies that `T` is continuous (`IsComputableMap.continuous` in the bridge). -/
def IsComputableMap (x : ℕ → X) (A : Set ℕ) (T : X → X) : Prop :=
  IsCeOpenFamily x A fun b : ℕ × ℚ ↦ T ⁻¹' Metric.ball (x b.1) b.2

variable [MeasurableSpace X]

/-- `μ` is `A`-computable ([N, §2.2], following Hoyrup–Rojas): the measures of finite unions of
rational balls are lower semicomputable in `A`, uniformly in the list of balls, i.e. the set of
pairs `(L, q)` with `q < μ(⋃_{(i, r) ∈ L} B(xᵢ, r))` is `A`-c.e. (Used for finite `μ`.) -/
def IsComputableMeasure (x : ℕ → X) (A : Set ℕ) (μ : Measure X) : Prop :=
  IsREIn A fun w : List (ℕ × ℚ) × ℚ ↦
    (w.2 : ℝ) < (μ (⋃ b ∈ w.1, Metric.ball (x b.1) b.2)).toReal

/-- `A` is admissible for `(X, d, T, μ)` with ideal points `(xᵢ)` ([N, §2.2]): `A` computes the
metric structure, `T` and `μ`. -/
structure IsAdmissible (x : ℕ → X) (T : X → X) (μ : Measure X) (A : Set ℕ) : Prop where
  /-- The ideal points are dense, with `A`-computable distances. -/
  presentation : IsComputablePresentation x A
  /-- `T` is `A`-computable. -/
  map : IsComputableMap x A T
  /-- `μ` is `A`-computable. -/
  measure : IsComputableMeasure x A μ

/-! ### Martin-Löf randomness -/

/-- A `μ`-test relative to `A` ([N, §2.2]): a uniformly `A`-c.e. open sequence `(U_m)` with
`μ(U_m) ≤ 2⁻ᵐ`. -/
def IsMLTest (x : ℕ → X) (A : Set ℕ) (μ : Measure X) (U : ℕ → Set X) : Prop :=
  IsCeOpenFamily x A U ∧ ∀ m, μ (U m) ≤ (2 : ℝ≥0∞)⁻¹ ^ m

/-- The set `R_A^μ` of points that are Martin-Löf random for `μ` relative to `A` ([N, §2.2]):
the points lying in `⋂_m U_m` for no `μ`-test `(U_m)` relative to `A`. -/
def MLRandom (x : ℕ → X) (A : Set ℕ) (μ : Measure X) : Set X :=
  {y | ∀ U : ℕ → Set X, IsMLTest x A μ U → y ∉ ⋂ m, U m}

end Metric

/-! ### Orbit complexity and local entropies -/

section Complexity

variable {X : Type*} [MetricSpace X]

/-- `K_n^A(y, T, ε) = min {K^A(i) : xᵢ ∈ B_n(y, T, ε)}` ([N, §2.1], [Din, Def. 3.1]), in `ℕ∞`
(the minimum of the empty set is `∞`; for `ε > 0` and continuous `T` the set is nonempty). -/
noncomputable def orbitComplexityN (x : ℕ → X) (T : X → X) (A : Set ℕ) (y : X) (n : ℕ)
    (ε : ℝ) : ℕ∞ :=
  ⨅ (i : ℕ) (_ : x i ∈ bowenBall T n y ε), (oracleNatComplexity A i : ℕ∞)

/-- The lower orbit complexity `K̲^A(y, T) = lim_{ε→0} liminf_n K_n^A(y, T, ε) / n`
([N, §2.1]). The inner quantity is nondecreasing as `ε ↓ 0`, so the limit is the supremum. -/
noncomputable def lowerOrbitComplexity (x : ℕ → X) (T : X → X) (A : Set ℕ) (y : X) : ℝ≥0∞ :=
  ⨆ (ε : ℝ) (_ : 0 < ε), liminf (fun n : ℕ ↦ (orbitComplexityN x T A y n ε : ℝ≥0∞) / n) atTop

/-- The upper orbit complexity `K̄^A(y, T) = lim_{ε→0} limsup_n K_n^A(y, T, ε) / n`
([N, §2.1]), again a supremum over `ε > 0`. -/
noncomputable def upperOrbitComplexity (x : ℕ → X) (T : X → X) (A : Set ℕ) (y : X) : ℝ≥0∞ :=
  ⨆ (ε : ℝ) (_ : 0 < ε), limsup (fun n : ℕ ↦ (orbitComplexityN x T A y n ε : ℝ≥0∞) / n) atTop

/-- The information `-log₂ q ∈ [0, ∞]` of a mass `q`: `∞` for `q = 0`. (Masses here are at most
`1`; for `q > 1` the value is truncated at `0`.) -/
noncomputable def info (q : ℝ≥0∞) : ℝ≥0∞ :=
  if q = 0 then ∞ else ENNReal.ofReal (-Real.logb 2 q.toReal)

variable [MeasurableSpace X]

/-- The lower local entropy `h̲_μ(T, y) = lim_{ε→0} liminf_n -(1/n) log μ(B_n(y, T, ε))`
([N, §2.3]), a supremum over `ε > 0` by monotonicity. -/
noncomputable def lowerLocalEntropy (μ : Measure X) (T : X → X) (y : X) : ℝ≥0∞ :=
  ⨆ (ε : ℝ) (_ : 0 < ε), liminf (fun n : ℕ ↦ info (μ (bowenBall T n y ε)) / n) atTop

/-- The upper local entropy `h̄_μ(T, y) = lim_{ε→0} limsup_n -(1/n) log μ(B_n(y, T, ε))`
([N, §2.3]). -/
noncomputable def upperLocalEntropy (μ : Measure X) (T : X → X) (y : X) : ℝ≥0∞ :=
  ⨆ (ε : ℝ) (_ : 0 < ε), limsup (fun n : ℕ ↦ info (μ (bowenBall T n y ε)) / n) atTop

end Complexity

/-! ### Kolmogorov–Sinai entropy -/

section KS

variable {X : Type*} [MeasurableSpace X]

/-- A finite measurable partition `ξ = (ξ₀, …, ξ_{p-1})` of `X`. -/
def IsFinitePartition {p : ℕ} (ξ : Fin p → Set X) : Prop :=
  (∀ i, MeasurableSet (ξ i)) ∧ Pairwise (fun i j ↦ Disjoint (ξ i) (ξ j)) ∧ ⋃ i, ξ i = univ

/-- The cell `⋂_{k<n} T⁻ᵏ ξ_{w_k}` of the refinement `ξⁿ = ξ ∨ T⁻¹ξ ∨ ⋯ ∨ T⁻⁽ⁿ⁻¹⁾ξ`. -/
def refinementCell (T : X → X) {p : ℕ} (ξ : Fin p → Set X) (n : ℕ) (w : Fin n → Fin p) :
    Set X :=
  ⋂ k : Fin n, T^[k] ⁻¹' ξ (w k)

/-- The Shannon entropy in bits `H_μ(ξⁿ) = -∑_w μ(C_w) log μ(C_w)` of the refinement `ξⁿ`. -/
noncomputable def refinementEntropy (μ : Measure X) (T : X → X) {p : ℕ} (ξ : Fin p → Set X)
    (n : ℕ) : ℝ :=
  ∑ w : Fin n → Fin p,
    -(μ (refinementCell T ξ n w)).toReal * Real.logb 2 (μ (refinementCell T ξ n w)).toReal

/-- The Kolmogorov–Sinai entropy `h_μ(T) = sup_ξ lim_n (1/n) H_μ(ξⁿ)` in bits, the supremum over
finite measurable partitions ([C, §1]). For invariant `μ` the limit exists (Fekete); `limsup`
is used so that the definition makes sense for every `μ`. -/
noncomputable def ksEntropy (μ : Measure X) (T : X → X) : ℝ≥0∞ :=
  ⨆ (p : ℕ) (ξ : Fin p → Set X) (_ : IsFinitePartition ξ),
    limsup (fun n : ℕ ↦ ENNReal.ofReal (refinementEntropy μ T ξ n / n)) atTop

end KS

/-! ### The statements -/

/-- [N, Theorem 3.3], first half: if `A` is admissible for `(X, d, T, μ)`, then at every point
`K̲^A(y, T) ≤ h̲_μ(T, y)` and `K̄^A(y, T) ≤ h̄_μ(T, y)`. Here `X` is a complete metric space with
dense ideal points `(xᵢ)` (separable), `T` is continuous (as in [N, §2.1]; this also follows from
admissibility), and `μ` is a Borel measure of total mass at most `1` (the note states it for
probability measures). No invariance, ergodicity or compactness. -/
def Theorem3_3_upper : Prop :=
  ∀ (X : Type u) [MetricSpace X] [CompleteSpace X] [MeasurableSpace X] [BorelSpace X]
    (x : ℕ → X) (T : X → X) (A : Set ℕ) (μ : Measure X),
    Continuous T → μ univ ≤ 1 → IsAdmissible x T μ A → ∀ y : X,
      lowerOrbitComplexity x T A y ≤ lowerLocalEntropy μ T y ∧
        upperOrbitComplexity x T A y ≤ upperLocalEntropy μ T y

/-- [N, Theorem 3.3]: if `A` is admissible for `(X, d, T, μ)` with `μ` a Borel probability
measure, then at every point `y` that is `μ`-random relative to `A`,
`K̲^A(y, T) = h̲_μ(T, y)` and `K̄^A(y, T) = h̄_μ(T, y)`. Same setting as `Theorem3_3_upper`. -/
def Theorem3_3 : Prop :=
  ∀ (X : Type u) [MetricSpace X] [CompleteSpace X] [MeasurableSpace X] [BorelSpace X]
    (x : ℕ → X) (T : X → X) (A : Set ℕ) (μ : Measure X) [IsProbabilityMeasure μ],
    Continuous T → IsAdmissible x T μ A → ∀ y ∈ MLRandom x A μ,
      lowerOrbitComplexity x T A y = lowerLocalEntropy μ T y ∧
        upperOrbitComplexity x T A y = upperLocalEntropy μ T y

/-- [C, Theorem 1]: let `X` be a compact metric space with ideal points `(xᵢ)`, `T : X → X`, and
`μ` a `T`-invariant ergodic Borel probability measure (Mathlib's `Ergodic T μ` includes
invariance), and let `A` compute the metric structure, `T` and `μ`. Then at every point `y`
that is Martin-Löf random for `μ` relative to `A`, `K̲^A(y, T) = K̄^A(y, T) = h_μ(T)`, including
when `h_μ(T) = ∞`. `Continuous T` is listed separately, as in `Theorem3_3`, although it follows
from `A`-computability of `T` (the companion does not list it). -/
def Theorem1 : Prop :=
  ∀ (X : Type u) [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
    (x : ℕ → X) (T : X → X) (A : Set ℕ) (μ : Measure X) [IsProbabilityMeasure μ],
    Continuous T → IsAdmissible x T μ A → Ergodic T μ → ∀ y ∈ MLRandom x A μ,
      lowerOrbitComplexity x T A y = ksEntropy μ T ∧ upperOrbitComplexity x T A y = ksEntropy μ T

/-! ### Sanity checks (from the definitions alone) -/

/-- The Bowen ball of length `1` is the ball. -/
theorem bowenBall_one {X : Type*} [MetricSpace X] (T : X → X) (y : X) (ε : ℝ) :
    bowenBall T 1 y ε = Metric.ball y ε := by
  ext z
  simp [bowenBall, Metric.mem_ball, dist_comm]

/-- Randomness is antitone in the oracle: a point random relative to `B` is random relative to
every `A ≤_T B`, since every test relative to `A` is a test relative to `B`. -/
theorem mlRandom_anti {X : Type*} [MetricSpace X] [MeasurableSpace X] (x : ℕ → X)
    (μ : Measure X) {A B : Set ℕ} (hAB : charOracle A ≤ᵀ charOracle B) :
    MLRandom x B μ ⊆ MLRandom x A μ := by
  rintro y hy U ⟨⟨E, hE, hU⟩, hμ⟩
  exact hy U ⟨⟨E, hE.mono_oracle hAB, hU⟩, hμ⟩

end Kolmogorov.Trusted
