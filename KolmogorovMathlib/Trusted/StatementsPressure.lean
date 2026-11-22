/-
Copyright (c) 2026 Emma Dinowitz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emma Dinowitz
-/
import Mathlib
import KolmogorovMathlib.Trusted.Statements
import KolmogorovMathlib.Oracle.Basic
import KolmogorovMathlib.Oracle.PrefixComplexity.Basic

/-!
# Trusted statements: pressure and BS dimension (Theorem 8.3 and Corollary 8.4)

This file continues `KolmogorovMathlib.Trusted.Statements` (whose definitions it reuses: Bowen
balls, admissible oracles, Martin-Löf random points, the information `info`). It defines, in
textbook style, the notions of [N, §8] (*Entropy of non-invariant measures and orbit complexity
of random points*) and of [Din] that §8 recalls, and states:

* `Theorem8_3_pressure` ([N, Thm. 8.3(ii)], pressure): at a random point with
  `inf_n S_n φ(y) / n > -∞`, the lower and upper pointwise pressures equal the lower and upper
  local pressures of `μ`;
* `Theorem8_3_bsDimension` ([N, Thm. 8.3(ii)], BS dimension): at a random point with positive
  lower Birkhoff average of `u`, the pointwise BS dimensions equal the local BS dimensions;
* `Corollary8_4_pressure` ([N, Cor. 8.4(c)], pressure): the lower and upper pressures of a set
  are the minima over Borel probability measures of the suprema of the local pressures over the
  set, attained by purely atomic measures;
* `Corollary8_4_bsDimension` ([N, Cor. 8.4(c)], BS dimension): the same for the BS dimensions.

The proofs are in `KolmogorovMathlib.Trusted.BridgePressure`, which also proves that every
definition below agrees with the library's: unconditionally, except that the local pressure
agrees for finite measures (the statements use probability measures).

## What is trusted

Besides Mathlib (in particular `birkhoffSum f g n x = ∑_{k<n} g (f^[k] x)`, the Birkhoff sum
`S_n g`, and `ENNReal.log : [0, ∞] → [-∞, ∞]`, the natural logarithm with `log 0 = -∞`,
`log ∞ = ∞`), this file uses only `KolmogorovMathlib.Trusted.Statements` and the library's
computability foundations listed there (`oracleNatComplexity A i = K^A(i)`, `IsREIn`).

Import closure (checked with a script that follows `import` lines): `Mathlib`, the pilot
`KolmogorovMathlib.Trusted.Statements`, `KolmogorovMathlib.Oracle.Basic` and
`KolmogorovMathlib.Oracle.PrefixComplexity.Basic`, 235 library modules in all (the 234 of the
pilot and the pilot itself); no module under `KolmogorovMathlib/PointToSet/` or
`KolmogorovMathlib/Ergodic/`.

## Conventions

* `log` is base 2. Pressures take values in `[-∞, ∞]` (`EReal`), BS dimensions in `[0, ∞]`
  (`ℝ≥0∞`).
* Limits as `ε → 0` of quantities that are nondecreasing as `ε ↓ 0` are written as suprema over
  `ε > 0` (for the local pressure this monotonicity uses that `μ` is finite); limits as
  `N → ∞` of quantities nondecreasing in `N` are written as suprema over `N ≥ 1`.
* At `n = 0` a few of the rates below take junk values (division by `0 = 0` in `ℝ`); a single
  term does not affect a `liminf` or `limsup` in `n`.
* Set pressures and BS dimensions are Carathéodory constructions with countable covers by Bowen
  balls. Each docstring says how the definition compares with the textbook one ([Din, Thms. A,
  B]; Pesin–Pitskel, Barreira–Schmeling): the library's choices of weights (centered for the
  pressures, supremum for BS) and of the countable modification are kept, since they are what the
  library's theorems are about.
-/

namespace Kolmogorov.Trusted

open MeasureTheory Filter Set
open scoped ENNReal Computability
open Kolmogorov.PointToSet (oracleNatComplexity)

universe u

section Pointwise

variable {X : Type*} [MetricSpace X]

/-! ### Birkhoff averages -/

/-- The lower Birkhoff average `u̲(y) = liminf_n S_n u(y) / n` ([N, §8]), in `[-∞, ∞]`. -/
noncomputable def lowerBirkhoffAverage (T : X → X) (u : X → ℝ) (y : X) : EReal :=
  liminf (fun n : ℕ ↦ ((birkhoffSum T u n y / n : ℝ) : EReal)) atTop

/-- `inf_{n ≥ 1} S_n φ(y) / n > -∞` ([N, Thm. 8.3(i)]): the Birkhoff averages of `φ` at `y` are
bounded below. -/
def IsBirkhoffBoundedBelow (T : X → X) (φ : X → ℝ) (y : X) : Prop :=
  ∃ L : ℝ, ∀ n : ℕ, 1 ≤ n → L ≤ birkhoffSum T φ n y / n

/-! ### Pointwise pressure and BS dimension of a point ([Din, Defs. 3.12, 3.32]) -/

/-- `min_{xᵢ ∈ B_n(y, T, ε)} (K^A(i) + S_n φ(xᵢ)) / n` ([N, §8]), as an infimum in `[-∞, ∞]`
(`+∞` if the ball has no ideal point). -/
noncomputable def pressureCostN (x : ℕ → X) (T : X → X) (φ : X → ℝ) (A : Set ℕ) (y : X)
    (n : ℕ) (ε : ℝ) : EReal :=
  ⨅ (i : ℕ) (_ : x i ∈ bowenBall T n y ε),
    (((oracleNatComplexity A i + birkhoffSum T φ n (x i)) / n : ℝ) : EReal)

/-- The lower pointwise pressure
`P̲^A(y, T, φ) = lim_{ε→0} liminf_n min_{xᵢ ∈ B_n(y,T,ε)} (K^A(i) + S_n φ(xᵢ)) / n`
([N, §8], [Din, Def. 3.12]). -/
noncomputable def lowerPointwisePressure (x : ℕ → X) (T : X → X) (φ : X → ℝ) (A : Set ℕ)
    (y : X) : EReal :=
  ⨆ (ε : ℝ) (_ : 0 < ε), liminf (fun n ↦ pressureCostN x T φ A y n ε) atTop

/-- The upper pointwise pressure `P̄^A(y, T, φ)`, with `limsup` ([N, §8]). -/
noncomputable def upperPointwisePressure (x : ℕ → X) (T : X → X) (φ : X → ℝ) (A : Set ℕ)
    (y : X) : EReal :=
  ⨆ (ε : ℝ) (_ : 0 < ε), limsup (fun n ↦ pressureCostN x T φ A y n ε) atTop

/-- `min_{xᵢ ∈ B_n(y, T, ε)} K^A(i) / S_n u(xᵢ)` ([N, §8]), in `[0, ∞]`, over the ideal points of
the ball with `S_n u(xᵢ) > 0`. This filter keeps the quotient meaningful; for uniformly
continuous `u` (as in the statements) it has no effect on the limits below at points with
`u̲(y) > 0`, where they are used. (For `n = 0` the value is `∞`.) -/
noncomputable def bsCostN (x : ℕ → X) (T : X → X) (u : X → ℝ) (A : Set ℕ) (y : X) (n : ℕ)
    (ε : ℝ) : ℝ≥0∞ :=
  ⨅ (i : ℕ) (_ : x i ∈ bowenBall T n y ε) (_ : 0 < birkhoffSum T u n (x i)),
    (oracleNatComplexity A i : ℝ≥0∞) / ENNReal.ofReal (birkhoffSum T u n (x i))

/-- The lower pointwise BS dimension
`dim^A_BS(y, T, u) = lim_{ε→0} liminf_n min_{xᵢ ∈ B_n(y,T,ε)} K^A(i) / S_n u(xᵢ)`
([N, §8], [Din, Def. 3.32]; the note uses it where `u̲(y) > 0`). -/
noncomputable def lowerPointwiseBSDimension (x : ℕ → X) (T : X → X) (u : X → ℝ) (A : Set ℕ)
    (y : X) : ℝ≥0∞ :=
  ⨆ (ε : ℝ) (_ : 0 < ε), liminf (fun n ↦ bsCostN x T u A y n ε) atTop

/-- The upper pointwise BS dimension `Dim^A_BS(y, T, u)`, with `limsup` ([N, §8]). -/
noncomputable def upperPointwiseBSDimension (x : ℕ → X) (T : X → X) (u : X → ℝ) (A : Set ℕ)
    (y : X) : ℝ≥0∞ :=
  ⨆ (ε : ℝ) (_ : 0 < ε), limsup (fun n ↦ bsCostN x T u A y n ε) atTop

/-! ### Local pressure and local BS dimension of a measure ([N, Def. 8.1]) -/

variable [MeasurableSpace X]

/-- `(-log μ(B_n(y, T, ε)) + S_n φ(y)) / n` ([N, Def. 8.1]), in `[-∞, ∞]`: `+∞` when the Bowen
ball is null (`-log 0 = ∞`). The logarithm is not truncated. (Used for finite `μ`.) -/
noncomputable def localPressureN (μ : Measure X) (T : X → X) (φ : X → ℝ) (y : X) (n : ℕ)
    (ε : ℝ) : EReal :=
  if μ (bowenBall T n y ε) = 0 then ⊤ else
    (((-Real.logb 2 (μ (bowenBall T n y ε)).toReal + birkhoffSum T φ n y) / n : ℝ) : EReal)

/-- The lower local pressure
`P̲_μ(y, T, φ) = lim_{ε→0} liminf_n (-log μ(B_n(y, T, ε)) + S_n φ(y)) / n` ([N, Def. 8.1]). -/
noncomputable def lowerLocalPressure (μ : Measure X) (T : X → X) (φ : X → ℝ) (y : X) : EReal :=
  ⨆ (ε : ℝ) (_ : 0 < ε), liminf (fun n ↦ localPressureN μ T φ y n ε) atTop

/-- The upper local pressure `P̄_μ(y, T, φ)`, with `limsup` ([N, Def. 8.1]). -/
noncomputable def upperLocalPressure (μ : Measure X) (T : X → X) (φ : X → ℝ) (y : X) : EReal :=
  ⨆ (ε : ℝ) (_ : 0 < ε), limsup (fun n ↦ localPressureN μ T φ y n ε) atTop

/-- The lower local BS dimension
`d̲_μ(y, T, u) = lim_{ε→0} liminf_n -log μ(B_n(y, T, ε)) / S_n u(y)` ([N, Def. 8.1], for
`u̲(y) > 0`). The information `-log μ(B_n)` is `info` (truncated at `0`; no effect for
probability measures), and the denominator is `max(S_n u(y), 0)`, which differs from
`S_n u(y)` for finitely many `n` when `u̲(y) > 0`. -/
noncomputable def lowerLocalBSDimension (μ : Measure X) (T : X → X) (u : X → ℝ) (y : X) :
    ℝ≥0∞ :=
  ⨆ (ε : ℝ) (_ : 0 < ε),
    liminf (fun n ↦ info (μ (bowenBall T n y ε)) / ENNReal.ofReal (birkhoffSum T u n y)) atTop

/-- The upper local BS dimension `d̄_μ(y, T, u)`, with `limsup` ([N, Def. 8.1]). -/
noncomputable def upperLocalBSDimension (μ : Measure X) (T : X → X) (u : X → ℝ) (y : X) :
    ℝ≥0∞ :=
  ⨆ (ε : ℝ) (_ : 0 < ε),
    limsup (fun n ↦ info (μ (bowenBall T n y ε)) / ENNReal.ofReal (birkhoffSum T u n y)) atTop

/-- `μ` is purely atomic ([N, Cor. 8.4(c)]): it is concentrated on a countable set `S`
(`μ(X \ S) = 0`); for a Borel measure on a metric space (singletons are measurable) this means
that `μ = ∑_{a ∈ S} μ{a} δ_a` is a countable sum of point masses. -/
def IsPurelyAtomic (μ : Measure X) : Prop :=
  ∃ S : Set X, S.Countable ∧ μ Sᶜ = 0

end Pointwise

/-! ### Pressure and BS dimension of a set -/

section Sets

variable {X : Type*} [MetricSpace X]

/-- `(c_j, m_j)_{j ∈ I}` (`I ⊆ ℕ`, so the family is countable, possibly finite or empty) is a
cover of `Z` by Bowen balls `B_{m_j}(c_j, T, ε)` of orders `m_j ≥ N`. Repetitions are allowed. -/
def IsBowenCover (T : X → X) (Z : Set X) (ε : ℝ) (N : ℕ) {I : Set ℕ} (c : I → X) (m : I → ℕ) :
    Prop :=
  (∀ j, N ≤ m j) ∧ Z ⊆ ⋃ j, bowenBall T (m j) (c j) ε

/-- The pressure content `M(Z, s, ε, N) = inf ∑_j 2^{-s m_j} 2^{S_{m_j} φ(c_j)}` over countable
covers of `Z` by Bowen balls `B_{m_j}(c_j, T, ε)` of orders `m_j ≥ N`. The potential is evaluated
at the centers (the textbook Pesin–Pitskel content uses `sup_{B_{m_j}(c_j)} S_{m_j} φ`; for
uniformly continuous `φ` the two give the same pressure as `ε → 0`). -/
noncomputable def pressureContent (T : X → X) (φ : X → ℝ) (Z : Set X) (s ε : ℝ) (N : ℕ) :
    ℝ≥0∞ :=
  ⨅ (I : Set ℕ) (c : I → X) (m : I → ℕ) (_ : IsBowenCover T Z ε N c m),
    ∑' j, (2 : ℝ≥0∞) ^ (-s * m j) * (2 : ℝ≥0∞) ^ birkhoffSum T φ (m j) (c j)

/-- The lower pressure of a set ([N, Cor. 8.4], [Din, Thm. A]; Pesin–Pitskel's pressure in
base 2): `P̲(Z, T, φ) = lim_{ε→0} inf {s : lim_{N→∞} M(Z, s, ε, N) = 0}`, in `[-∞, ∞]`
(`inf ∅ = +∞`; `-∞` for `Z = ∅`). -/
noncomputable def lowerPressure (T : X → X) (φ : X → ℝ) (Z : Set X) : EReal :=
  ⨆ (ε : ℝ) (_ : 0 < ε),
    ⨅ (s : ℝ) (_ : ⨆ (N : ℕ) (_ : 1 ≤ N), pressureContent T φ Z s ε N = 0), (s : EReal)

/-- The partition sum `Λ(Y, n, ε) = inf ∑_{c ∈ F} 2^{S_n φ(c)}` over countable sets `F` of centers
with `Y ⊆ ⋃_{c ∈ F} B_n(c, T, ε)` (centers anywhere in `X`; potential at the centers). -/
noncomputable def pressurePartitionSum (T : X → X) (φ : X → ℝ) (Y : Set X) (n : ℕ) (ε : ℝ) :
    ℝ≥0∞ :=
  ⨅ (F : Set X) (_ : F.Countable ∧ Y ⊆ ⋃ c ∈ F, bowenBall T n c ε),
    ∑' c : F, (2 : ℝ≥0∞) ^ birkhoffSum T φ n c

/-- The upper pressure of a set ([N, Cor. 8.4], [Din, Thm. A]): the countably modified upper
capacity pressure
`P̄(Z, T, φ) = lim_{ε→0} inf_{Z ⊆ ⋃_k Y_k} sup_k limsup_n (1/n) log₂ Λ(Y_k, n, ε)`, in `[-∞, ∞]`.
Here `(1/n) log₂ q = ln q / (n ln 2)` with `ln = ENNReal.log`, and the pieces `Y_k` are arbitrary
subsets of `X`. For `φ = 0`, `Λ(Y, n, ε)` is the least number of Bowen balls `B_n(c, T, ε)`
covering `Y`, and this is the modified upper capacity entropy. -/
noncomputable def upperPressure (T : X → X) (φ : X → ℝ) (Z : Set X) : EReal :=
  ⨆ (ε : ℝ) (_ : 0 < ε), ⨅ (Y : ℕ → Set X) (_ : Z ⊆ ⋃ k, Y k), ⨆ k,
    limsup (fun n : ℕ ↦ ENNReal.log (pressurePartitionSum T φ (Y k) n ε) *
      (((n * Real.log 2)⁻¹ : ℝ) : EReal)) atTop

/-- The Barreira–Schmeling weight `2^{-s sup_{B_n(c,T,ε)} S_n u}` of a Bowen ball, written as
`(sup_{z ∈ B_n(c, T, ε)} 2^{S_n u(z)})^{-s}` (an `ℝ≥0∞` power, meaningful also when the
supremum is infinite). -/
noncomputable def bsWeight (T : X → X) (u : X → ℝ) (s : ℝ) (n : ℕ) (c : X) (ε : ℝ) : ℝ≥0∞ :=
  (⨆ z ∈ bowenBall T n c ε, (2 : ℝ≥0∞) ^ birkhoffSum T u n z) ^ (-s)

/-- The BS content `M(Z, s, ε, N) = inf ∑_j 2^{-s sup_{B_{m_j}(c_j)} S_{m_j} u}` over countable
covers of `Z` by Bowen balls of orders `m_j ≥ N`. -/
noncomputable def bsContent (T : X → X) (u : X → ℝ) (Z : Set X) (s ε : ℝ) (N : ℕ) : ℝ≥0∞ :=
  ⨅ (I : Set ℕ) (c : I → X) (m : I → ℕ) (_ : IsBowenCover T Z ε N c m),
    ∑' j, bsWeight T u s (m j) (c j) ε

/-- The (lower) Barreira–Schmeling dimension of a set ([N, Cor. 8.4], [Din, Thm. B]), the
classical definition in base 2:
`dim_BS(Z, T, u) = lim_{ε→0} inf {s ≥ 0 : lim_{N→∞} M(Z, s, ε, N) = 0}` (`inf ∅ = ∞`). -/
noncomputable def lowerBSDimension (T : X → X) (u : X → ℝ) (Z : Set X) : ℝ≥0∞ :=
  ⨆ (ε : ℝ) (_ : 0 < ε),
    ⨅ (s : ℝ) (_ : 0 ≤ s) (_ : ⨆ (N : ℕ) (_ : 1 ≤ N), bsContent T u Z s ε N = 0),
      ENNReal.ofReal s

/-- The fixed-order BS sum `Λ_s(Y, n, ε) = inf ∑_{c ∈ F} 2^{-s sup_{B_n(c,T,ε)} S_n u}` over
countable sets `F` of centers with `Y ⊆ ⋃_{c ∈ F} B_n(c, T, ε)`. -/
noncomputable def bsPartitionSum (T : X → X) (u : X → ℝ) (Y : Set X) (s ε : ℝ) (n : ℕ) :
    ℝ≥0∞ :=
  ⨅ (F : Set X) (_ : F.Countable ∧ Y ⊆ ⋃ c ∈ F, bowenBall T n c ε),
    ∑' c : F, bsWeight T u s n c ε

/-- The upper Barreira–Schmeling dimension of a set ([N, Cor. 8.4], [Din, Thm. B]): the
countably modified upper capacity BS dimension
`Dim_BS(Z, T, u) = lim_{ε→0} inf_{(Y_k)} sup_k inf {s ≥ 0 : limsup_n Λ_s(Y_k, n, ε) < ∞}`, the
infimum over countable covers `Z = ⋃_k Y_k` by subsets of `Z`. (Unlike `upperPressure`, the
pieces lie in `Z`, and the critical value uses finiteness of the `limsup`.) -/
noncomputable def upperBSDimension (T : X → X) (u : X → ℝ) (Z : Set X) : ℝ≥0∞ :=
  ⨆ (ε : ℝ) (_ : 0 < ε), ⨅ (Y : ℕ → Set X) (_ : (∀ k, Y k ⊆ Z) ∧ Z ⊆ ⋃ k, Y k), ⨆ k,
    ⨅ (s : ℝ) (_ : 0 ≤ s) (_ : limsup (fun n ↦ bsPartitionSum T u (Y k) s ε n) atTop < ⊤),
      ENNReal.ofReal s

end Sets

/-! ### The statements -/

/-- [N, Theorem 8.3(ii)], pressure: let `A` be admissible for `(X, d, T, μ)` with `μ` a Borel
probability measure, and `φ : X → ℝ` uniformly continuous (as in [N, §8]). At every point `y`
that is `μ`-random relative to `A` with `inf_n S_n φ(y) / n > -∞`,
`P̲^A(y, T, φ) = P̲_μ(y, T, φ)` and `P̄^A(y, T, φ) = P̄_μ(y, T, φ)`. Same setting as
`Theorem3_3` (complete `X`, dense ideal points `(xᵢ)`, `Continuous T` listed separately). -/
def Theorem8_3_pressure : Prop :=
  ∀ (X : Type u) [MetricSpace X] [CompleteSpace X] [MeasurableSpace X] [BorelSpace X]
    (x : ℕ → X) (T : X → X) (φ : X → ℝ) (A : Set ℕ) (μ : Measure X) [IsProbabilityMeasure μ],
    Continuous T → UniformContinuous φ → IsAdmissible x T μ A →
    ∀ y ∈ MLRandom x A μ, IsBirkhoffBoundedBelow T φ y →
      lowerPointwisePressure x T φ A y = lowerLocalPressure μ T φ y ∧
        upperPointwisePressure x T φ A y = upperLocalPressure μ T φ y

/-- [N, Theorem 8.3(ii)], BS dimension: let `A` be admissible for `(X, d, T, μ)` with `μ` a
Borel probability measure, and `u : X → ℝ` uniformly continuous. At every point `y` that is
`μ`-random relative to `A` with `u̲(y) > 0`, `dim^A_BS(y, T, u) = d̲_μ(y, T, u)` and
`Dim^A_BS(y, T, u) = d̄_μ(y, T, u)`. Same setting as `Theorem8_3_pressure`. -/
def Theorem8_3_bsDimension : Prop :=
  ∀ (X : Type u) [MetricSpace X] [CompleteSpace X] [MeasurableSpace X] [BorelSpace X]
    (x : ℕ → X) (T : X → X) (u : X → ℝ) (A : Set ℕ) (μ : Measure X) [IsProbabilityMeasure μ],
    Continuous T → UniformContinuous u → IsAdmissible x T μ A →
    ∀ y ∈ MLRandom x A μ, 0 < lowerBirkhoffAverage T u y →
      lowerPointwiseBSDimension x T u A y = lowerLocalBSDimension μ T u y ∧
        upperPointwiseBSDimension x T u A y = upperLocalBSDimension μ T u y

/-- [N, Corollary 8.4(c)], pressure: let `X` be a complete separable metric space, `T`
continuous and `φ` uniformly continuous, and let `Z ⊆ X` with `inf_n S_n φ(y) / n > -∞` for
every `y ∈ Z`. Then `P̲(Z, T, φ) = min_μ sup_{y ∈ Z} P̲_μ(y, T, φ)` over Borel probability
measures `μ`, the minimum being attained by a purely atomic measure, and the same for
`P̄(Z, T, φ)` with `P̄_μ`. Each part is stated as "`=` the infimum" and "`=` the value at a
purely atomic probability measure". The note assumes `Z` nonempty; here `Z` is arbitrary, and
`X` is assumed nonempty instead (on the empty space there is no probability measure). -/
def Corollary8_4_pressure : Prop :=
  ∀ (X : Type u) [MetricSpace X] [CompleteSpace X] [TopologicalSpace.SeparableSpace X]
    [Nonempty X] [MeasurableSpace X] [BorelSpace X] (T : X → X) (φ : X → ℝ),
    Continuous T → UniformContinuous φ →
    ∀ Z : Set X, (∀ y ∈ Z, IsBirkhoffBoundedBelow T φ y) →
      (lowerPressure T φ Z = ⨅ (μ : Measure X) (_ : IsProbabilityMeasure μ),
          ⨆ y ∈ Z, lowerLocalPressure μ T φ y) ∧
      (∃ μ : Measure X, IsProbabilityMeasure μ ∧ IsPurelyAtomic μ ∧
          lowerPressure T φ Z = ⨆ y ∈ Z, lowerLocalPressure μ T φ y) ∧
      (upperPressure T φ Z = ⨅ (μ : Measure X) (_ : IsProbabilityMeasure μ),
          ⨆ y ∈ Z, upperLocalPressure μ T φ y) ∧
      (∃ μ : Measure X, IsProbabilityMeasure μ ∧ IsPurelyAtomic μ ∧
          upperPressure T φ Z = ⨆ y ∈ Z, upperLocalPressure μ T φ y)

/-- [N, Corollary 8.4(c)], BS dimension: let `X` be a complete separable metric space, `T`
continuous and `u` uniformly continuous, and let `Z ⊆ X` with `u̲(y) > 0` for every `y ∈ Z`.
Then `dim_BS(Z, T, u) = min_μ sup_{y ∈ Z} d̲_μ(y, T, u)` over Borel probability measures `μ`,
the minimum being attained by a purely atomic measure, and the same for `Dim_BS(Z, T, u)` with
`d̄_μ`. As in `Corollary8_4_pressure`, `Z` is arbitrary and `X` nonempty. -/
def Corollary8_4_bsDimension : Prop :=
  ∀ (X : Type u) [MetricSpace X] [CompleteSpace X] [TopologicalSpace.SeparableSpace X]
    [Nonempty X] [MeasurableSpace X] [BorelSpace X] (T : X → X) (u : X → ℝ),
    Continuous T → UniformContinuous u →
    ∀ Z : Set X, (∀ y ∈ Z, 0 < lowerBirkhoffAverage T u y) →
      (lowerBSDimension T u Z = ⨅ (μ : Measure X) (_ : IsProbabilityMeasure μ),
          ⨆ y ∈ Z, lowerLocalBSDimension μ T u y) ∧
      (∃ μ : Measure X, IsProbabilityMeasure μ ∧ IsPurelyAtomic μ ∧
          lowerBSDimension T u Z = ⨆ y ∈ Z, lowerLocalBSDimension μ T u y) ∧
      (upperBSDimension T u Z = ⨅ (μ : Measure X) (_ : IsProbabilityMeasure μ),
          ⨆ y ∈ Z, upperLocalBSDimension μ T u y) ∧
      (∃ μ : Measure X, IsProbabilityMeasure μ ∧ IsPurelyAtomic μ ∧
          upperBSDimension T u Z = ⨆ y ∈ Z, upperLocalBSDimension μ T u y)

/-! ### Sanity checks (from the definitions alone) -/

/-- For `u = 1` the Birkhoff sum is `n`, so the lower Birkhoff average is `1`. -/
theorem lowerBirkhoffAverage_one {X : Type*} [MetricSpace X] (T : X → X) (y : X) :
    lowerBirkhoffAverage T (fun _ ↦ 1) y = 1 := by
  have h : (fun n : ℕ ↦ ((birkhoffSum T (fun _ ↦ (1 : ℝ)) n y / n : ℝ) : EReal)) =ᶠ[atTop]
      fun _ ↦ 1 := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn' : (n : ℝ) ≠ 0 := by positivity
    simp [birkhoffSum, hn']
  rw [lowerBirkhoffAverage, liminf_congr h, liminf_const]

/-- A Dirac mass is purely atomic. -/
theorem isPurelyAtomic_dirac {X : Type*} [MetricSpace X] [MeasurableSpace X]
    [MeasurableSingletonClass X] (a : X) : IsPurelyAtomic (Measure.dirac a) :=
  ⟨{a}, countable_singleton a, by simp⟩

end Kolmogorov.Trusted
