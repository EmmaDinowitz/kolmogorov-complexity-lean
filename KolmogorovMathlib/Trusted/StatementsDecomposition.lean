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
# Trusted statements: Theorem 3.3 at a fixed scale, Theorems 7.3 and 7.5, Jacobs' theorem

This file continues `KolmogorovMathlib.Trusted.Statements` (the "pilot"), whose definitions it
reuses: Bowen balls, admissible oracles, the orbit complexities `K̲^A`, `K̄^A`, the local
entropies `h̲_μ`, `h̄_μ` and the Kolmogorov–Sinai entropy `ksEntropy`. It states, as `Prop`s
without proofs, the following results of

* [N] *Entropy of non-invariant measures and orbit complexity of random points*, and
* Jacobs' theorem ([Wal, Ch. 8]), used in [N, Thm. 7.5(b)] and in [N, Rem. 6.7]:

* `Theorem3_3_fixedScale` ([N, Thm. 3.3(i)]): `K̲^A(y, T, 6ε) ≤ h̲_μ(T, y, ε)` and
  `K̄^A(y, T, 6ε) ≤ h̄_μ(T, y, ε)` at every point and every rational scale `ε > 0`;
* `Theorem3_3_ae` ([N, Thm. 3.3], almost-everywhere form): `K̲^A = h̲_μ` and `K̄^A = h̄_μ`
  `μ`-almost everywhere;
* `Theorem7_3_a` ([N, Thm. 7.3(a)]): along an integral decomposition `μ = ∫ μ_ω dQ(ω)`, the
  local entropies of the component `μ_ω` at `x` are at most those of `μ`, for `M`-a.e. `(ω, x)`;
* `Theorem7_5_a` ([N, Thm. 7.5(a)]): equality there when `μ_ω ≪ μ` for a.e. `ω`;
* `Theorem7_5_b`, `Theorem7_5_b_fengHuang` ([N, Thm. 7.5(b)]): along an ergodic decomposition
  on a compact space, `h̲_μ(T, x) = h̄_μ(T, x) = h_{μ_ω}(T)`, `h̲_{μ_ω}(T, x) = h̲_μ(T, x)` and
  `h̄_{μ_ω}(T, x) = h̄_μ(T, x)` for `M`-a.e. `(ω, x)`, with `h_{μ_ω}(T)` the Kolmogorov–Sinai
  entropy, respectively the mean local entropy `∫ h̲_{μ_ω}(T, z) dμ_ω(z)` of the component;
* `JacobsTheorem`: on a compact metric space the Kolmogorov–Sinai entropy of a mixture of
  invariant measures is the mean of their entropies.

The proofs are in `KolmogorovMathlib.Trusted.BridgeDecomposition`, which also proves that the
fixed-scale notions below agree with the library's: the local entropies unconditionally, the
orbit complexities for continuous `T` and `ε > 0` (both are hypotheses where they are used).
The pilot's `ksEntropy` agrees with the library's for invariant probability measures; in
`Theorem7_5_b` and `JacobsTheorem` it is applied to almost every component, which is invariant
by hypothesis, and to the mixture, which is then invariant too (`measurePreserving_bind` in the
bridge).

## Integral decompositions (Mathlib vocabulary)

[N, §7] decomposes a measure `μ` on `X` as `μ = ∫ μ_ω dQ(ω)`, a family of measures `μ_ω`
indexed by a parameter `ω` of a measurable space `Ω`, averaged by a measure `Q` on `Ω`. The
statements use Mathlib's notions for this:

* `κ : Kernel Ω X` is a measurable family of measures `ω ↦ κ ω` on `X` (a kernel), the family
  `μ_ω = κ ω`; `IsFiniteKernel κ` says that the masses `κ ω X` are bounded, and
  `IsMarkovKernel κ` that every `κ ω` is a probability measure;
* `Q.bind κ` is the mixture `μ = ∫ κ ω dQ(ω)`, the measure `s ↦ ∫ κ ω (s) dQ(ω)`;
* `Q ⊗ₘ κ` is the measure `M` on `Ω × X` of [N, §7]: `ω` is drawn from `Q`, then `x` from
  `κ ω`; its second marginal is `Q.bind κ`;
* `ν ≪ μ` is absolute continuity (`μ s = 0 → ν s = 0`), `Ergodic T ν` says that `ν` is
  `T`-invariant and ergodic, and `MeasurePreserving T ν ν` that `ν` is `T`-invariant
  (with `T` measurable).

## What is trusted

As for the pilot: Mathlib, and from the library only `KolmogorovMathlib.Oracle.Basic` and
`KolmogorovMathlib.Oracle.PrefixComplexity.Basic` (through the pilot). Import closure (checked
with a script that follows `import` lines): the pilot's 234 library modules plus the pilot
itself; no module under `KolmogorovMathlib/PointToSet/` or `KolmogorovMathlib/Ergodic/`.

## Conventions

As in the pilot: `log` is base 2, all entropies and complexities are in `[0, ∞]` (`ℝ≥0∞`).
For a function that may fail to be measurable, `∫⁻` is Mathlib's lower Lebesgue integral; the
integrands below are almost everywhere measurable (proved in the library).
-/

namespace Kolmogorov.Trusted

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal

universe u v

/-! ### Orbit complexity and local entropies at a fixed scale -/

section FixedScale

variable {X : Type*} [MetricSpace X]

/-- The lower orbit complexity at the scale `ε`, `K̲^A(y, T, ε) = liminf_n K_n^A(y, T, ε) / n`
([N, §2.1]). The pilot's `lowerOrbitComplexity` is its supremum over `ε > 0`
(`lowerOrbitComplexity_eq_iSup` below). -/
noncomputable def lowerOrbitComplexityAt (x : ℕ → X) (T : X → X) (A : Set ℕ) (y : X)
    (ε : ℝ) : ℝ≥0∞ :=
  liminf (fun n : ℕ ↦ (orbitComplexityN x T A y n ε : ℝ≥0∞) / n) atTop

/-- The upper orbit complexity at the scale `ε`, `K̄^A(y, T, ε) = limsup_n K_n^A(y, T, ε) / n`
([N, §2.1]). -/
noncomputable def upperOrbitComplexityAt (x : ℕ → X) (T : X → X) (A : Set ℕ) (y : X)
    (ε : ℝ) : ℝ≥0∞ :=
  limsup (fun n : ℕ ↦ (orbitComplexityN x T A y n ε : ℝ≥0∞) / n) atTop

variable [MeasurableSpace X]

/-- The lower local entropy at the scale `ε`,
`h̲_μ(T, y, ε) = liminf_n -(1/n) log μ(B_n(y, T, ε))` ([N, §2.3]). -/
noncomputable def lowerLocalEntropyAt (μ : Measure X) (T : X → X) (y : X) (ε : ℝ) : ℝ≥0∞ :=
  liminf (fun n : ℕ ↦ info (μ (bowenBall T n y ε)) / n) atTop

/-- The upper local entropy at the scale `ε`,
`h̄_μ(T, y, ε) = limsup_n -(1/n) log μ(B_n(y, T, ε))` ([N, §2.3]). -/
noncomputable def upperLocalEntropyAt (μ : Measure X) (T : X → X) (y : X) (ε : ℝ) : ℝ≥0∞ :=
  limsup (fun n : ℕ ↦ info (μ (bowenBall T n y ε)) / n) atTop

omit [MeasurableSpace X] in
/-- The pilot's lower orbit complexity is the supremum of `K̲^A(y, T, ε)` over `ε > 0`. -/
theorem lowerOrbitComplexity_eq_iSup (x : ℕ → X) (T : X → X) (A : Set ℕ) (y : X) :
    lowerOrbitComplexity x T A y = ⨆ (ε : ℝ) (_ : 0 < ε), lowerOrbitComplexityAt x T A y ε :=
  rfl

omit [MeasurableSpace X] in
/-- The pilot's upper orbit complexity is the supremum of `K̄^A(y, T, ε)` over `ε > 0`. -/
theorem upperOrbitComplexity_eq_iSup (x : ℕ → X) (T : X → X) (A : Set ℕ) (y : X) :
    upperOrbitComplexity x T A y = ⨆ (ε : ℝ) (_ : 0 < ε), upperOrbitComplexityAt x T A y ε :=
  rfl

/-- The pilot's lower local entropy is the supremum of `h̲_μ(T, y, ε)` over `ε > 0`. -/
theorem lowerLocalEntropy_eq_iSup (μ : Measure X) (T : X → X) (y : X) :
    lowerLocalEntropy μ T y = ⨆ (ε : ℝ) (_ : 0 < ε), lowerLocalEntropyAt μ T y ε :=
  rfl

/-- The pilot's upper local entropy is the supremum of `h̄_μ(T, y, ε)` over `ε > 0`. -/
theorem upperLocalEntropy_eq_iSup (μ : Measure X) (T : X → X) (y : X) :
    upperLocalEntropy μ T y = ⨆ (ε : ℝ) (_ : 0 < ε), upperLocalEntropyAt μ T y ε :=
  rfl

end FixedScale

/-! ### Theorem 3.3: the fixed-scale and almost-everywhere forms -/

/-- [N, Theorem 3.3(i)], at a fixed scale: if `A` is admissible for `(X, d, T, μ)` and `ε > 0`
is rational, then at every point `K̲^A(y, T, 6ε) ≤ h̲_μ(T, y, ε)` and
`K̄^A(y, T, 6ε) ≤ h̄_μ(T, y, ε)`. Same setting as the pilot's `Theorem3_3_upper`: `X` complete
with dense ideal points `(xᵢ)`, `T` continuous, `μ` a Borel measure of total mass at most `1`
(the note states it for probability measures). As in the note, `ε` is rational. -/
def Theorem3_3_fixedScale : Prop :=
  ∀ (X : Type u) [MetricSpace X] [CompleteSpace X] [MeasurableSpace X] [BorelSpace X]
    (x : ℕ → X) (T : X → X) (A : Set ℕ) (μ : Measure X),
    Continuous T → μ univ ≤ 1 → IsAdmissible x T μ A → ∀ ε : ℚ, 0 < ε → ∀ y : X,
      lowerOrbitComplexityAt x T A y (6 * ε) ≤ lowerLocalEntropyAt μ T y ε ∧
        upperOrbitComplexityAt x T A y (6 * ε) ≤ upperLocalEntropyAt μ T y ε

/-- [N, Theorem 3.3], almost-everywhere form (not stated in the note; it follows since random
points have full measure): if `A` is admissible for `(X, d, T, μ)` with `μ` a Borel probability
measure, then `K̲^A(y, T) = h̲_μ(T, y)` and `K̄^A(y, T) = h̄_μ(T, y)` for `μ`-almost every `y`.
Same setting as the pilot's `Theorem3_3`. -/
def Theorem3_3_ae : Prop :=
  ∀ (X : Type u) [MetricSpace X] [CompleteSpace X] [MeasurableSpace X] [BorelSpace X]
    (x : ℕ → X) (T : X → X) (A : Set ℕ) (μ : Measure X) [IsProbabilityMeasure μ],
    Continuous T → IsAdmissible x T μ A → ∀ᵐ y ∂μ,
      lowerOrbitComplexity x T A y = lowerLocalEntropy μ T y ∧
        upperOrbitComplexity x T A y = upperLocalEntropy μ T y

/-! ### Integral decompositions: Theorems 7.3(a) and 7.5 -/

/-- [N, Theorem 7.3(a)]: for an integral decomposition `μ = ∫ μ_ω dQ(ω)` (`μ_ω = κ ω`,
`μ = Q.bind κ`) and `M = Q ⊗ κ`, for `M`-almost every `(ω, x)`
`h̲_{μ_ω}(T, x) ≤ h̲_μ(T, x)` and `h̄_{μ_ω}(T, x) ≤ h̄_μ(T, x)`.
`X` is a separable (equivalently, second-countable) metric space with its Borel σ-algebra and
`T` is continuous; `Q` and the `μ_ω` need only be finite, with bounded masses (the note has
probability measures); no completeness, invariance or standard Borel assumption. -/
def Theorem7_3_a : Prop :=
  ∀ (X : Type u) [MetricSpace X] [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X]
    (Ω : Type v) [MeasurableSpace Ω] (T : X → X) (Q : Measure Ω) [IsFiniteMeasure Q]
    (κ : Kernel Ω X) [IsFiniteKernel κ],
    Continuous T → ∀ᵐ p ∂(Q ⊗ₘ κ),
      lowerLocalEntropy (κ p.1) T p.2 ≤ lowerLocalEntropy (Q.bind κ) T p.2 ∧
        upperLocalEntropy (κ p.1) T p.2 ≤ upperLocalEntropy (Q.bind κ) T p.2

/-- [N, Theorem 7.5(a)]: in the setting of `Theorem7_3_a`, if `μ_ω ≪ μ` for `Q`-almost every
`ω`, then `h̲_{μ_ω}(T, x) = h̲_μ(T, x)` and `h̄_{μ_ω}(T, x) = h̄_μ(T, x)` for `M`-almost every
`(ω, x)` (which is integral affinity, by [N, Thm. 7.3(b)]). Finite `Q` and `μ_ω`, as in
`Theorem7_3_a`. -/
def Theorem7_5_a : Prop :=
  ∀ (X : Type u) [MetricSpace X] [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X]
    (Ω : Type v) [MeasurableSpace Ω] (T : X → X) (Q : Measure Ω) [IsFiniteMeasure Q]
    (κ : Kernel Ω X) [IsFiniteKernel κ],
    Continuous T → (∀ᵐ ω ∂Q, κ ω ≪ Q.bind κ) → ∀ᵐ p ∂(Q ⊗ₘ κ),
      lowerLocalEntropy (κ p.1) T p.2 = lowerLocalEntropy (Q.bind κ) T p.2 ∧
        upperLocalEntropy (κ p.1) T p.2 = upperLocalEntropy (Q.bind κ) T p.2

/-- [N, Theorem 7.5(b)], with the Kolmogorov–Sinai entropy: let `X` be a compact metric space,
`T` continuous, and `μ = ∫ μ_ω dQ(ω)` (`Q` a probability measure, every `μ_ω = κ ω` a
probability measure) a `T`-invariant measure whose components `μ_ω` are ergodic (and invariant)
for `Q`-almost every `ω` — an ergodic decomposition of `μ`. Then for `M`-almost every `(ω, x)`:
`h̲_μ(T, x) = h̄_μ(T, x) = h_{μ_ω}(T)`, and `h̲_{μ_ω}(T, x) = h̲_μ(T, x)`,
`h̄_{μ_ω}(T, x) = h̄_μ(T, x)` (integral affinity).

Differences with the note: its hypothesis `h_μ(T) < ∞` is not needed (values may be `∞`); the
invariance of `μ` is listed as in the note although it follows from that of the components;
integral affinity, the note's conclusion, is stated in its almost-everywhere form
`h̲_{μ_ω} = h̲_μ`, `h̄_{μ_ω} = h̄_μ` (equivalent by [N, Thm. 7.3(b)]). -/
def Theorem7_5_b : Prop :=
  ∀ (X : Type u) [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
    (Ω : Type v) [MeasurableSpace Ω] (T : X → X) (Q : Measure Ω) [IsProbabilityMeasure Q]
    (κ : Kernel Ω X) [IsMarkovKernel κ],
    Continuous T → MeasurePreserving T (Q.bind κ) (Q.bind κ) → (∀ᵐ ω ∂Q, Ergodic T (κ ω)) →
      ∀ᵐ p ∂(Q ⊗ₘ κ),
        lowerLocalEntropy (Q.bind κ) T p.2 = ksEntropy (κ p.1) T ∧
          upperLocalEntropy (Q.bind κ) T p.2 = ksEntropy (κ p.1) T ∧
          lowerLocalEntropy (κ p.1) T p.2 = lowerLocalEntropy (Q.bind κ) T p.2 ∧
          upperLocalEntropy (κ p.1) T p.2 = upperLocalEntropy (Q.bind κ) T p.2

/-- [N, Theorem 7.5(b)], with the entropy of the component written as its mean lower local
entropy `∫ h̲_{μ_ω}(T, z) dμ_ω(z)` (the Feng–Huang entropy of [N, §4]; for an ergodic `μ_ω`
it equals `h_{μ_ω}(T)`). Same hypotheses and the same remarks as `Theorem7_5_b`. -/
def Theorem7_5_b_fengHuang : Prop :=
  ∀ (X : Type u) [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
    (Ω : Type v) [MeasurableSpace Ω] (T : X → X) (Q : Measure Ω) [IsProbabilityMeasure Q]
    (κ : Kernel Ω X) [IsMarkovKernel κ],
    Continuous T → MeasurePreserving T (Q.bind κ) (Q.bind κ) → (∀ᵐ ω ∂Q, Ergodic T (κ ω)) →
      ∀ᵐ p ∂(Q ⊗ₘ κ),
        lowerLocalEntropy (Q.bind κ) T p.2 = ∫⁻ z, lowerLocalEntropy (κ p.1) T z ∂(κ p.1) ∧
          upperLocalEntropy (Q.bind κ) T p.2 = ∫⁻ z, lowerLocalEntropy (κ p.1) T z ∂(κ p.1) ∧
          lowerLocalEntropy (κ p.1) T p.2 = lowerLocalEntropy (Q.bind κ) T p.2 ∧
          upperLocalEntropy (κ p.1) T p.2 = upperLocalEntropy (Q.bind κ) T p.2

/-! ### Jacobs' theorem -/

/-- Jacobs' theorem ([Wal, Ch. 8], quoted in [N, Thm. 7.5(b)]): let `X` be a compact metric
space, `ρ` a probability measure on `Ω` and `κ ω` probability measures on `X`, `T`-invariant for
`ρ`-almost every `ω`. Then the Kolmogorov–Sinai entropy of the mixture `∫ κ ω dρ(ω)` is the mean
of the entropies of the components: `h_{∫ κ ω dρ}(T) = ∫ h_{κ ω}(T) dρ(ω)`.
No continuity of `T` and no ergodicity; the invariance of the mixture follows. The integrand
`ω ↦ h_{κ ω}(T)` is almost everywhere measurable (`aemeasurable_ksEntropy` in the bridge), so
the right side is an honest integral. -/
def JacobsTheorem : Prop :=
  ∀ (X : Type u) [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
    (Ω : Type v) [MeasurableSpace Ω] (T : X → X) (ρ : Measure Ω) [IsProbabilityMeasure ρ]
    (κ : Kernel Ω X) [IsMarkovKernel κ],
    (∀ᵐ ω ∂ρ, MeasurePreserving T (κ ω) (κ ω)) →
      ksEntropy (ρ.bind κ) T = ∫⁻ ω, ksEntropy (κ ω) T ∂ρ

end Kolmogorov.Trusted
