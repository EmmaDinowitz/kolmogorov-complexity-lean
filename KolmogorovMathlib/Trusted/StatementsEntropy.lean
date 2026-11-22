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
# Trusted statements: entropies of sets (Theorem 2.1, Theorem 4.3, Corollaries 4.2 and 6.5)

This file continues `KolmogorovMathlib.Trusted.Statements` (whose definitions it reuses: Bowen
balls, admissible oracles, Martin-Löf random points, orbit complexities, local entropies). It
defines, in textbook style,

* the Bowen entropy `h̲(T, Z)` and the packing entropy `h̄(T, Z)` of an arbitrary set `Z`
  (the note writes them `h̲(Z, T)`, `h̄(Z, T)` and refers to [Din] for the definitions; we use
  Bowen's and Feng–Huang's classical definitions, in bits);
* the Feng–Huang entropies `h̲_μ(T) = ∫ h̲_μ(T, y) dμ(y)` and `h̄_μ(T) = ∫ h̄_μ(T, y) dμ(y)` of a
  measure ([N, §4.1]);
* the entropy law `Λ_μ`, the joint law of `(h̲_μ(T, ·), h̄_μ(T, ·))` under `μ` ([N, Def. 6.1]);

and states, without proofs:

* `Theorem2_1_lower`, `Theorem2_1_upper` ([N, Thm. 2.1], the point-to-set principle for entropy,
  cited from [Din]): `h̲(T, Z) = min_A sup_{y ∈ Z} K̲^A(y, T)`, the same for `h̄`, `K̄`;
* `Corollary4_2` ([N, Cor. 4.2]) and the Feng–Huang variational principle
  (`VariationalPrinciple`, `PackingVariationalInequality`) that it rests on;
* `Theorem4_3_a`, `Theorem4_3_b`, `Theorem4_3_c` ([N, Thm. 4.3]): essential suprema and infima
  of the local entropies in terms of orbit complexities of random points and entropies of sets;
* `Corollary6_5_a`, `Corollary6_5_b`, `Corollary6_5_c` ([N, Cor. 6.5]).

The proofs are in `KolmogorovMathlib.Trusted.BridgeEntropy`, which also proves that the new
definitions agree with the library's: `bowenEntropy_eq` (unconditionally, with the library's
`lowerEntropy`), `packingEntropy_eq` (with the library's `upperEntropy P T`, for continuous `T`;
this goes through the library's identification of `upperEntropy` with the zero-potential packing
pressure), `lowerMeasureEntropy_eq`, `upperMeasureEntropy_eq` and `entropyLaw_eq`
(unconditionally, with `measureEntropy` and `entropyLaw`).

## What is trusted

Besides Mathlib, the pilot file `KolmogorovMathlib.Trusted.Statements` and its foundations
(`ComputableIn`, `IsREIn`, `oracleNatComplexity`; see there). Import closure (checked with a
script that follows `import` lines): `Mathlib`, `KolmogorovMathlib.Trusted.Statements`,
`KolmogorovMathlib.Oracle.Basic` and `KolmogorovMathlib.Oracle.PrefixComplexity.Basic`, the same
234 library modules as the pilot; no module under `KolmogorovMathlib/PointToSet/` or
`KolmogorovMathlib/Ergodic/`.

## Conventions

* As in the pilot: `log` is base 2, all entropies are in `[0, ∞]` (`ℝ≥0∞`), and limits as
  `ε → 0` of quantities nondecreasing as `ε ↓ 0` are written as suprema over `ε > 0`.
* Critical values are infima over `s ≥ 0`: the infimum of the empty set is `∞`, and the
  entropies of the empty set are `0`.
* Sets `Z ⊆ X` are arbitrary, and `μ Z` is Mathlib's outer measure of `Z` (for measurable `Z`
  it is the measure). The suprema over measures are over the probability measures `μ` with
  `μ K = 1`, written `⨆ (μ : Measure X) (_ : IsProbabilityMeasure μ) (_ : μ K = 1), …`.
* `essSup f μ` and `essInf f μ` are Mathlib's essential supremum and infimum.
* "`min_A`" (attained infimum) is stated as an infimum together with an upper cone of oracles
  `{A : B ≤_T A}` on which the value is attained; likewise for "`max_B`".
-/

namespace Kolmogorov.Trusted

open MeasureTheory Filter Set
open scoped ENNReal Computability

universe u

/-! ### Entropies of sets -/

section SetEntropy

variable {X : Type*} [MetricSpace X]

/-- Bowen's content `M(Z, s, ε, N) = inf Σⱼ 2^{-s nⱼ}` over the countable covers
`Z ⊆ ⋃ⱼ B_{nⱼ}(yⱼ, T, ε)` by Bowen balls of orders `nⱼ ≥ N` (Bowen 1973, in Pesin's form with
Bowen balls; [N, §2] via [Din]). A cover is a family `(yⱼ, nⱼ)_{j ∈ J}` indexed by a set
`J ⊆ ℕ` (finite, infinite or empty); the centers `yⱼ ∈ X` are arbitrary. -/
noncomputable def bowenContent (T : X → X) (Z : Set X) (s ε : ℝ) (N : ℕ) : ℝ≥0∞ :=
  ⨅ (J : Set ℕ) (y : J → X) (n : J → ℕ)
    (_ : (∀ j, N ≤ n j) ∧ Z ⊆ ⋃ j, bowenBall T (n j) (y j) ε),
    ∑' j, (2 : ℝ≥0∞) ^ (-s * n j)

/-- The Bowen (topological) entropy `h̲(T, Z)` of an arbitrary set `Z`, in bits:
`h̲(T, Z) = lim_{ε→0} inf {s ≥ 0 : lim_{N→∞} M(Z, s, ε, N) = 0}`. The content is nondecreasing
in `N` and the critical value is nondecreasing as `ε ↓ 0`, so both limits are suprema.
`h̲(T, ∅) = 0`. -/
noncomputable def bowenEntropy (T : X → X) (Z : Set X) : ℝ≥0∞ :=
  ⨆ (ε : ℝ) (_ : 0 < ε),
    ⨅ (s : ℝ) (_ : 0 ≤ s) (_ : ⨆ N, bowenContent T Z s ε N = 0), ENNReal.ofReal s

/-- The packing content `P(Z, s, ε, N) = sup Σᵢ 2^{-s nᵢ}` over the countable packings of `Z`:
families of pairs `(yᵢ, nᵢ)` with centers `yᵢ ∈ Z`, orders `nᵢ ≥ N`, and pairwise disjoint
Bowen balls `B_{nᵢ}(yᵢ, T, ε)` (Feng–Huang, *Variational principles for topological entropies
of subsets*, J. Funct. Anal. 263 (2012), in bits). The balls are the open Bowen balls of the
pilot file; with closed Bowen balls the entropy (after `ε → 0`) is the same, since disjoint
closed balls of radius `ε` have disjoint open ones, and disjoint open balls of radius `ε` have
disjoint closed ones of radius `ε / 2`. -/
noncomputable def packingContent (T : X → X) (Z : Set X) (s ε : ℝ) (N : ℕ) : ℝ≥0∞ :=
  ⨆ (F : Set (X × ℕ)) (_ : F.Countable ∧ (∀ a ∈ F, a.1 ∈ Z ∧ N ≤ a.2) ∧
      F.Pairwise fun a b ↦ Disjoint (bowenBall T a.2 a.1 ε) (bowenBall T b.2 b.1 ε)),
    ∑' a : F, (2 : ℝ≥0∞) ^ (-s * (a : X × ℕ).2)

/-- The packing measure `𝒫(Z, s, ε) = inf Σⱼ lim_{N→∞} P(Zⱼ, s, ε, N)` over the countable covers
`Z ⊆ ⋃ⱼ Zⱼ` (Feng–Huang). `P(·, s, ε, N)` is nonincreasing in `N`, so the limit is the
infimum over `N`. -/
noncomputable def packingMeasure (T : X → X) (Z : Set X) (s ε : ℝ) : ℝ≥0∞ :=
  ⨅ (Y : ℕ → Set X) (_ : Z ⊆ ⋃ j, Y j), ∑' j, ⨅ N, packingContent T (Y j) s ε N

/-- The packing (topological) entropy `h̄(T, Z) = h^P_top(T, Z)` of an arbitrary set `Z`, in
bits: `h̄(T, Z) = lim_{ε→0} inf {s ≥ 0 : 𝒫(Z, s, ε) = 0}` (Feng–Huang), the limit being a
supremum since the critical value is nondecreasing as `ε ↓ 0`. Since the infimum is over
`s ≥ 0`, `h̄(T, ∅) = 0`. -/
noncomputable def packingEntropy (T : X → X) (Z : Set X) : ℝ≥0∞ :=
  ⨆ (ε : ℝ) (_ : 0 < ε),
    ⨅ (s : ℝ) (_ : 0 ≤ s) (_ : packingMeasure T Z s ε = 0), ENNReal.ofReal s

end SetEntropy

/-! ### Feng–Huang entropies of a measure and the entropy law -/

section MeasureEntropy

variable {X : Type*} [MetricSpace X] [MeasurableSpace X]

/-- The lower Feng–Huang entropy `h̲_μ(T) = ∫ h̲_μ(T, y) dμ(y)` of a measure ([N, §4.1]), as a
lower Lebesgue integral in `[0, ∞]` (`∫⁻`; for continuous `T` the integrand is measurable). -/
noncomputable def lowerMeasureEntropy (μ : Measure X) (T : X → X) : ℝ≥0∞ :=
  ∫⁻ y, lowerLocalEntropy μ T y ∂μ

/-- The upper Feng–Huang entropy `h̄_μ(T) = ∫ h̄_μ(T, y) dμ(y)` of a measure ([N, §4.1]). -/
noncomputable def upperMeasureEntropy (μ : Measure X) (T : X → X) : ℝ≥0∞ :=
  ∫⁻ y, upperLocalEntropy μ T y ∂μ

/-- The entropy law `Λ_μ = (Φ_μ)_* μ` ([N, Def. 6.1]): the push-forward of `μ` under
`Φ_μ(y) = (h̲_μ(T, y), h̄_μ(T, y))`, a measure on `[0, ∞]²` (the note restricts it to the
triangle `{s ≤ t}`, which carries it). Mathlib's `Measure.map` is `0` when `Φ_μ` is not
measurable; every statement below assumes `T` continuous, for which `Φ_μ` is measurable. -/
noncomputable def entropyLaw (μ : Measure X) (T : X → X) : Measure (ℝ≥0∞ × ℝ≥0∞) :=
  μ.map fun y ↦ (lowerLocalEntropy μ T y, upperLocalEntropy μ T y)

end MeasureEntropy

/-! ### Theorem 2.1: the point-to-set principle for entropy -/

/-- [N, Theorem 2.1] (from [Din]), Bowen entropy: for every set `Z`,
`h̲(T, Z) = min_A sup_{y ∈ Z} K̲^A(y, T)`, the minimum over all oracles `A ⊆ ℕ`, attained on an
upper cone of oracles. `X` is a complete metric space with dense ideal points `(xᵢ)`, relative
to which the orbit complexities are computed, and `T` is continuous ([N, §2.1]). The supremum
over `Z = ∅` is `0`. -/
def Theorem2_1_lower : Prop :=
  ∀ (X : Type u) [MetricSpace X] [CompleteSpace X] (x : ℕ → X) (T : X → X),
    DenseRange x → Continuous T → ∀ Z : Set X,
      bowenEntropy T Z = ⨅ A : Set ℕ, ⨆ y ∈ Z, lowerOrbitComplexity x T A y ∧
        ∃ B : Set ℕ, ∀ A : Set ℕ, charOracle B ≤ᵀ charOracle A →
          bowenEntropy T Z = ⨆ y ∈ Z, lowerOrbitComplexity x T A y

/-- [N, Theorem 2.1] (from [Din]), packing entropy: for every set `Z`,
`h̄(T, Z) = min_A sup_{y ∈ Z} K̄^A(y, T)`, attained on an upper cone of oracles. Same setting as
`Theorem2_1_lower`. -/
def Theorem2_1_upper : Prop :=
  ∀ (X : Type u) [MetricSpace X] [CompleteSpace X] (x : ℕ → X) (T : X → X),
    DenseRange x → Continuous T → ∀ Z : Set X,
      packingEntropy T Z = ⨅ A : Set ℕ, ⨆ y ∈ Z, upperOrbitComplexity x T A y ∧
        ∃ B : Set ℕ, ∀ A : Set ℕ, charOracle B ≤ᵀ charOracle A →
          packingEntropy T Z = ⨆ y ∈ Z, upperOrbitComplexity x T A y

/-! ### The variational principle and Corollary 4.2 -/

/-- The variational principle of Feng and Huang (J. Funct. Anal. 263 (2012), Thms. 1.2–1.3,
used in [N, Cor. 4.2, Cor. 6.5(c)]): on a compact metric space, for continuous `T` and a
nonempty compact `K`, `h̲(T, K) = sup {h̲_μ(T) : μ(K) = 1}` and
`h̄(T, K) = sup {h̄_μ(T) : μ(K) = 1}`, over Borel probability measures. -/
def VariationalPrinciple : Prop :=
  ∀ (X : Type u) [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
    (T : X → X) (K : Set X), Continuous T → IsCompact K → K.Nonempty →
      bowenEntropy T K =
          ⨆ (μ : Measure X) (_ : IsProbabilityMeasure μ) (_ : μ K = 1), lowerMeasureEntropy μ T ∧
        packingEntropy T K =
          ⨆ (μ : Measure X) (_ : IsProbabilityMeasure μ) (_ : μ K = 1), upperMeasureEntropy μ T

/-- The hard half of the packing variational principle, Feng–Huang's Theorem 1.3 in its own
form: `h^P_top(T, K) ≤ sup {h̄_μ(T) : μ(K) = 1}`. It is the inequality `≤` of the second half of
`VariationalPrinciple`; it is stated separately because the library proves it separately, for
its packing pressure. -/
def PackingVariationalInequality : Prop :=
  ∀ (X : Type u) [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
    (T : X → X) (K : Set X), Continuous T → IsCompact K → K.Nonempty →
      packingEntropy T K ≤
        ⨆ (μ : Measure X) (_ : IsProbabilityMeasure μ) (_ : μ K = 1), upperMeasureEntropy μ T

/-- [N, Corollary 4.2] (variational form): let `X` be a compact metric space with ideal points
`(xᵢ)`, `T` continuous and `K ⊆ X` nonempty and compact. Then
`min_A sup_{y ∈ K} K̲^A(y, T) = sup_{μ(K) = 1} ∫ K̲^{A_μ}(y, T) dμ(y)`, where `A_μ` is any
oracle admissible for `(X, d, T, μ)`, and the same with `K̄`. "Any" is a choice function
`μ ↦ A_μ` with the admissibility hypothesis for every Borel probability measure (such a choice
exists when the ideal points are dense, which is part of admissibility, so no separate density
hypothesis is needed); the minimum is written as an infimum (it is attained, by `Theorem2_1_lower`,
`Theorem2_1_upper`). -/
def Corollary4_2 : Prop :=
  ∀ (X : Type u) [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
    (x : ℕ → X) (T : X → X) (K : Set X) (Aμ : Measure X → Set ℕ),
    Continuous T → IsCompact K → K.Nonempty →
    (∀ μ : Measure X, IsProbabilityMeasure μ → IsAdmissible x T μ (Aμ μ)) →
      ⨅ A : Set ℕ, ⨆ y ∈ K, lowerOrbitComplexity x T A y =
          ⨆ (μ : Measure X) (_ : IsProbabilityMeasure μ) (_ : μ K = 1),
            ∫⁻ y, lowerOrbitComplexity x T (Aμ μ) y ∂μ ∧
        ⨅ A : Set ℕ, ⨆ y ∈ K, upperOrbitComplexity x T A y =
          ⨆ (μ : Measure X) (_ : IsProbabilityMeasure μ) (_ : μ K = 1),
            ∫⁻ y, upperOrbitComplexity x T (Aμ μ) y ∂μ

/-! ### Theorem 4.3: essential bounds of the local entropies -/

/-- [N, Theorem 4.3(a)]: let `μ` be a Borel probability measure and `A` admissible for
`(X, d, T, μ)`, with `R_A` the `μ`-random points relative to `A`. Then
`ess sup h̲_μ(T, ·) = sup_{y ∈ R_A} K̲^A(y, T) = h̲(T, R_A) = inf {h̲(T, Z) : μ(Z) = 1}`.
Setting as in `Theorem3_3` (`X` complete, `T` continuous); `μ(Z)` is the outer measure. -/
def Theorem4_3_a : Prop :=
  ∀ (X : Type u) [MetricSpace X] [CompleteSpace X] [MeasurableSpace X] [BorelSpace X]
    (x : ℕ → X) (T : X → X) (A : Set ℕ) (μ : Measure X) [IsProbabilityMeasure μ],
    Continuous T → IsAdmissible x T μ A →
      essSup (lowerLocalEntropy μ T) μ = ⨆ y ∈ MLRandom x A μ, lowerOrbitComplexity x T A y ∧
        essSup (lowerLocalEntropy μ T) μ = bowenEntropy T (MLRandom x A μ) ∧
        essSup (lowerLocalEntropy μ T) μ = ⨅ (Z : Set X) (_ : μ Z = 1), bowenEntropy T Z

/-- [N, Theorem 4.3(b)]: for a Borel probability measure `μ`,
`ess sup h̄_μ(T, ·) = min_B sup_{y ∈ R_B} K̄^B(y, T) = inf {h̄(T, Z) : μ(Z) = 1}`, where `B`
ranges over the oracles admissible for `(X, d, T, μ)`, and the minimum is attained on an upper
cone of oracles (all of them admissible). The first conjunct is the inequality
`ess sup ≤ sup_{R_B} K̄^B` for every admissible `B`. `X` is complete with dense ideal points `(xᵢ)`
(as in [N, §2.1]; without them no oracle is admissible), `T` is continuous. -/
def Theorem4_3_b : Prop :=
  ∀ (X : Type u) [MetricSpace X] [CompleteSpace X] [MeasurableSpace X] [BorelSpace X]
    (x : ℕ → X) (T : X → X) (μ : Measure X) [IsProbabilityMeasure μ],
    DenseRange x → Continuous T →
      (∀ B : Set ℕ, IsAdmissible x T μ B →
        essSup (upperLocalEntropy μ T) μ ≤ ⨆ y ∈ MLRandom x B μ, upperOrbitComplexity x T B y) ∧
      essSup (upperLocalEntropy μ T) μ =
        ⨅ (B : Set ℕ) (_ : IsAdmissible x T μ B),
          ⨆ y ∈ MLRandom x B μ, upperOrbitComplexity x T B y ∧
      (∃ C : Set ℕ, ∀ B : Set ℕ, charOracle C ≤ᵀ charOracle B →
        IsAdmissible x T μ B ∧
          ⨆ y ∈ MLRandom x B μ, upperOrbitComplexity x T B y = essSup (upperLocalEntropy μ T) μ) ∧
      essSup (upperLocalEntropy μ T) μ = ⨅ (Z : Set X) (_ : μ Z = 1), packingEntropy T Z

/-- [N, Theorem 4.3(c)]: for a Borel probability measure `μ`,
`ess inf h̲_μ(T, ·) = max_B inf_{y ∈ R_B} K̲^B(y, T) = inf {h̲(T, Z) : μ(Z) > 0}`, and the same
with `h̄_μ`, `K̄^B`, `h̄`; `B` ranges over the admissible oracles and the maximum is attained on an
upper cone of (admissible) oracles. The first conjunct is the inequality `inf_{R_B} ≤ ess inf`
for every admissible `B`. Same setting as `Theorem4_3_b`. -/
def Theorem4_3_c : Prop :=
  ∀ (X : Type u) [MetricSpace X] [CompleteSpace X] [MeasurableSpace X] [BorelSpace X]
    (x : ℕ → X) (T : X → X) (μ : Measure X) [IsProbabilityMeasure μ],
    DenseRange x → Continuous T →
      (∀ B : Set ℕ, IsAdmissible x T μ B →
        ⨅ y ∈ MLRandom x B μ, lowerOrbitComplexity x T B y ≤ essInf (lowerLocalEntropy μ T) μ ∧
          ⨅ y ∈ MLRandom x B μ, upperOrbitComplexity x T B y ≤
            essInf (upperLocalEntropy μ T) μ) ∧
      (∃ C : Set ℕ, ∀ B : Set ℕ, charOracle C ≤ᵀ charOracle B →
        IsAdmissible x T μ B ∧
          ⨅ y ∈ MLRandom x B μ, lowerOrbitComplexity x T B y = essInf (lowerLocalEntropy μ T) μ ∧
          ⨅ y ∈ MLRandom x B μ, upperOrbitComplexity x T B y =
            essInf (upperLocalEntropy μ T) μ) ∧
      (essInf (lowerLocalEntropy μ T) μ =
          ⨆ (B : Set ℕ) (_ : IsAdmissible x T μ B),
            ⨅ y ∈ MLRandom x B μ, lowerOrbitComplexity x T B y ∧
        essInf (upperLocalEntropy μ T) μ =
          ⨆ (B : Set ℕ) (_ : IsAdmissible x T μ B),
            ⨅ y ∈ MLRandom x B μ, upperOrbitComplexity x T B y) ∧
      essInf (lowerLocalEntropy μ T) μ = ⨅ (Z : Set X) (_ : μ Z ≠ 0), bowenEntropy T Z ∧
        essInf (upperLocalEntropy μ T) μ = ⨅ (Z : Set X) (_ : μ Z ≠ 0), packingEntropy T Z

/-! ### Corollary 6.5: statistics of the entropy law -/

/-- [N, Corollary 6.5(a)]: the Feng–Huang entropies are the means of the two marginals of the
entropy law: `h̲_μ(T) = ∫ s dΛ_μ(s, t)` and `h̄_μ(T) = ∫ t dΛ_μ(s, t)`. For every measure `μ`
and continuous `T`. -/
def Corollary6_5_a : Prop :=
  ∀ (X : Type u) [MetricSpace X] [MeasurableSpace X] [BorelSpace X] (T : X → X)
    (μ : Measure X), Continuous T →
      lowerMeasureEntropy μ T = ∫⁻ p, p.1 ∂entropyLaw μ T ∧
        upperMeasureEntropy μ T = ∫⁻ p, p.2 ∂entropyLaw μ T

/-- [N, Corollary 6.5(b)]: the essential suprema and infima of the local entropies (the numbers
of Theorem 4.3) are those of the two coordinates under the entropy law `Λ_μ` (the endpoints of
the supports of its marginals). For every measure `μ` and continuous `T`. -/
def Corollary6_5_b : Prop :=
  ∀ (X : Type u) [MetricSpace X] [MeasurableSpace X] [BorelSpace X] (T : X → X)
    (μ : Measure X), Continuous T →
      essSup (lowerLocalEntropy μ T) μ = essSup Prod.fst (entropyLaw μ T) ∧
        essSup (upperLocalEntropy μ T) μ = essSup Prod.snd (entropyLaw μ T) ∧
        essInf (lowerLocalEntropy μ T) μ = essInf Prod.fst (entropyLaw μ T) ∧
        essInf (upperLocalEntropy μ T) μ = essInf Prod.snd (entropyLaw μ T)

/-- [N, Corollary 6.5(c)]: on a compact metric space, for continuous `T` and a nonempty compact
`K`, `h̲(T, K) = sup_{μ(K)=1} ess inf h̲_μ(T, ·) = sup_{μ(K)=1} h̲_μ(T) = sup_{μ(K)=1} ess sup
h̲_μ(T, ·)`, and the same for `h̄(T, K)` with the upper local entropies (the suprema over Borel
probability measures `μ` with `μ(K) = 1`). The middle equalities are `VariationalPrinciple`. -/
def Corollary6_5_c : Prop :=
  ∀ (X : Type u) [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
    (T : X → X) (K : Set X), Continuous T → IsCompact K → K.Nonempty →
      (bowenEntropy T K = ⨆ (μ : Measure X) (_ : IsProbabilityMeasure μ) (_ : μ K = 1),
          essInf (lowerLocalEntropy μ T) μ ∧
        bowenEntropy T K = ⨆ (μ : Measure X) (_ : IsProbabilityMeasure μ) (_ : μ K = 1),
          lowerMeasureEntropy μ T ∧
        bowenEntropy T K = ⨆ (μ : Measure X) (_ : IsProbabilityMeasure μ) (_ : μ K = 1),
          essSup (lowerLocalEntropy μ T) μ) ∧
      (packingEntropy T K = ⨆ (μ : Measure X) (_ : IsProbabilityMeasure μ) (_ : μ K = 1),
          essInf (upperLocalEntropy μ T) μ ∧
        packingEntropy T K = ⨆ (μ : Measure X) (_ : IsProbabilityMeasure μ) (_ : μ K = 1),
          upperMeasureEntropy μ T ∧
        packingEntropy T K = ⨆ (μ : Measure X) (_ : IsProbabilityMeasure μ) (_ : μ K = 1),
          essSup (upperLocalEntropy μ T) μ)

end Kolmogorov.Trusted
