/-
Copyright (c) 2026 Emma Dinowitz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emma Dinowitz
-/
import KolmogorovMathlib.PointToSet.Measure.Shift
import Mathlib.Dynamics.Ergodic.Ergodic

/-!
# Generic points of a shift (Proposition 7.10)

Let `X = ℕ → α` be a one-sided shift on a finite alphabet with a first-difference metric
(E. Dinowitz, *Entropy of non-invariant measures and orbit complexity of random points*,
§7.4). Mathlib has no Kolmogorov–Sinai entropy; for a measure `ν` on the shift we use

`shiftEntropy ν = inf_{k ≥ 1} (1/k) H_ν(ξ^k)`, `H_ν(ξ^k) = -∑_{|w| = k} ν[w] log₂ ν[w]`

(`blockEntropy`), the entropy of the generating partition into cylinders; for an invariant `ν`
this infimum is the limit `lim_k (1/k) H_ν(ξ^k) = h_ν(σ)`.

* `IsGenericPoint ν x`: the frequency in `x` of every word `w` converges to `ν[w]`.
* `upperOrbitComplexity_le_shiftEntropy` (Proposition 7.10(i)): at a generic point of a
  shift-invariant `ν`, `K̄^A(x, σ) ≤ h_ν(σ)` for every oracle `A`. Stated, with the added
  hypothesis that the symbols of the ideal points of the presentation are `A`-computable
  (tracked `sorry`: the block-coding argument is not formalized).
* `orbitComplexities_eq_shiftEntropy` (Proposition 7.10(ii)): if moreover `ν` is ergodic and
  `x` is `ν`-random relative to an oracle `B` admissible for `ν`, then
  `K̲^A(x, σ) = K̄^A(x, σ) = h_ν(σ)` for `A ≤_T B` (tracked `sorry`: V'yugin's and Hoyrup's
  effective ergodic theorem, external input).

Blueprint node `meas:examples`.
-/

namespace Kolmogorov.PointToSet

open Filter Set MeasureTheory
open scoped Topology ENNReal Computability

/-! ### Proposition 7.10: generic points of a shift -/

section generic

variable {α : Type*} [Fintype α] [MetricSpace (ℕ → α)] [MeasurableSpace (ℕ → α)]

/-- The cylinder `[w] = {y | y↾k = w}` of a word `w` of length `k`. -/
def wordCylinder {k : ℕ} (w : Fin k → α) : Set (ℕ → α) :=
  {y | ∀ i : Fin k, y i = w i}

/-- The Shannon entropy in bits `H_ν(ξ^k) = -∑_{|w| = k} ν[w] log₂ ν[w]` of the partition of
`ℕ → α` into the cylinders of length `k`. Blueprint node `meas:examples`. -/
noncomputable def blockEntropy (ν : Measure (ℕ → α)) (k : ℕ) : ℝ :=
  ∑ w : Fin k → α, -(ν (wordCylinder w)).toReal * Real.logb 2 (ν (wordCylinder w)).toReal

/-- The Kolmogorov–Sinai entropy `h_ν(σ)` of a shift-invariant measure, in bits:
`inf_{k ≥ 1} (1/k) H_ν(ξ^k)`, which for an invariant `ν` is the limit `lim_k (1/k) H_ν(ξ^k)`
(subadditivity) and equals the Kolmogorov–Sinai entropy since the cylinder partition is
generating. Mathlib has no Kolmogorov–Sinai entropy; this is the definition used here.
Blueprint node `meas:examples`. -/
noncomputable def shiftEntropy (ν : Measure (ℕ → α)) : ℝ≥0∞ :=
  ⨅ k : ℕ, ⨅ (_ : 1 ≤ k), ENNReal.ofReal (blockEntropy ν k / k)

/-- A point `x` is generic for `ν` when, for every word `w`, the frequency of the occurrences
of `w` in `x` converges to `ν[w]`: `#{j < n | x↾[j, j + k) = w} / n → ν[w]`.
Blueprint node `meas:examples`. -/
def IsGenericPoint (ν : Measure (ℕ → α)) (x : ℕ → α) : Prop :=
  ∀ (k : ℕ) (w : Fin k → α), Tendsto
    (fun n : ℕ ↦ ((({j | j < n ∧ ∀ i : Fin k, x (j + i) = w i} : Set ℕ).ncard : ℝ) / n))
    atTop (𝓝 (ν (wordCylinder w)).toReal)

variable [Primcodable α] {β : ℝ}

/-- Proposition 7.10(i): if `x` is generic for a shift-invariant probability measure `ν`, then
the upper orbit complexity satisfies `K̄^A(x, σ) ≤ h_ν(σ)`.

Added hypothesis: the symbols of the ideal points of the presentation are computable relative
to `A` (`(i, j) ↦ (P.ι i) j`). The paper leaves the presentation of the shift implicit (the
standard computable one); without such a hypothesis the statement fails, since a presentation
whose ideal points are relabelled by a noncomputable isometry can make every prefix expensive.
The paper's proof is a block-coding (method of types) argument.
Blueprint node `meas:examples`. -/
theorem upperOrbitComplexity_le_shiftEntropy [BorelSpace (ℕ → α)] (hβ : 0 < β) (hβ₁ : β < 1)
    (hd : ∀ x y : ℕ → α, x ≠ y → dist x y = β ^ PiNat.firstDiff x y)
    (P : Presentation (ℕ → α)) (A : Set ℕ)
    (hP : ComputableIn {charOracle A} fun q : ℕ × ℕ ↦ P.ι q.1 q.2)
    (ν : Measure (ℕ → α)) [IsProbabilityMeasure ν] (hν : MeasurePreserving shiftMap ν ν)
    {x : ℕ → α} (hx : IsGenericPoint ν x) :
    (orbitComplexities P shiftMap A x).2 ≤ shiftEntropy ν := by
  -- TODO(sorry): not yet proved — block coding: cut `x↾n` into blocks of length `k` at an
  -- offset `r < k` and describe it by `r`, the empirical block distribution, the index in its
  -- type class and `2k` remaining symbols; by concavity of entropy and genericity this costs
  -- `(n/k) H_ν(ξ^k) + o(n)` bits; then `symbolic_orbitComplexity_upper`.
  sorry

/-- Proposition 7.10(ii) (V'yugin's and Hoyrup's effective ergodic theorem): if `ν` is ergodic
and `x` is `ν`-random relative to an oracle `B` admissible for `ν` (so that `B` computes `ν`),
then both orbit complexities of `x` relative to every `A ≤_T B` equal `h_ν(σ)`.

Added hypothesis, as in `upperOrbitComplexity_le_shiftEntropy`: the symbols of the ideal points
are computable relative to `A`. Blueprint node `meas:examples`. -/
theorem orbitComplexities_eq_shiftEntropy [BorelSpace (ℕ → α)] (hβ : 0 < β) (hβ₁ : β < 1)
    (hd : ∀ x y : ℕ → α, x ≠ y → dist x y = β ^ PiNat.firstDiff x y)
    (P : Presentation (ℕ → α)) (ν : Measure (ℕ → α)) [IsProbabilityMeasure ν]
    (hν : Ergodic shiftMap ν) {B : Set ℕ} (hB : IsMeasureAdmissible P shiftMap ν B)
    {x : ℕ → α} (hx : x ∈ randomPoints P B ν) {A : Set ℕ}
    (hAB : charOracle A ≤ᵀ charOracle B)
    (hP : ComputableIn {charOracle A} fun q : ℕ × ℕ ↦ P.ι q.1 q.2) :
    orbitComplexities P shiftMap A x = (shiftEntropy ν, shiftEntropy ν) := by
  -- TODO(sorry): external input — V'yugin's effective ergodic theorem / Hoyrup's theorem,
  -- relativized to `B`: `K^B(x↾n)/n → h_ν(σ)` at every `ν`-random point relative to `B`
  -- (and such a point is generic for `ν`). The rest is formal but not yet written: the lower
  -- bound from `K^A ≥ K^B - O(1)` (`A ≤_T B`) and `symbolic_orbitComplexity_lower`; the upper
  -- bound from `upperOrbitComplexity_le_shiftEntropy` (itself still a `sorry`).
  sorry

end generic

end Kolmogorov.PointToSet
