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
§7.4). For a measure `ν` on the shift we use

`shiftEntropy ν = inf_{k ≥ 1} (1/k) H_ν(ξ^k)`, `H_ν(ξ^k) = -∑_{|w| = k} ν[w] log₂ ν[w]`

(`blockEntropy`), the entropy of the generating partition into cylinders; for an invariant `ν`
this infimum is the limit `lim_k (1/k) H_ν(ξ^k) = h_ν(σ)`.

* `IsGenericPoint ν x`: the frequency in `x` of every word `w` converges to `ν[w]`.
* Proposition 7.10 itself (`upperOrbitComplexity_le_shiftEntropy`,
  `orbitComplexities_eq_shiftEntropy`) is stated and proved in
  `Measure/Ergodic/Proposition710.lean`, from block coding and Hoyrup's theorem, which need the
  word-level material built on this file.
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
generating: for shift-invariant `ν` it equals `Kolmogorov.Ergodic.ksEntropy ν shiftMap`
(`shiftKS_shiftEntropy_eq_ksEntropy`, `Ergodic/ShiftKSEntropy.lean`). Blueprint node
`meas:examples`. -/
noncomputable def shiftEntropy (ν : Measure (ℕ → α)) : ℝ≥0∞ :=
  ⨅ k : ℕ, ⨅ (_ : 1 ≤ k), ENNReal.ofReal (blockEntropy ν k / k)

/-- A point `x` is generic for `ν` when, for every word `w`, the frequency of the occurrences
of `w` in `x` converges to `ν[w]`: `#{j < n | x↾[j, j + k) = w} / n → ν[w]`.
Blueprint node `meas:examples`. -/
def IsGenericPoint (ν : Measure (ℕ → α)) (x : ℕ → α) : Prop :=
  ∀ (k : ℕ) (w : Fin k → α), Tendsto
    (fun n : ℕ ↦ ((({j | j < n ∧ ∀ i : Fin k, x (j + i) = w i} : Set ℕ).ncard : ℝ) / n))
    atTop (𝓝 (ν (wordCylinder w)).toReal)

end generic

end Kolmogorov.PointToSet
