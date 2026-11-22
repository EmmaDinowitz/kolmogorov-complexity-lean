/-
Copyright (c) 2026 Emma Dinowitz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emma Dinowitz
-/
import KolmogorovMathlib.PointToSet.Measure.Ergodic.OrbitUpper
import KolmogorovMathlib.PointToSet.Measure.Ergodic.OrbitLower

/-!
# Orbit complexity of Martin-Löf random points equals entropy

Theorem 1 of the note *Orbit complexity of Martin-Löf random points equals entropy*
(November 2026): on a compact space with an `A`-computable presentation, for an `A`-represented
continuous map `T` and an `A`-computable `T`-invariant ergodic probability measure `μ`, every
point `x` that is Martin-Löf random for `μ` relative to `A` has
`K̲^A(x, T) = K̄^A(x, T) = h_μ(T)`, the Kolmogorov–Sinai entropy (`ksEntropy`, in bits), including
when `h_μ(T) = ∞`.

* `orbitComplexities_eq_ksEntropy` (Theorem 1), from `upperOrbitComplexity_le_ksEntropy` (a) and
  `ksEntropy_le_lowerOrbitComplexity` (b), and `lowerOrbitComplexity ≤ upperOrbitComplexity`.

Consequences for the chapter on non-invariant measures (*Entropy of non-invariant measures and
orbit complexity of random points*):

* `exists_presentation`: a compact metric space has a presentation (a dense sequence).
* `ae_localEntropy_eq_ksEntropy` (Brin–Katok for ergodic measures): for a continuous `T` on a
  compact metric space and an ergodic invariant probability measure `μ`, the lower and upper local
  entropies equal `h_μ(T)` `μ`-almost everywhere. Proof: an oracle admissible for `μ` exists
  (`exists_measureAdmissible_base`), random points have full measure
  (`measure_compl_randomPoints`), and at random points the local entropies are the orbit
  complexities (Theorem 3.3 of that note, `orbitComplexities_eq_localEntropy`).
* `measureEntropy_eq_ksEntropy`: the Feng–Huang entropies of an ergodic measure are
  `(h_μ(T), h_μ(T))`.
* `ae_localEntropy_eq_measureEntropy_of_ergodic`: the form of Brin–Katok stated in
  `RemarksShift` (`ae_localEntropy_eq_of_ergodic`), without its finiteness hypothesis.

Blueprint node `erg:theorem-one`.
-/

namespace Kolmogorov.PointToSet

open Filter Set MeasureTheory
open scoped Topology ENNReal Computability

variable {X : Type*} [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]

/-- Theorem 1: at every point that is Martin-Löf random for an `A`-computable invariant ergodic
measure relative to `A`, both orbit complexities equal the Kolmogorov–Sinai entropy.
Blueprint node `erg:theorem-one`. -/
theorem orbitComplexities_eq_ksEntropy (P : Presentation X) (T : X → X) (hT : Continuous T)
    (A : Set ℕ) (μ : Measure X) [IsProbabilityMeasure μ] (hA : IsMeasureAdmissible P T μ A)
    (herg : Ergodic T μ) {x : X} (hx : x ∈ randomPoints P A μ) :
    orbitComplexities P T A x = (Ergodic.ksEntropy μ T, Ergodic.ksEntropy μ T) := by
  have hb := ksEntropy_le_lowerOrbitComplexity P T hT A μ hA herg hx
  have ha := upperOrbitComplexity_le_ksEntropy P T hT A μ hA herg hx
  have hle : (orbitComplexities P T A x).1 ≤ (orbitComplexities P T A x).2 := by
    rw [orbitComplexities_eq_localEntropy P T hT A μ hA hx]
    exact localEntropy_fst_le_snd μ T x
  exact Prod.ext (le_antisymm (hle.trans ha) hb) (le_antisymm ha (hb.trans hle))

omit [MeasurableSpace X] [BorelSpace X] in
/-- A nonempty compact metric space has a presentation. Blueprint node `erg:theorem-one`. -/
theorem exists_presentation [Nonempty X] : Nonempty (Presentation X) :=
  ⟨⟨TopologicalSpace.denseSeq X, TopologicalSpace.denseRange_denseSeq X, inferInstance⟩⟩

/-- Brin–Katok for ergodic measures: the lower and upper local entropies of an ergodic invariant
probability measure of a continuous map of a compact metric space equal `h_μ(T)` almost
everywhere. Blueprint node `erg:theorem-one`. -/
theorem ae_localEntropy_eq_ksEntropy {T : X → X} (hT : Continuous T) (μ : Measure X)
    [IsProbabilityMeasure μ] (herg : Ergodic T μ) :
    ∀ᵐ x ∂μ, localEntropy μ T x = (Ergodic.ksEntropy μ T, Ergodic.ksEntropy μ T) := by
  have : Nonempty X := nonempty_of_isProbabilityMeasure μ
  obtain ⟨P⟩ := exists_presentation (X := X)
  obtain ⟨C, hC⟩ := exists_measureAdmissible_base P T hT μ
  have hA := hC C (TuringReducible.refl _)
  have hrand : ∀ᵐ x ∂μ, x ∈ randomPoints P C μ := measure_compl_randomPoints P C μ
  filter_upwards [hrand] with x hx
  rw [← orbitComplexities_eq_localEntropy P T hT C μ hA hx]
  exact orbitComplexities_eq_ksEntropy P T hT C μ hA herg hx

/-- The Feng–Huang entropies of an ergodic invariant measure both equal the Kolmogorov–Sinai
entropy. Blueprint node `erg:theorem-one`. -/
theorem measureEntropy_eq_ksEntropy {T : X → X} (hT : Continuous T) (μ : Measure X)
    [IsProbabilityMeasure μ] (herg : Ergodic T μ) :
    measureEntropy μ T = (Ergodic.ksEntropy μ T, Ergodic.ksEntropy μ T) := by
  have h := ae_localEntropy_eq_ksEntropy hT μ herg
  have h₁ : ∀ᵐ x ∂μ, (localEntropy μ T x).1 = Ergodic.ksEntropy μ T :=
    h.mono fun x hx ↦ by rw [hx]
  have h₂ : ∀ᵐ x ∂μ, (localEntropy μ T x).2 = Ergodic.ksEntropy μ T :=
    h.mono fun x hx ↦ by rw [hx]
  simp only [measureEntropy, lintegral_congr_ae h₁, lintegral_congr_ae h₂, lintegral_const,
    measure_univ, mul_one]

/-- Remark 6.7, the Brin–Katok formula for an ergodic measure, in the form stated in
`RemarksShift` (`ae_localEntropy_eq_of_ergodic`): the local entropy of an ergodic invariant
probability measure of a continuous map of a compact metric space is almost everywhere the
constant `(h, h)`, where `h` is the lower Feng–Huang entropy. No finiteness hypothesis is needed:
both sides equal `h_μ(T)` (`ae_localEntropy_eq_ksEntropy`, `measureEntropy_eq_ksEntropy`).
Blueprint node `meas:remarks`. -/
theorem ae_localEntropy_eq_measureEntropy_of_ergodic {T : X → X} (hT : Continuous T)
    (μ : Measure X) [IsProbabilityMeasure μ] (hμ : Ergodic T μ) :
    ∀ᵐ x ∂μ, localEntropy μ T x = ((measureEntropy μ T).1, (measureEntropy μ T).1) := by
  rw [measureEntropy_eq_ksEntropy hT μ hμ]
  exact ae_localEntropy_eq_ksEntropy hT μ hμ

end Kolmogorov.PointToSet
