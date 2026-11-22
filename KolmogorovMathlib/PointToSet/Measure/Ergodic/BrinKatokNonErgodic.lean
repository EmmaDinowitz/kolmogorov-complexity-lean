/-
Copyright (c) 2026 Emma Dinowitz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emma Dinowitz
-/
import KolmogorovMathlib.PointToSet.Measure.Ergodic.ErgodicDecompositionEntropy
import KolmogorovMathlib.Ergodic.ErgodicDecomposition

/-!
# The Brin–Katok formula for invariant measures

For a continuous map of a compact metric space and an invariant Borel probability measure `μ`, the
lower and upper local entropies agree almost everywhere, and equal the Kolmogorov–Sinai entropy of
the ergodic component (Brin–Katok). Proof: the ergodic decomposition
(`exists_ergodicDecomposition`, `Q = μ`) and Theorem 7.5(b)
(`ae_compProd_localEntropy_eq_ksEntropy_of_ergodicDecomposition`); the `x`-marginal of `μ ⊗ κ` is
`μ.bind κ = μ` (`Measure.snd_compProd`), and the set where the two local entropies agree is
measurable (`measurable_localEntropy`), so the statement passes from `μ ⊗ κ` to `μ`.

Blueprint node `erg:decomposition-entropy`.
-/

namespace Kolmogorov.PointToSet

open Filter Set MeasureTheory ProbabilityTheory
open scoped Topology ENNReal Computability

variable {X : Type*} [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]

/-- Brin–Katok for invariant measures: the lower and upper local entropies agree almost
everywhere. Blueprint node `erg:decomposition-entropy`. -/
theorem ae_localEntropy_fst_eq_snd_of_invariant {T : X → X} (hT : Continuous T)
    (μ : Measure X) [IsProbabilityMeasure μ] (hμ : MeasurePreserving T μ μ) :
    ∀ᵐ x ∂μ, (localEntropy μ T x).1 = (localEntropy μ T x).2 := by
  obtain ⟨κ, hκ, hbind, herg⟩ := Ergodic.exists_ergodicDecomposition hT μ hμ
  have hinv : MeasurePreserving T (μ.bind κ) (μ.bind κ) := by
    rw [hbind]; exact hμ
  have h := ae_compProd_localEntropy_eq_ksEntropy_of_ergodicDecomposition hT μ κ hinv herg
  rw [hbind] at h
  have hP : ∀ᵐ p ∂(μ ⊗ₘ κ), (localEntropy μ T p.2).1 = (localEntropy μ T p.2).2 :=
    h.mono fun p hp ↦ by rw [hp.1]
  have hmeas : MeasurableSet {x | (localEntropy μ T x).1 = (localEntropy μ T x).2} :=
    measurableSet_eq_fun (measurable_localEntropy μ hT).fst (measurable_localEntropy μ hT).snd
  have hsnd : (μ ⊗ₘ κ).snd = μ := by rw [Measure.snd_compProd]; exact hbind
  have hmap := (ae_map_iff measurable_snd.aemeasurable hmeas).2 hP
  rwa [← Measure.snd, hsnd] at hmap

end Kolmogorov.PointToSet
