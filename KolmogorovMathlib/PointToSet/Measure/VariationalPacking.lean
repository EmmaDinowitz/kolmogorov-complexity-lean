/-
Copyright (c) 2026 Emma Dinowitz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emma Dinowitz
-/
import KolmogorovMathlib.PointToSet.Measure.Variational
import KolmogorovMathlib.PointToSet.PackingEquivalences.Pressure.Equivalence

/-!
# The Feng–Huang variational inequality in packing form

`upperEntropy_le_iSup_measureEntropy` bounds the chapter's upper entropy `upperEntropy P T K` (the
modified upper capacity entropy) of a compact set by the supremum of the upper Feng–Huang
entropies of the probability measures carried by `K`. The library identifies this upper entropy
with the zero-potential packing pressure (`entropy_eq_zeroPotentialPressure_of_nonempty_upper`
and `pressureEquivalence_upper`), so the same bound holds for the packing topological entropy
`h^P_top(T, K)` in the sense of Feng–Huang, which is the form of their Theorem 1.3.

* `packingPressure_zero_le_iSup_measureEntropy`: `h^P_top(T, K) ≤ sup_{μ(K)=1} h̄_μ(T)`.

The presentation `P` is used only to reach the chapter's `upperEntropy`; the statement does not
depend on it. Blueprint node `meas:variational`.
-/

namespace Kolmogorov.PointToSet

open MeasureTheory
open scoped ENNReal

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

/-- The Feng–Huang variational inequality for the packing topological entropy (zero-potential
packing pressure) of a nonempty compact set: it is at most the supremum of the upper
Feng–Huang entropies `h̄_μ(T)` of the probability measures with `μ K = 1`. From
`upperEntropy_le_iSup_measureEntropy` and the library's packing equivalence
`pressureEquivalence_upper`. Blueprint node `meas:variational`. -/
theorem packingPressure_zero_le_iSup_measureEntropy [CompactSpace X] (P : Presentation X)
    {T : X → X} (hT : Continuous T) {K : Set X} (hK : IsCompact K) (hne : K.Nonempty) :
    packingPressure T (fun _ ↦ 0) K ≤
      (((⨆ (μ : Measure X) (_ : IsProbabilityMeasure μ) (_ : μ K = 1),
        (measureEntropy μ T).2 : ℝ≥0∞)) : EReal) := by
  rw [pressureEquivalence_upper T hT _ uniformContinuous_const K,
    ← entropy_eq_zeroPotentialPressure_of_nonempty_upper P T hT K hne]
  exact EReal.coe_ennreal_le_coe_ennreal_iff.2 (upperEntropy_le_iSup_measureEntropy P hT hK hne)

end Kolmogorov.PointToSet
