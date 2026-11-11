/-
Copyright (c) 2026 Emma Dinowitz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emma Dinowitz
-/
import KolmogorovMathlib.PointToSet.ComputableMetric.StaticDimensions
import KolmogorovMathlib.Oracle.PrefixComplexity.Decoders

/-!
# The complexity account of a localization program

A program partial recursive in the oracle `A` that reads two naturals and a pair of naturals
and outputs ideal indices within `δ` of a point `z` turns shortest descriptions of its inputs
into a bound on the precision complexity of `z` at radius `δ`:
```
K^A_δ(z) ≤ K^A(i) + K^A(i') + K^A(Tp, Tm) + c,
```
with `c` depending only on the program (`precisionComplexity_le_of_program`, from the decoder
bound `oracleNatComplexity_le_of_decoder`). The two bookkeeping facts it rests on are that
precision complexity is antitone in the radius (`precisionComplexityNat_anti`) and that an ideal
point within `δ` of `z` bounds it by its own complexity (`precisionComplexityNat_le_of_dist_lt`).
Blueprint node `eff:program-account`.
-/

namespace Kolmogorov.PointToSet

open scoped Computability

variable {X : Type*} [MetricSpace X] (P : Presentation X) (A : Set ℕ)

/-- Precision complexity is antitone in the radius (library `staticPointDimensions_antitone`,
natural shadow). Blueprint node `geo:orbit-to-location`. -/
theorem precisionComplexityNat_anti {x : X} {δ δ' : ℝ} (h0 : 0 < δ) (h : δ ≤ δ') :
    precisionComplexityNat P A x δ' ≤ precisionComplexityNat P A x δ := by
  obtain ⟨i, -, hi⟩ := staticPointDimensions_attained P A x δ h0
  unfold precisionComplexityNat
  exact ENat.toNat_le_toNat (staticPointDimensions_antitone P A x h)
    (by rw [hi]; exact ENat.natCast_ne_top _)

/-- An ideal point within `δ` of `z` bounds the precision complexity at radius `δ` by its own
complexity. Blueprint node `geo:orbit-to-location`. -/
theorem precisionComplexityNat_le_of_dist_lt {z : X} {δ : ℝ} {q : ℕ} (hq : dist (P.ι q) z < δ) :
    precisionComplexityNat P A z δ ≤ oracleNatComplexity A q := by
  have h : precisionComplexity P A z δ ≤ (oracleNatComplexity A q : ENat) := iInf₂_le q hq
  unfold precisionComplexityNat
  simpa using ENat.toNat_le_toNat h (ENat.natCast_ne_top _)

/-- The complexity account of a program: if `F` is partial recursive in `A`, there is a
constant `c` such that whenever `F` halts on `(i, i', Tp, Tm)` with every output within `δ` of
`z`, the precision complexity of `z` at radius `δ` is at most
`K^A(i) + K^A(i') + K^A(Tp, Tm) + c`. Blueprint node `eff:program-account`. -/
theorem precisionComplexity_le_of_program (F : ℕ × ℕ × ℕ × ℕ →. ℕ)
    (hF : PartrecIn {charOracle A} F) :
    ∃ c : ℕ, ∀ (z : X) (δ : ℝ) (i i' Tp Tm : ℕ), (F (i, i', Tp, Tm)).Dom →
      (∀ q ∈ F (i, i', Tp, Tm), dist (P.ι q) z < δ) →
      precisionComplexityNat P A z δ ≤
        oracleNatComplexity A i + oracleNatComplexity A i' + oraclePairComplexity A Tp Tm + c := by
  obtain ⟨c, hc⟩ := oracleNatComplexity_le_of_decoder A F hF
  refine ⟨c, fun z δ i i' Tp Tm hdom hout ↦ ?_⟩
  have hq := Part.get_mem hdom
  exact (precisionComplexityNat_le_of_dist_lt P A (hout _ hq)).trans (hc i i' Tp Tm _ hq)

end Kolmogorov.PointToSet
