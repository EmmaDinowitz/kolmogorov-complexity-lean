/-
Copyright (c) 2026 Emma Dinowitz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emma Dinowitz
-/
import KolmogorovMathlib.PointToSet.Measure.Ergodic.ShiftTransport
import KolmogorovMathlib.PointToSet.Measure.Ergodic.ShiftTranslation
import KolmogorovMathlib.PointToSet.Measure.Ergodic.ShiftRandomness
import KolmogorovMathlib.PointToSet.Measure.Ergodic.BlockCoding
import KolmogorovMathlib.PointToSet.Measure.Ergodic.SymbolicLowerBound
import KolmogorovMathlib.PointToSet.Measure.EntropyLaw

/-!
# Proposition 7.10: orbit complexity at generic and random points of a shift

Proposition 7.10 of *Entropy of non-invariant measures and orbit complexity of random points*, on a
one-sided shift over a finite alphabet with a first-difference metric and a presentation whose ideal
points have computable symbols:

* `upperOrbitComplexity_le_shiftEntropy` (7.10(i)): at a generic point of a shift-invariant `ν`,
  `K̄^A(x, σ) ≤ h_ν(σ)` for every oracle `A` computing the symbols.
* `orbitComplexities_eq_shiftEntropy` (7.10(ii)): if `ν` is ergodic and `x` is `ν`-random relative
  to an oracle `B` admissible for `ν`, then `K̲^A(x, σ) = K̄^A(x, σ) = h_ν(σ)` for `A ≤_T B`.

Both were tracked `sorry`s in `ShiftGeneric.lean` (block coding not written; V'yugin's and Hoyrup's
theorems as external input). They are proved here from `BlockCoding` and Hoyrup's theorem
(`SymbolicLowerBound`, `Hoyrup*`), with the transport to `Fin |α|` of `ShiftTransport`, the
word/ideal-point translation of `ShiftTranslation`, and `ShiftRandomness`.

Blueprint node `erg:prop710`.
-/

namespace Kolmogorov.PointToSet

open Filter Set MeasureTheory
open scoped Topology ENNReal Computability

variable {α : Type*} [Fintype α] [MetricSpace (ℕ → α)] [MeasurableSpace (ℕ → α)]
  [Primcodable α] {β : ℝ}

omit [Fintype α] [MetricSpace (ℕ → α)] [MeasurableSpace (ℕ → α)] [Primcodable α] in
/-- If `a n ≤ b n + c` for all `n`, the normalized `limsup` and `liminf` of `a` are at most those
of `b`. Blueprint node `erg:prop710`. -/
private theorem limsup_liminf_div_le_of_le_add {a b : ℕ → ℕ} (c : ℕ) (h : ∀ n, a n ≤ b n + c) :
    limsup (fun n : ℕ ↦ (a n : ℝ≥0∞) / n) atTop ≤ limsup (fun n : ℕ ↦ (b n : ℝ≥0∞) / n) atTop ∧
      liminf (fun n : ℕ ↦ (a n : ℝ≥0∞) / n) atTop ≤
        liminf (fun n : ℕ ↦ (b n : ℝ≥0∞) / n) atTop := by
  have hlim : Tendsto (fun n : ℕ ↦ (c : ℝ≥0∞) / n) atTop (𝓝 0) := by
    have := ENNReal.Tendsto.const_mul ENNReal.tendsto_inv_nat_nhds_zero
      (Or.inr (ENNReal.natCast_ne_top c))
    simpa [div_eq_mul_inv] using this
  have hle : ∀ n : ℕ, (a n : ℝ≥0∞) / n ≤
      ((fun n : ℕ ↦ (b n : ℝ≥0∞) / n) + fun n : ℕ ↦ (c : ℝ≥0∞) / n) n := fun n ↦ by
    simp only [Pi.add_apply]
    rw [← ENNReal.add_div]
    gcongr
    exact_mod_cast h n
  refine ⟨?_, ?_⟩
  · exact (limsup_le_limsup (.of_forall hle)).trans_eq
      (ENNReal.limsup_add_of_right_tendsto_zero hlim _)
  · exact (liminf_le_liminf (.of_forall hle)).trans_eq
      (ENNReal.liminf_add_of_right_tendsto_zero hlim _)

omit [Fintype α] [MetricSpace (ℕ → α)] [MeasurableSpace (ℕ → α)] [Primcodable α] in
/-- The lower orbit complexity is at most the upper one. Blueprint node `erg:prop710`. -/
private theorem orbitComplexities_fst_le_snd' {X : Type*} [MetricSpace X] (P : Presentation X)
    (T : X → X) (A : Set ℕ) (x : X) :
    (orbitComplexities P T A x).1 ≤ (orbitComplexities P T A x).2 :=
  iSup_mono fun _ ↦ liminf_le_limsup (by isBoundedDefault) (by isBoundedDefault)

/-- Proposition 7.10(i): if `x` is generic for a shift-invariant probability measure `ν`, then
the upper orbit complexity satisfies `K̄^A(x, σ) ≤ h_ν(σ)`.

Added hypothesis: the symbols of the ideal points of the presentation are computable relative
to `A` (`(i, j) ↦ (P.ι i) j`). The paper leaves the presentation of the shift implicit (the
standard computable one); without such a hypothesis the statement fails, since a presentation
whose ideal points are relabelled by a noncomputable isometry can make every prefix expensive.
Proof: the upper translation `orbitComplexities_snd_le_limsup_wordComplexity`, then block coding
(`limsup_wordComplexity_le_shiftEntropy`) after recoding into `Fin |α|` (`ShiftTransport`).
Blueprint node `erg:prop710`. -/
theorem upperOrbitComplexity_le_shiftEntropy [BorelSpace (ℕ → α)] (hβ : 0 < β) (hβ₁ : β < 1)
    (hd : ∀ x y : ℕ → α, x ≠ y → dist x y = β ^ PiNat.firstDiff x y)
    (P : Presentation (ℕ → α)) (A : Set ℕ)
    (hP : ComputableIn {charOracle A} fun q : ℕ × ℕ ↦ P.ι q.1 q.2)
    (ν : Measure (ℕ → α)) [IsProbabilityMeasure ν] (hν : MeasurePreserving shiftMap ν ν)
    {x : ℕ → α} (hx : IsGenericPoint ν x) :
    (orbitComplexities P shiftMap A x).2 ≤ shiftEntropy ν := by
  obtain ⟨c, hc⟩ := exists_wordComplexity_finCode_le (α := α) A
  calc (orbitComplexities P shiftMap A x).2
      ≤ limsup (fun n : ℕ ↦ (wordComplexity A x n : ℝ≥0∞) / n) atTop :=
        orbitComplexities_snd_le_limsup_wordComplexity hβ hβ₁ hd P A hP x
    _ ≤ limsup (fun n : ℕ ↦ (wordComplexity A (finCode x) n : ℝ≥0∞) / n) atTop :=
        (limsup_liminf_div_le_of_le_add c fun n ↦ (hc x n).2).1
    _ ≤ shiftEntropy (ν.map finCode) :=
        limsup_wordComplexity_le_shiftEntropy A _ (measurePreserving_map_finCode hβ hβ₁ hd hν)
          (isGenericPoint_map_finCode hβ hβ₁ hd hx)
    _ = shiftEntropy ν := shiftEntropy_map_finCode hβ hβ₁ hd ν

/-- Proposition 7.10(ii) (V'yugin's and Hoyrup's effective ergodic theorem): if `ν` is ergodic
and `x` is `ν`-random relative to an oracle `B` admissible for `ν` (so that `B` computes `ν`),
then both orbit complexities of `x` relative to every `A ≤_T B` equal `h_ν(σ)`.

Added hypothesis, as in `upperOrbitComplexity_le_shiftEntropy`: the symbols of the ideal points
are computable relative to `A`. Proof: `x` is generic (`isGenericPoint_of_mem_randomPoints`), so
(i) gives the upper bound; for the lower bound, `K̲^A(x, σ) ≥ K̲^B(x, σ)`
(`orbitComplexities_mono_oracle`), the lower translation
`liminf_wordComplexity_le_orbitComplexities_fst` for `B`, and Hoyrup's theorem for the finite
alphabet (`shiftEntropy_le_liminf_wordComplexity`) after recoding, since `x` is word-random and `ν`
has computable cylinder measures relative to `B` (`ShiftRandomness`).
Blueprint node `erg:prop710`. -/
theorem orbitComplexities_eq_shiftEntropy [BorelSpace (ℕ → α)] (hβ : 0 < β) (hβ₁ : β < 1)
    (hd : ∀ x y : ℕ → α, x ≠ y → dist x y = β ^ PiNat.firstDiff x y)
    (P : Presentation (ℕ → α)) (ν : Measure (ℕ → α)) [IsProbabilityMeasure ν]
    (hν : Ergodic shiftMap ν) {B : Set ℕ} (hB : IsMeasureAdmissible P shiftMap ν B)
    {x : ℕ → α} (hx : x ∈ randomPoints P B ν) {A : Set ℕ}
    (hAB : charOracle A ≤ᵀ charOracle B)
    (hP : ComputableIn {charOracle A} fun q : ℕ × ℕ ↦ P.ι q.1 q.2) :
    orbitComplexities P shiftMap A x = (shiftEntropy ν, shiftEntropy ν) := by
  have hPB := computableIn_mono_oracle hP hAB
  have hgen := isGenericPoint_of_mem_randomPoints hβ hβ₁ hd P ν hν hB hPB hx
  have hup := upperOrbitComplexity_le_shiftEntropy hβ hβ₁ hd P A hP ν
    hν.toMeasurePreserving hgen
  obtain ⟨c, hc⟩ := exists_wordComplexity_finCode_le (α := α) B
  have hlow : shiftEntropy ν ≤ (orbitComplexities P shiftMap A x).1 :=
    calc shiftEntropy ν = shiftEntropy (ν.map finCode) :=
          (shiftEntropy_map_finCode hβ hβ₁ hd ν).symm
      _ ≤ liminf (fun n : ℕ ↦ (wordComplexity B (finCode x) n : ℝ≥0∞) / n) atTop :=
        shiftEntropy_le_liminf_wordComplexity B _ (ergodic_map_finCode hβ hβ₁ hd hν)
          (isComputableWordMeasureIn_map_finCode hβ hβ₁ hd
            (isComputableWordMeasureIn_of_isComputableMeasureIn hβ hβ₁ hd P B hB.1 hPB ν hB.2.2))
          (finCode_mem_wordRandomPoints hβ hβ₁ hd
            (mem_wordRandomPoints_of_mem_randomPoints hβ hβ₁ hd P B hB.1 hPB ν hx))
      _ ≤ liminf (fun n : ℕ ↦ (wordComplexity B x n : ℝ≥0∞) / n) atTop :=
        (limsup_liminf_div_le_of_le_add c fun n ↦ (hc x n).1).2
      _ ≤ (orbitComplexities P shiftMap B x).1 :=
        liminf_wordComplexity_le_orbitComplexities_fst hβ hβ₁ hd P B hPB x
      _ ≤ (orbitComplexities P shiftMap A x).1 :=
        (orbitComplexities_mono_oracle P shiftMap hAB x).1
  have hle := orbitComplexities_fst_le_snd' P shiftMap A x
  exact Prod.ext (le_antisymm (hle.trans hup) hlow) (le_antisymm hup (hlow.trans hle))

end Kolmogorov.PointToSet
