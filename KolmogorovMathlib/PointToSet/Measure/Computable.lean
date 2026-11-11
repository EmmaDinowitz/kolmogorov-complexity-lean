/-
Copyright (c) 2026 Emma Dinowitz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emma Dinowitz
-/
import KolmogorovMathlib.PointToSet.Measure.BowenCeOpen
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite

/-!
# Measures computable relative to an oracle

Following Hoyrup and Rojas, a finite Borel measure `μ` on a presented metric space is
`A`-computable when the measures of finite unions of basic balls are lower semicomputable in
`A`, uniformly in the list of balls (`IsComputableMeasureIn`). Every finite measure is
`A`-computable for all `A` in an upper cone. An oracle is admissible for `(X, d, T, μ)` when it
computes the metric table, represents `T` and computes `μ` (`IsMeasureAdmissible`).
(E. Dinowitz, *Entropy of non-invariant measures and orbit complexity of random points*, §2.2.)

The two consequences used throughout are:

* (M1) `IsComputableMeasureIn.lowerSemicomputable_ceOpen`: `μ(U)` is lower semicomputable in
  `A`, uniformly, for an `A`-c.e. open family `U`; for a probability measure the measure of
  the complement is upper semicomputable (`IsComputableMeasureIn.isREIn_measure_compl_lt`).
* (M2) `IsMeasureAdmissible.lowerSemicomputable_bowenBall` and
  `IsMeasureAdmissible.isREIn_measure_closedBowenBall_lt`: the measures of Bowen balls about
  ideal points are lower semicomputable and those of closed Bowen balls upper semicomputable,
  uniformly in the order, the centre and the rational radius.

Blueprint nodes `meas:computable`, `meas:admissible`.
-/

namespace Kolmogorov.PointToSet

open Filter Set MeasureTheory
open scoped Topology ENNReal Computability

variable {X : Type*} [MetricSpace X] [MeasurableSpace X]

/-- A finite Borel measure is computable relative to `A` when the measures of the finite
unions of basic balls are lower semicomputable in `A`, uniformly in the list of balls.
Blueprint node `meas:computable`. -/
def IsComputableMeasureIn (P : Presentation X) (A : Set ℕ) (μ : Measure X) : Prop :=
  IsLowerSemicomputableIn A fun L : List (ℕ × ℚ) ↦ (μ (ballUnion P L)).toReal

/-- Computability of a measure transfers to every Turing-stronger oracle. -/
theorem IsComputableMeasureIn.mono_oracle {P : Presentation X} {A B : Set ℕ} {μ : Measure X}
    (hμ : IsComputableMeasureIn P A μ) (hAB : charOracle A ≤ᵀ charOracle B) :
    IsComputableMeasureIn P B μ := by
  exact IsREIn.mono_oracle hμ hAB

/-- Every measure is computable relative to all oracles of an upper cone.
Blueprint node `meas:computable`. -/
theorem exists_oracle_isComputableMeasureIn (P : Presentation X) (μ : Measure X) :
    ∃ C : Set ℕ, ∀ A : Set ℕ, charOracle C ≤ᵀ charOracle A → IsComputableMeasureIn P A μ := by
  exact exists_oracle_isREIn _

/-- (M1): the measure of an `A`-c.e. open set is lower semicomputable in `A`, uniformly in
the index of a c.e. open family. Blueprint node `meas:computable`. -/
theorem IsComputableMeasureIn.lowerSemicomputable_ceOpen [BorelSpace X] {P : Presentation X}
    {A : Set ℕ} {μ : Measure X} [IsFiniteMeasure μ] (hμ : IsComputableMeasureIn P A μ)
    {ι : Type*} [Primcodable ι] {U : ι → Set X} (hU : IsCeOpenFamilyIn P A U) :
    IsLowerSemicomputableIn A fun i : ι ↦ (μ (U i)).toReal := by
  obtain ⟨E, hE, hUE⟩ := hU
  obtain ⟨L, hL, hsound, hmono, hexh, -⟩ := hE.exists_prefixList
  -- `U i` is the increasing union of the finite unions of balls listed at the stages
  have hUnion : ∀ i, U i = ⋃ t, ballUnion P (L (i, t)) := by
    intro i
    rw [hUE i]
    ext y
    simp only [ballUnion, mem_iUnion, exists_prop]
    constructor
    · rintro ⟨b, hb, hy⟩
      obtain ⟨t, ht⟩ := hexh i b hb
      exact ⟨t, b, ht, hy⟩
    · rintro ⟨t, b, hb, hy⟩
      exact ⟨b, hsound i t b hb, hy⟩
  have hmonoU : ∀ i, Monotone fun t ↦ ballUnion P (L (i, t)) := by
    intro i t t' htt' y hy
    simp only [ballUnion, mem_iUnion, exists_prop] at hy ⊢
    obtain ⟨b, hb, hy⟩ := hy
    exact ⟨b, hmono i t t' htt' b hb, hy⟩
  have hiff : ∀ w : ι × ℚ, ((w.2 : ℝ) < (μ (U w.1)).toReal) ↔
      ∃ t, (w.2 : ℝ) < (μ (ballUnion P (L (w.1, t)))).toReal := by
    rintro ⟨i, q⟩
    constructor
    · intro h
      rcases lt_or_ge (q : ℝ) 0 with hq | hq
      · exact ⟨0, hq.trans_le ENNReal.toReal_nonneg⟩
      · have h' : ENNReal.ofReal q < μ (U i) :=
          (ENNReal.ofReal_lt_iff_lt_toReal hq (measure_ne_top μ _)).mpr h
        rw [hUnion i, (hmonoU i).measure_iUnion] at h'
        obtain ⟨t, ht⟩ := lt_iSup_iff.mp h'
        exact ⟨t, (ENNReal.ofReal_lt_iff_lt_toReal hq (measure_ne_top μ _)).mp ht⟩
    · rintro ⟨t, ht⟩
      refine ht.trans_le (ENNReal.toReal_mono (measure_ne_top μ _) (measure_mono ?_))
      rw [hUnion i]
      exact subset_iUnion (fun t ↦ ballUnion P (L (i, t))) t
  have hre : IsREIn A fun w : ι × ℚ ↦
      ∃ t, (w.2 : ℝ) < (μ (ballUnion P (L (w.1, t)))).toReal := by
    have hmap : ComputableIn {charOracle A} fun v : (ι × ℚ) × ℕ ↦ (L (v.1.1, v.2), v.1.2) :=
      (hL.comp ((ComputableIn.fst.comp ComputableIn.fst).pair ComputableIn.snd)).pair
        (ComputableIn.snd.comp ComputableIn.fst)
    exact (IsREIn.comp hμ hmap).exists
  have heq : (fun w : ι × ℚ ↦ (w.2 : ℝ) < (μ (U w.1)).toReal) = fun w : ι × ℚ ↦
      ∃ t, (w.2 : ℝ) < (μ (ballUnion P (L (w.1, t)))).toReal :=
    funext fun w ↦ propext (hiff w)
  change IsREIn A fun w : ι × ℚ ↦ (w.2 : ℝ) < (μ (U w.1)).toReal
  rw [heq]
  exact hre

/-- (M1), closed sets: for a probability measure the measure of the complement of an
`A`-c.e. open set is upper semicomputable in `A`, uniformly in the index.
Blueprint node `meas:computable`. -/
theorem IsComputableMeasureIn.isREIn_measure_compl_lt [BorelSpace X] {P : Presentation X}
    {A : Set ℕ} {μ : Measure X} [IsProbabilityMeasure μ] (hμ : IsComputableMeasureIn P A μ)
    {ι : Type*} [Primcodable ι] {U : ι → Set X} (hU : IsCeOpenFamilyIn P A U) :
    IsREIn A fun d : ι × ℚ ↦ (μ (U d.1)ᶜ).toReal < (d.2 : ℝ) := by
  have hlow := hμ.lowerSemicomputable_ceOpen hU
  have hmap : Computable fun d : ι × ℚ ↦ (d.1, 1 - d.2) :=
    Computable.fst.pair (computable₂_ratSub.comp (Computable.const 1) Computable.snd)
  have hre := IsREIn.comp hlow hmap.computableIn
  have hmeas : ∀ i, MeasurableSet (U i) := by
    obtain ⟨E, -, hUE⟩ := hU
    intro i
    rw [hUE i]
    exact (isOpen_biUnion fun b _ ↦ Metric.isOpen_ball).measurableSet
  have heq : (fun d : ι × ℚ ↦ (μ (U d.1)ᶜ).toReal < (d.2 : ℝ)) = fun d : ι × ℚ ↦
      (((1 - d.2 : ℚ)) : ℝ) < (μ (U d.1)).toReal := by
    funext d
    refine propext ?_
    rw [prob_compl_eq_one_sub (hmeas d.1), ENNReal.toReal_sub_of_le prob_le_one ENNReal.one_ne_top,
      ENNReal.toReal_one]
    push_cast
    constructor <;> intro h <;> linarith
  rw [heq]
  exact hre

/-- An oracle is admissible for `(X, d, T, μ)` when it computes the metric table of the
presentation, represents the dynamics and computes the measure.
Blueprint node `meas:admissible`. -/
def IsMeasureAdmissible (P : Presentation X) (T : X → X) (μ : Measure X) (A : Set ℕ) : Prop :=
  ComputablePresentationIn P A ∧ IsRepresentedMapIn P P A T ∧ IsComputableMeasureIn P A μ

/-- Admissibility for `(X, d, T, μ)` transfers to every Turing-stronger oracle. -/
theorem IsMeasureAdmissible.mono_oracle {P : Presentation X} {T : X → X} {μ : Measure X}
    {A B : Set ℕ} (hA : IsMeasureAdmissible P T μ A) (hAB : charOracle A ≤ᵀ charOracle B) :
    IsMeasureAdmissible P T μ B := by
  obtain ⟨R, hR, hs, hc⟩ := hA.2.1
  exact ⟨isComputableRealFamilyIn_mono_oracle hA.1 hAB,
    ⟨R, hR.mono_oracle hAB, hs, hc⟩, hA.2.2.mono_oracle hAB⟩

/-- The oracles admissible for `(X, d, T, μ)` contain an upper cone.
Blueprint node `meas:admissible`. -/
theorem exists_measureAdmissible_base (P : Presentation X) (T : X → X) (hT : Continuous T)
    (μ : Measure X) :
    ∃ C : Set ℕ, ∀ A : Set ℕ, charOracle C ≤ᵀ charOracle A → IsMeasureAdmissible P T μ A := by
  obtain ⟨C₁, hC₁⟩ := exists_admissible_base P T hT (fun j : Fin 0 ↦ j.elim0)
    (fun j ↦ j.elim0)
  obtain ⟨C₂, hC₂⟩ := exists_oracle_isComputableMeasureIn P μ
  refine ⟨oracleJoin C₁ C₂, fun A hA ↦ ?_⟩
  have h₁ := hC₁ A ((oracle_joins C₁ C₂).trans hA)
  exact ⟨h₁.1, h₁.2.1, hC₂ A ((oracle_joins_right C₁ C₂).trans hA)⟩

/-- (M2) for the measure: the measures of the Bowen balls about ideal points with rational
radii are lower semicomputable in an admissible oracle, uniformly.
Blueprint node `meas:admissible`. -/
theorem IsMeasureAdmissible.lowerSemicomputable_bowenBall [BorelSpace X] {P : Presentation X}
    {T : X → X} {μ : Measure X} [IsFiniteMeasure μ] {A : Set ℕ}
    (hA : IsMeasureAdmissible P T μ A) :
    IsLowerSemicomputableIn A fun d : ℕ × ℕ × ℚ ↦
      (μ (bowenBall T d.1 (P.ι d.2.1) (d.2.2 : ℝ))).toReal := by
  exact hA.2.2.lowerSemicomputable_ceOpen (isCeOpenFamilyIn_bowenBall P T A hA.1 hA.2.1)

/-- (M2) for the measure, closed balls: for a probability measure the measures of the closed
Bowen balls about ideal points with rational radii are upper semicomputable in an admissible
oracle, uniformly. Blueprint node `meas:admissible`. -/
theorem IsMeasureAdmissible.isREIn_measure_closedBowenBall_lt [BorelSpace X]
    {P : Presentation X} {T : X → X} {μ : Measure X} [IsProbabilityMeasure μ] {A : Set ℕ}
    (hA : IsMeasureAdmissible P T μ A) :
    IsREIn A fun d : (ℕ × ℕ × ℚ) × ℚ ↦
      (μ (closedBowenBall T d.1.1 (P.ι d.1.2.1) (d.1.2.2 : ℝ))).toReal < (d.2 : ℝ) := by
  have h := (hA.2.2.isREIn_measure_compl_lt
    (isCeOpenFamilyIn_compl_closedBowenBall P T A hA.1 hA.2.1)).comp
    (((Computable.fst : Computable fun d : (ℕ × ℕ × ℚ) × ℚ ↦ d.1).pair
      Computable.snd).computableIn (O := {charOracle A}))
  simpa only [compl_compl] using h

end Kolmogorov.PointToSet
