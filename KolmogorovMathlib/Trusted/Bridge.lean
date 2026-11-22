/-
Copyright (c) 2026 Emma Dinowitz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emma Dinowitz
-/
import KolmogorovMathlib.Trusted.Statements
import KolmogorovMathlib.PointToSet.Measure.Ergodic.OrbitEntropy

/-!
# Bridge: the trusted statements follow from the library

Proofs of the three statements of `KolmogorovMathlib.Trusted.Statements`:

* `theorem3_3_upper : Trusted.Theorem3_3_upper` (from `orbitComplexities_le_localEntropy`),
* `theorem3_3 : Trusted.Theorem3_3` (from `orbitComplexities_eq_localEntropy`),
* `theorem1 : Trusted.Theorem1` (from `orbitComplexities_eq_ksEntropy`),

through equivalences between each plain definition and the library's. A dense sequence `x` in a
complete space gives the library's `Presentation` (`toPresentation`); for a presentation `P`:

* `bowenBall_eq`: `Trusted.bowenBall = PointToSet.bowenBall`;
* `isComputablePresentation_iff`: `↔ ComputablePresentationIn P A`;
* `isCeOpen_iff`, `isCeOpenFamily_iff`: `↔ IsCeOpenIn P A`, `↔ IsCeOpenFamilyIn P A`;
* `isComputableMap_iff`: preimage form `↔ IsRepresentedMapIn P P A T` (sound and complete
  c.e. ball relation); `IsComputableMap.continuous`: an `A`-computable map is continuous;
* `isComputableMeasure_iff`: `↔ IsComputableMeasureIn P A μ`;
* `isAdmissible_iff`: `↔ IsMeasureAdmissible P T μ A`;
* `isMLTest_iff`, `mlRandom_eq`: `↔ IsMeasureTestIn`, `= randomPoints P A μ`;
* `lowerOrbitComplexity_eq`, `upperOrbitComplexity_eq`: `= (orbitComplexities P T A y).1, .2`
  for continuous `T` (the library's finite-scale cost is the normalized orbit complexity only
  when Bowen balls contain ideal points);
* `lowerLocalEntropy_eq`, `upperLocalEntropy_eq`: `= (localEntropy μ T y).1, .2`;
* `info_eq`, `refinementCell_eq`: `= infoBits`, `= Ergodic.refinement` (definitional);
* `isFinitePartition_iff`: `↔ Ergodic.IsMeasurablePartition`;
* `ksEntropy_eq`: `= Ergodic.ksEntropy μ T` for an invariant probability measure (the plain
  definition uses `limsup_n H(ξⁿ)/n`, the library `inf_{n ≥ 1} H(ξⁿ)/n`; Fekete).

The hypotheses are not vacuous: admissible oracles exist (`exists_isAdmissible`) and the random
points have full measure (`measure_compl_mlRandom`).
-/

namespace Kolmogorov.Trusted

open MeasureTheory Filter Set
open scoped ENNReal Computability

universe u

section Metric

variable {X : Type*} [MetricSpace X]

/-- The library's presentation given by a dense sequence of a complete metric space. -/
def toPresentation [CompleteSpace X] (x : ℕ → X) (hx : DenseRange x) :
    PointToSet.Presentation X :=
  ⟨x, hx, inferInstance⟩

/-- The plain Bowen ball is the library's. -/
theorem bowenBall_eq (T : X → X) (n : ℕ) (y : X) (ε : ℝ) :
    bowenBall T n y ε = PointToSet.bowenBall T n y ε := by
  ext z
  exact PointToSet.mem_bowenBall_iff.symm

variable (P : PointToSet.Presentation X) {A : Set ℕ}

/-- A union of rational balls listed by a predicate, written with the library's basic balls. -/
theorem iUnion_ball_eq (F : ℕ × ℚ → Prop) :
    ⋃ (i : ℕ) (q : ℚ) (_ : F (i, q)), Metric.ball (P.ι i) q =
      ⋃ b ∈ {b | F b}, PointToSet.basicBall P b := by
  ext z
  simp [PointToSet.basicBall]

/-- Plain computable presentation is the library's computable metric table. -/
theorem isComputablePresentation_iff :
    IsComputablePresentation P.ι A ↔ PointToSet.ComputablePresentationIn P A := by
  constructor
  · rintro ⟨-, r, hr, h⟩
    exact ⟨r, hr, fun ij p ↦ h ij.1 ij.2 p⟩
  · rintro ⟨r, hr, h⟩
    exact ⟨P.dense, r, hr, fun i j p ↦ h (i, j) p⟩

/-- Plain c.e. open sets are the library's. -/
theorem isCeOpen_iff (U : Set X) : IsCeOpen P.ι A U ↔ PointToSet.IsCeOpenIn P A U := by
  constructor
  · rintro ⟨E, hE, rfl⟩
    exact ⟨E, hE, iUnion_ball_eq P E⟩
  · rintro ⟨E, hE, rfl⟩
    exact ⟨E, hE, (iUnion_ball_eq P E).symm⟩

/-- Plain uniformly c.e. open families are the library's. -/
theorem isCeOpenFamily_iff {κ : Type*} [Primcodable κ] (U : κ → Set X) :
    IsCeOpenFamily P.ι A U ↔ PointToSet.IsCeOpenFamilyIn P A U := by
  constructor
  · rintro ⟨E, hE, h⟩
    exact ⟨E, hE, fun k ↦ (h k).trans (iUnion_ball_eq P fun b ↦ E (k, b))⟩
  · rintro ⟨E, hE, h⟩
    exact ⟨E, hE, fun k ↦ (h k).trans (iUnion_ball_eq P fun b ↦ E (k, b)).symm⟩

/-- A computable map in the preimage form is a represented map in the library's sense (a sound
and complete c.e. relation between positive rational balls), and conversely. -/
theorem isComputableMap_iff (T : X → X) :
    IsComputableMap P.ι A T ↔ PointToSet.IsRepresentedMapIn P P A T := by
  constructor
  · rintro ⟨E, hE, h⟩
    have hmem : ∀ c z, T z ∈ PointToSet.basicBall P c ↔
        ∃ i q, E (c, i, q) ∧ z ∈ Metric.ball (P.ι i) q := by
      intro c z
      change z ∈ T ⁻¹' Metric.ball (P.ι c.1) c.2 ↔ _
      rw [show T ⁻¹' Metric.ball (P.ι c.1) c.2 = _ from h c]
      simp
    refine ⟨fun bc ↦ E (bc.2, bc.1) ∧ 0 < bc.1.2 ∧ 0 < bc.2.2, ?_, ?_, ?_⟩
    · have h1 : PointToSet.IsREIn A fun bc : (ℕ × ℚ) × (ℕ × ℚ) ↦ E (bc.2, bc.1) :=
        hE.comp (Computable.snd.pair Computable.fst).computableIn
      have h2 : PointToSet.IsREIn A fun bc : (ℕ × ℚ) × (ℕ × ℚ) ↦ (0 : ℚ) < bc.1.2 :=
        PointToSet.isREIn_of_computable_decide
          (computable₂_ratLt.comp (Computable.const 0) (Computable.snd.comp Computable.fst))
      have h3 : PointToSet.IsREIn A fun bc : (ℕ × ℚ) × (ℕ × ℚ) ↦ (0 : ℚ) < bc.2.2 :=
        PointToSet.isREIn_of_computable_decide
          (computable₂_ratLt.comp (Computable.const 0) (Computable.snd.comp Computable.snd))
      exact h1.and (h2.and h3)
    · rintro b c ⟨hbc, hb, hc⟩
      refine ⟨hb, hc, ?_⟩
      rintro _ ⟨z, hz, rfl⟩
      exact (hmem c z).2 ⟨b.1, b.2, hbc, hz⟩
    · intro z c hz
      obtain ⟨i, q, hE', hzq⟩ := (hmem c z).1 hz
      have hq : (0 : ℚ) < q := by
        have := dist_nonneg.trans_lt (Metric.mem_ball.1 hzq)
        exact_mod_cast this
      have hc : (0 : ℚ) < c.2 := by
        have := dist_nonneg.trans_lt (Metric.mem_ball.1 hz)
        exact_mod_cast this
      exact ⟨(i, q), ⟨hE', hq, hc⟩, hzq⟩
  · rintro ⟨R, hR, hs, hc⟩
    refine ⟨fun w ↦ R (w.2, w.1), hR.comp (Computable.snd.pair Computable.fst).computableIn,
      fun c ↦ ?_⟩
    ext z
    simp only [mem_preimage, mem_iUnion, exists_prop]
    constructor
    · intro hz
      obtain ⟨b, hb, hzb⟩ := hc z c hz
      exact ⟨b.1, b.2, hb, hzb⟩
    · rintro ⟨i, q, hb, hz⟩
      exact (hs (i, q) c hb).2.2 ⟨z, hz, rfl⟩

/-- An `A`-computable map (for a dense sequence of ideal points) is continuous: the preimages of
the rational balls are open, and these balls form a basis. -/
theorem IsComputableMap.continuous {x : ℕ → X} (hx : DenseRange x) {T : X → X}
    (hT : IsComputableMap x A T) : Continuous T := by
  obtain ⟨E, -, h⟩ := hT
  have hopen : ∀ b : ℕ × ℚ, IsOpen (T ⁻¹' Metric.ball (x b.1) b.2) := fun b ↦ by
    rw [show T ⁻¹' Metric.ball (x b.1) b.2 = _ from h b]
    exact isOpen_iUnion fun _ ↦ isOpen_iUnion fun _ ↦ isOpen_iUnion fun _ ↦ Metric.isOpen_ball
  rw [Metric.continuous_iff']
  intro a ε hε
  obtain ⟨i, hi⟩ := Metric.denseRange_iff.mp hx (T a) (ε / 3) (by positivity)
  obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show ε / 3 < 2 * ε / 3 by linarith)
  have hmem : a ∈ T ⁻¹' Metric.ball (x (i, q).1) (i, q).2 := by
    rw [mem_preimage, Metric.mem_ball]
    exact hi.trans hq1
  filter_upwards [(hopen (i, q)).mem_nhds hmem] with z hz
  have hz' : dist (T z) (x i) < q := hz
  calc dist (T z) (T a) ≤ dist (T z) (x i) + dist (x i) (T a) := dist_triangle _ _ _
    _ < q + ε / 3 := add_lt_add hz' (by rw [dist_comm]; exact hi)
    _ < ε := by linarith

variable [MeasurableSpace X]

/-- Plain computability of a measure is the library's. -/
theorem isComputableMeasure_iff (μ : Measure X) :
    IsComputableMeasure P.ι A μ ↔ PointToSet.IsComputableMeasureIn P A μ :=
  Iff.rfl

/-- Plain admissibility is the library's. -/
theorem isAdmissible_iff (T : X → X) (μ : Measure X) :
    IsAdmissible P.ι T μ A ↔ PointToSet.IsMeasureAdmissible P T μ A := by
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨(isComputablePresentation_iff P).1 h1, (isComputableMap_iff P T).1 h2,
      (isComputableMeasure_iff P μ).1 h3⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨(isComputablePresentation_iff P).2 h1, (isComputableMap_iff P T).2 h2,
      (isComputableMeasure_iff P μ).2 h3⟩

/-- Plain Martin-Löf tests are the library's. -/
theorem isMLTest_iff (μ : Measure X) (U : ℕ → Set X) :
    IsMLTest P.ι A μ U ↔ PointToSet.IsMeasureTestIn P A μ U := by
  rw [IsMLTest, PointToSet.IsMeasureTestIn, isCeOpenFamily_iff]

/-- Plain Martin-Löf random points are the library's. -/
theorem mlRandom_eq (μ : Measure X) : MLRandom P.ι A μ = PointToSet.randomPoints P A μ := by
  ext y
  simp only [MLRandom, PointToSet.randomPoints, mem_ofPred_eq, isMLTest_iff, mem_iInter,
    not_forall]

end Metric

/-! ### Orbit complexities and local entropies -/

section Complexity

variable {X : Type*} [MetricSpace X] (P : PointToSet.Presentation X) (A : Set ℕ)

/-- The plain `K_n^A(y, T, ε)` is the library's `orbitComplexity`. -/
theorem orbitComplexityN_eq (T : X → X) (y : X) (n : ℕ) (ε : ℝ) :
    orbitComplexityN P.ι T A y n ε = PointToSet.orbitComplexity P T A y n ε := by
  simp only [orbitComplexityN, PointToSet.orbitComplexity, bowenBall_eq]

/-- At positive orders and radii the plain rate `K_n^A(y, T, ε) / n` is the library's
finite-scale cost, for continuous `T`. -/
theorem orbitComplexityN_div_eq {T : X → X} (hT : Continuous T) (y : X) {n : ℕ} (hn : 1 ≤ n)
    {ε : ℝ} (hε : 0 < ε) :
    (orbitComplexityN P.ι T A y n ε : ℝ≥0∞) / n =
      PointToSet.finiteScaleBSCost P T (fun _ ↦ 1) A y n ε := by
  rw [PointToSet.entropiesAndOrbitComplexities_rate P T hT A y n hn ε hε,
    PointToSet.orbitComplexityNat, orbitComplexityN_eq]
  obtain ⟨i, hi⟩ := PointToSet.bowen_ball_dense P T hT y n hn ε hε
  have hne : PointToSet.orbitComplexity P T A y n ε ≠ ⊤ :=
    ne_top_of_le_ne_top (ENat.natCast_ne_top (PointToSet.oracleNatComplexity A i)) (iInf₂_le i hi)
  conv_lhs => rw [← ENat.natCast_toNat hne]
  rw [ENat.toENNReal_coe]

/-- At a positive radius, the plain liminf and limsup of `K_n^A / n` are the library's
`orbitComplexityAt`, for continuous `T`. -/
theorem orbitComplexityAt_eq {T : X → X} (hT : Continuous T) (y : X) {ε : ℝ} (hε : 0 < ε) :
    (liminf (fun n : ℕ ↦ (orbitComplexityN P.ι T A y n ε : ℝ≥0∞) / n) atTop,
      limsup (fun n : ℕ ↦ (orbitComplexityN P.ι T A y n ε : ℝ≥0∞) / n) atTop) =
      PointToSet.orbitComplexityAt P T A y ε := by
  have h : (fun n : ℕ ↦ (orbitComplexityN P.ι T A y n ε : ℝ≥0∞) / n) =ᶠ[atTop]
      fun n ↦ PointToSet.finiteScaleBSCost P T (fun _ ↦ 1) A y n ε :=
    (eventually_ge_atTop 1).mono fun n hn ↦ orbitComplexityN_div_eq P A hT y hn hε
  exact Prod.ext (liminf_congr h) (limsup_congr h)

/-- The plain lower orbit complexity is the library's, for continuous `T`. -/
theorem lowerOrbitComplexity_eq {T : X → X} (hT : Continuous T) (y : X) :
    lowerOrbitComplexity P.ι T A y = (PointToSet.orbitComplexities P T A y).1 := by
  refine le_antisymm (iSup₂_le fun ε hε ↦ ?_) ?_
  · have h := congrArg Prod.fst (orbitComplexityAt_eq P A hT y hε)
    exact h.trans_le (PointToSet.orbitComplexityAt_le_orbitComplexities P T A y hε).1
  · rw [PointToSet.orbitComplexities_eq_iSup_orbitComplexityAt]
    refine iSup_le fun p ↦ ?_
    have h := congrArg Prod.fst (orbitComplexityAt_eq P A hT y (PointToSet.dyadicRadius_pos p))
    exact h.symm.trans_le (le_iSup₂_of_le (PointToSet.dyadicRadius p)
      (PointToSet.dyadicRadius_pos p) le_rfl)

/-- The plain upper orbit complexity is the library's, for continuous `T`. -/
theorem upperOrbitComplexity_eq {T : X → X} (hT : Continuous T) (y : X) :
    upperOrbitComplexity P.ι T A y = (PointToSet.orbitComplexities P T A y).2 := by
  refine le_antisymm (iSup₂_le fun ε hε ↦ ?_) ?_
  · have h := congrArg Prod.snd (orbitComplexityAt_eq P A hT y hε)
    exact h.trans_le (PointToSet.orbitComplexityAt_le_orbitComplexities P T A y hε).2
  · rw [PointToSet.orbitComplexities_eq_iSup_orbitComplexityAt]
    refine iSup_le fun p ↦ ?_
    have h := congrArg Prod.snd (orbitComplexityAt_eq P A hT y (PointToSet.dyadicRadius_pos p))
    exact h.symm.trans_le (le_iSup₂_of_le (PointToSet.dyadicRadius p)
      (PointToSet.dyadicRadius_pos p) le_rfl)

variable [MeasurableSpace X]

/-- The plain information `-log₂ q` is the library's `infoBits`. -/
theorem info_eq (q : ℝ≥0∞) : info q = PointToSet.infoBits q :=
  rfl

/-- At every radius, the plain liminf and limsup of `-(1/n) log μ(B_n)` are the library's
`localEntropyAt`. -/
theorem localEntropyAt_eq (μ : Measure X) (T : X → X) (y : X) (ε : ℝ) :
    (liminf (fun n : ℕ ↦ info (μ (bowenBall T n y ε)) / n) atTop,
      limsup (fun n : ℕ ↦ info (μ (bowenBall T n y ε)) / n) atTop) =
      PointToSet.localEntropyAt μ T y ε := by
  simp only [bowenBall_eq]
  rfl

/-- The plain lower local entropy is the library's. -/
theorem lowerLocalEntropy_eq (μ : Measure X) (T : X → X) (y : X) :
    lowerLocalEntropy μ T y = (PointToSet.localEntropy μ T y).1 := by
  refine le_antisymm (iSup₂_le fun ε hε ↦ ?_) (iSup_le fun p ↦ ?_)
  · have h := congrArg Prod.fst (localEntropyAt_eq μ T y ε)
    exact h.trans_le (PointToSet.localEntropyAt_le_localEntropy μ T y hε).1
  · have h := congrArg Prod.fst (localEntropyAt_eq μ T y (PointToSet.dyadicRadius p))
    exact h.symm.trans_le (le_iSup₂_of_le (PointToSet.dyadicRadius p)
      (PointToSet.dyadicRadius_pos p) le_rfl)

/-- The plain upper local entropy is the library's. -/
theorem upperLocalEntropy_eq (μ : Measure X) (T : X → X) (y : X) :
    upperLocalEntropy μ T y = (PointToSet.localEntropy μ T y).2 := by
  refine le_antisymm (iSup₂_le fun ε hε ↦ ?_) (iSup_le fun p ↦ ?_)
  · have h := congrArg Prod.snd (localEntropyAt_eq μ T y ε)
    exact h.trans_le (PointToSet.localEntropyAt_le_localEntropy μ T y hε).2
  · have h := congrArg Prod.snd (localEntropyAt_eq μ T y (PointToSet.dyadicRadius p))
    exact h.symm.trans_le (le_iSup₂_of_le (PointToSet.dyadicRadius p)
      (PointToSet.dyadicRadius_pos p) le_rfl)

end Complexity

/-! ### Kolmogorov–Sinai entropy -/

section KS

variable {X : Type*} [MeasurableSpace X]

omit [MeasurableSpace X] in
/-- The plain cells of `ξⁿ` are the library's `refinement`. -/
theorem refinementCell_eq (T : X → X) {p : ℕ} (ξ : Fin p → Set X) (n : ℕ) :
    refinementCell T ξ n = Ergodic.refinement T ξ n :=
  rfl

/-- Plain finite measurable partitions are the library's. -/
theorem isFinitePartition_iff {p : ℕ} (ξ : Fin p → Set X) :
    IsFinitePartition ξ ↔ Ergodic.IsMeasurablePartition ξ :=
  ⟨fun ⟨h1, h2, h3⟩ ↦ ⟨h1, h2, h3⟩, fun ⟨h1, h2, h3⟩ ↦ ⟨h1, h2, h3⟩⟩

/-- The plain `H_μ(ξⁿ)` is the library's `refinementEntropy`. -/
theorem refinementEntropy_eq (μ : Measure X) (T : X → X) {p : ℕ} (ξ : Fin p → Set X) (n : ℕ) :
    refinementEntropy μ T ξ n = Ergodic.refinementEntropy μ T ξ n :=
  rfl

/-- For an invariant probability measure the plain Kolmogorov–Sinai entropy (with
`limsup_n H(ξⁿ)/n`) is the library's (with `inf_{n ≥ 1} H(ξⁿ)/n`). -/
theorem ksEntropy_eq {μ : Measure X} [IsProbabilityMeasure μ] {T : X → X}
    (hT : MeasurePreserving T μ μ) : ksEntropy μ T = Ergodic.ksEntropy μ T := by
  refine iSup_congr fun p ↦ iSup_congr fun ξ ↦ iSup_congr_Prop (isFinitePartition_iff ξ) ?_
  intro hξ
  exact (Ergodic.tendsto_refinementEntropy_div hT hξ).limsup_eq

end KS

/-! ### The hypotheses are not vacuous -/

/-- Admissible oracles exist: for a dense sequence in a complete space, a continuous `T` and any
measure, every oracle above some `C` is admissible. -/
theorem exists_isAdmissible {X : Type*} [MetricSpace X] [CompleteSpace X] [MeasurableSpace X]
    {x : ℕ → X} (hx : DenseRange x) {T : X → X} (hT : Continuous T) (μ : Measure X) :
    ∃ C : Set ℕ, ∀ A : Set ℕ, charOracle C ≤ᵀ charOracle A → IsAdmissible x T μ A := by
  obtain ⟨C, hC⟩ := PointToSet.exists_measureAdmissible_base (toPresentation x hx) T hT μ
  exact ⟨C, fun A hA ↦ (isAdmissible_iff (toPresentation x hx) T μ).2 (hC A hA)⟩

/-- Martin-Löf random points have full measure. -/
theorem measure_compl_mlRandom {X : Type*} [MetricSpace X] [CompleteSpace X]
    [MeasurableSpace X] [BorelSpace X] {x : ℕ → X} (hx : DenseRange x) (A : Set ℕ)
    (μ : Measure X) : μ (MLRandom x A μ)ᶜ = 0 := by
  have h := PointToSet.measure_compl_randomPoints (toPresentation x hx) A μ
  rwa [← mlRandom_eq] at h

/-! ### The three statements -/

/-- [N, Theorem 3.3], first half, from `orbitComplexities_le_localEntropy`. -/
theorem theorem3_3_upper : Theorem3_3_upper.{u} := by
  intro X _ _ _ _ x T A μ hT hμ hA y
  have : IsFiniteMeasure μ := ⟨hμ.trans_lt ENNReal.one_lt_top⟩
  let P := toPresentation x hA.presentation.1
  have hA' : PointToSet.IsMeasureAdmissible P T μ A := (isAdmissible_iff P T μ).1 hA
  have h := PointToSet.orbitComplexities_le_localEntropy P T hT A μ hμ hA' y
  have e1 : lowerOrbitComplexity x T A y = _ := lowerOrbitComplexity_eq P A hT y
  have e2 : upperOrbitComplexity x T A y = _ := upperOrbitComplexity_eq P A hT y
  rw [e1, e2, lowerLocalEntropy_eq, upperLocalEntropy_eq]
  exact h

/-- [N, Theorem 3.3], from `orbitComplexities_eq_localEntropy`. -/
theorem theorem3_3 : Theorem3_3.{u} := by
  intro X _ _ _ _ x T A μ _ hT hA y hy
  let P := toPresentation x hA.presentation.1
  have hA' : PointToSet.IsMeasureAdmissible P T μ A := (isAdmissible_iff P T μ).1 hA
  have hy' : y ∈ PointToSet.randomPoints P A μ := by
    rw [← mlRandom_eq]
    exact hy
  have h := PointToSet.orbitComplexities_eq_localEntropy P T hT A μ hA' hy'
  have e1 : lowerOrbitComplexity x T A y = _ := lowerOrbitComplexity_eq P A hT y
  have e2 : upperOrbitComplexity x T A y = _ := upperOrbitComplexity_eq P A hT y
  rw [e1, e2, lowerLocalEntropy_eq, upperLocalEntropy_eq, h]
  exact ⟨rfl, rfl⟩

/-- [C, Theorem 1], from `orbitComplexities_eq_ksEntropy`. -/
theorem theorem1 : Theorem1.{u} := by
  intro X _ _ _ _ x T A μ _ hT hA herg y hy
  let P := toPresentation x hA.presentation.1
  have hA' : PointToSet.IsMeasureAdmissible P T μ A := (isAdmissible_iff P T μ).1 hA
  have hy' : y ∈ PointToSet.randomPoints P A μ := by
    rw [← mlRandom_eq]
    exact hy
  have h := PointToSet.orbitComplexities_eq_ksEntropy P T hT A μ hA' herg hy'
  have e1 : lowerOrbitComplexity x T A y = _ := lowerOrbitComplexity_eq P A hT y
  have e2 : upperOrbitComplexity x T A y = _ := upperOrbitComplexity_eq P A hT y
  rw [e1, e2, h, ksEntropy_eq herg.toMeasurePreserving]
  exact ⟨rfl, rfl⟩

end Kolmogorov.Trusted

