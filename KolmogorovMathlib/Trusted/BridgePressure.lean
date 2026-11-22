/-
Copyright (c) 2026 Emma Dinowitz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emma Dinowitz
-/
import KolmogorovMathlib.Trusted.StatementsPressure
import KolmogorovMathlib.Trusted.Bridge
import KolmogorovMathlib.PointToSet.Measure.PressurePointwise

/-!
# Bridge: the pressure statements follow from the library

Proofs of the four statements of `KolmogorovMathlib.Trusted.StatementsPressure`:

* `theorem8_3_pressure` (from `pointwisePressure_eq_localPressure`),
* `theorem8_3_bsDimension` (from `pointwiseBSDimension_eq_localBSDimension`),
* `corollary8_4_pressure` (from `lowerPressure_eq_iInf_measure`, `upperPressure_eq_iInf_measure`,
  `exists_atomic_measure_lowerPressure_eq`, `exists_atomic_measure_upperPressure_eq`),
* `corollary8_4_bsDimension` (from `lowerBSDimension_eq_iInf_measure`,
  `upperBSDimension_eq_iInf_measure`, `exists_atomic_measure_lowerBSDimension_eq`,
  `exists_atomic_measure_upperBSDimension_eq`),

through equivalences between each plain definition and the library's (the pilot bridge
`KolmogorovMathlib.Trusted.Bridge` supplies `toPresentation`, `bowenBall_eq`,
`isAdmissible_iff`, `mlRandom_eq`). For a presentation `P`:

* `lowerBirkhoffAverage_eq`, `isBirkhoffBoundedBelow_iff`: definitional;
* `lowerPointwisePressure_eq`, `upperPointwisePressure_eq`: `= (pointwisePressure P T φ A y).1,
  .2` (the plain cost `pressureCostN` is `finiteScalePressureRate` for `n ≥ 1`);
* `lowerPointwiseBSDimension_eq`, `upperPointwiseBSDimension_eq`:
  `= (pointwiseBSDimension P T u A y).1, .2` (`bsCostN_eq`: `= finiteScaleBSCost` at every `n`);
* `lowerLocalPressure_eq`, `upperLocalPressure_eq`: `= (localPressure μ T φ y).1, .2` for finite
  `μ` (the rate is antitone in the radius only for finite `μ`);
* `lowerLocalBSDimension_eq`, `upperLocalBSDimension_eq`: `= (localBSDimension μ T u y).1, .2`;
* `lowerPressure_eq`, `upperPressure_eq`: `= lowerPressure T φ p₀ Z`, `= upperPressure T φ p₀ Z`
  for every scale cut-off `p₀` (all quantities are antitone in the radius);
* `lowerBSDimension_eq`, `upperBSDimension_eq`: `= lowerBSDimension T u Z`,
  `= upperBSDimension T u Z`.

The scale limits are handled by `iSup_pos_eq_iSup_dyadic`: for a function antitone in the
radius, the supremum over `ε > 0` is the supremum over the dyadic radii `2^{-p}`, `p ≥ p₀`.
The library's `PressureData` is built from a dense sequence, a continuous map and a uniformly
continuous potential by `toPressureData`.
-/

namespace Kolmogorov.Trusted

open MeasureTheory Filter Set
open scoped ENNReal Computability

universe u

/-! ### Scale limits -/

/-- For a function antitone on positive radii, the supremum over `ε > 0` is the supremum over the
dyadic radii `2^{-p}` with `p ≥ p₀`. -/
theorem iSup_pos_eq_iSup_dyadic {α : Type*} [CompleteLattice α] (f : ℝ → α)
    (hf : ∀ ⦃ε ε' : ℝ⦄, 0 < ε → ε ≤ ε' → f ε' ≤ f ε) (p₀ : ℕ) :
    ⨆ (ε : ℝ) (_ : 0 < ε), f ε = ⨆ (p : ℕ) (_ : p₀ ≤ p), f (PointToSet.dyadicRadius p) := by
  refine le_antisymm (iSup₂_le fun ε hε ↦ ?_)
    (iSup₂_le fun p _ ↦ le_iSup₂_of_le _ (PointToSet.dyadicRadius_pos p) le_rfl)
  obtain ⟨p, hp⟩ := PointToSet.exists_dyadicRadius_lt hε
  have hle : PointToSet.dyadicRadius (max p p₀) ≤ ε :=
    (PointToSet.dyadicRadius_antitone (le_max_left p p₀)).trans hp.le
  exact (hf (PointToSet.dyadicRadius_pos _) hle).trans
    (le_iSup₂_of_le (f := fun (q : ℕ) (_ : p₀ ≤ q) ↦ f (PointToSet.dyadicRadius q))
      (max p p₀) (le_max_right p p₀) le_rfl)

/-- For a function antitone on positive radii, the supremum over `ε > 0` is the supremum over all
dyadic radii `2^{-p}`. -/
theorem iSup_pos_eq_iSup_dyadic' {α : Type*} [CompleteLattice α] (f : ℝ → α)
    (hf : ∀ ⦃ε ε' : ℝ⦄, 0 < ε → ε ≤ ε' → f ε' ≤ f ε) :
    ⨆ (ε : ℝ) (_ : 0 < ε), f ε = ⨆ p : ℕ, f (PointToSet.dyadicRadius p) := by
  rw [iSup_pos_eq_iSup_dyadic f hf 0]
  exact iSup_congr fun p ↦ iSup_pos (Nat.zero_le p)

/-- Bowen balls grow with the radius. -/
theorem bowenBall_mono {X : Type*} [MetricSpace X] (T : X → X) (n : ℕ) (y : X) {ε ε' : ℝ}
    (h : ε ≤ ε') : bowenBall T n y ε ⊆ bowenBall T n y ε' :=
  fun _ hz k hk ↦ (hz k hk).trans_le h

/-! ### Birkhoff averages and pointwise quantities -/

section Pointwise

variable {X : Type*} [MetricSpace X]

omit [MetricSpace X] in
/-- The plain lower Birkhoff average is the library's. -/
theorem lowerBirkhoffAverage_eq (T : X → X) (u : X → ℝ) (y : X) :
    lowerBirkhoffAverage T u y = PointToSet.lowerBirkhoffAverage T u y :=
  rfl

/-- Plain boundedness below of the Birkhoff averages is the library's. -/
theorem isBirkhoffBoundedBelow_iff [MeasurableSpace X] [BorelSpace X] (T : X → X) (φ : X → ℝ)
    (y : X) : IsBirkhoffBoundedBelow T φ y ↔ PointToSet.BirkhoffBoundedBelow T φ y :=
  Iff.rfl

variable (P : PointToSet.Presentation X)

/-- At positive orders the plain pressure cost is the library's `finiteScalePressureRate`. -/
theorem pressureCostN_eq (T : X → X) (φ : X → ℝ) (A : Set ℕ) (y : X) {n : ℕ} (hn : n ≠ 0)
    (ε : ℝ) : pressureCostN P.ι T φ A y n ε = PointToSet.finiteScalePressureRate P T φ A y n ε := by
  rw [PointToSet.finiteScalePressureRate, ite_eq_right hn]
  simp only [pressureCostN, bowenBall_eq]

/-- The plain pressure cost is antitone in the radius. -/
theorem pressureCostN_anti (x : ℕ → X) (T : X → X) (φ : X → ℝ) (A : Set ℕ) (y : X) (n : ℕ)
    {ε ε' : ℝ} (h : ε ≤ ε') : pressureCostN x T φ A y n ε' ≤ pressureCostN x T φ A y n ε :=
  iInf_mono fun _ ↦ iInf_mono' fun hi ↦ ⟨bowenBall_mono T n y h hi, le_rfl⟩

/-- At every radius, the plain pressure cost is eventually the library's. -/
theorem pressureCostN_eventuallyEq (T : X → X) (φ : X → ℝ) (A : Set ℕ) (y : X) (ε : ℝ) :
    (fun n ↦ pressureCostN P.ι T φ A y n ε) =ᶠ[atTop]
      fun n ↦ PointToSet.finiteScalePressureRate P T φ A y n ε :=
  (eventually_ge_atTop 1).mono fun _ hn ↦ pressureCostN_eq P T φ A y (by omega) ε

/-- The plain lower pointwise pressure is the library's. -/
theorem lowerPointwisePressure_eq (T : X → X) (φ : X → ℝ) (A : Set ℕ) (y : X) :
    lowerPointwisePressure P.ι T φ A y = (PointToSet.pointwisePressure P T φ A y).1 := by
  rw [lowerPointwisePressure, iSup_pos_eq_iSup_dyadic'
    (fun ε ↦ liminf (fun n ↦ pressureCostN P.ι T φ A y n ε) atTop)
    fun _ _ _ h ↦ liminf_le_liminf (.of_forall fun n ↦ pressureCostN_anti _ T φ A y n h)]
  exact iSup_congr fun p ↦ liminf_congr (pressureCostN_eventuallyEq P T φ A y _)

/-- The plain upper pointwise pressure is the library's. -/
theorem upperPointwisePressure_eq (T : X → X) (φ : X → ℝ) (A : Set ℕ) (y : X) :
    upperPointwisePressure P.ι T φ A y = (PointToSet.pointwisePressure P T φ A y).2 := by
  rw [upperPointwisePressure, iSup_pos_eq_iSup_dyadic'
    (fun ε ↦ limsup (fun n ↦ pressureCostN P.ι T φ A y n ε) atTop)
    fun _ _ _ h ↦ limsup_le_limsup (.of_forall fun n ↦ pressureCostN_anti _ T φ A y n h)]
  exact iSup_congr fun p ↦ limsup_congr (pressureCostN_eventuallyEq P T φ A y _)

/-- The plain BS cost is the library's `finiteScaleBSCost`, at every order. -/
theorem bsCostN_eq (T : X → X) (u : X → ℝ) (A : Set ℕ) (y : X) (n : ℕ) (ε : ℝ) :
    bsCostN P.ι T u A y n ε = PointToSet.finiteScaleBSCost P T u A y n ε := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [bsCostN, PointToSet.finiteScaleBSCost]
  · rw [PointToSet.finiteScaleBSCost, ite_eq_right hn]
    simp only [bsCostN, bowenBall_eq]

/-- The plain BS cost is antitone in the radius. -/
theorem bsCostN_anti (x : ℕ → X) (T : X → X) (u : X → ℝ) (A : Set ℕ) (y : X) (n : ℕ)
    {ε ε' : ℝ} (h : ε ≤ ε') : bsCostN x T u A y n ε' ≤ bsCostN x T u A y n ε :=
  iInf_mono fun _ ↦ iInf_mono' fun hi ↦ ⟨bowenBall_mono T n y h hi, le_rfl⟩

/-- The plain lower pointwise BS dimension is the library's. -/
theorem lowerPointwiseBSDimension_eq (T : X → X) (u : X → ℝ) (A : Set ℕ) (y : X) :
    lowerPointwiseBSDimension P.ι T u A y = (PointToSet.pointwiseBSDimension P T u A y).1 := by
  rw [lowerPointwiseBSDimension, iSup_pos_eq_iSup_dyadic'
    (fun ε ↦ liminf (fun n ↦ bsCostN P.ι T u A y n ε) atTop)
    fun _ _ _ h ↦ liminf_le_liminf (.of_forall fun n ↦ bsCostN_anti _ T u A y n h)]
  simp only [bsCostN_eq]
  rfl

/-- The plain upper pointwise BS dimension is the library's. -/
theorem upperPointwiseBSDimension_eq (T : X → X) (u : X → ℝ) (A : Set ℕ) (y : X) :
    upperPointwiseBSDimension P.ι T u A y = (PointToSet.pointwiseBSDimension P T u A y).2 := by
  rw [upperPointwiseBSDimension, iSup_pos_eq_iSup_dyadic'
    (fun ε ↦ limsup (fun n ↦ bsCostN P.ι T u A y n ε) atTop)
    fun _ _ _ h ↦ limsup_le_limsup (.of_forall fun n ↦ bsCostN_anti _ T u A y n h)]
  simp only [bsCostN_eq]
  rfl

end Pointwise

/-! ### Local pressure and local BS dimension -/

section Local

variable {X : Type*} [MetricSpace X] [MeasurableSpace X]

/-- The plain local pressure rate is the library's `localPressureRate`. -/
theorem localPressureN_eq (μ : Measure X) (T : X → X) (φ : X → ℝ) (y : X) (n : ℕ) (ε : ℝ) :
    localPressureN μ T φ y n ε = PointToSet.localPressureRate μ T φ y n ε := by
  simp only [localPressureN, PointToSet.localPressureRate, bowenBall_eq]

/-- For a finite measure the local pressure rate is antitone in the radius. -/
theorem localPressureN_anti (μ : Measure X) [IsFiniteMeasure μ] (T : X → X) (φ : X → ℝ) (y : X)
    (n : ℕ) {ε ε' : ℝ} (h : ε ≤ ε') : localPressureN μ T φ y n ε' ≤ localPressureN μ T φ y n ε := by
  have hsub : μ (bowenBall T n y ε) ≤ μ (bowenBall T n y ε') :=
    measure_mono (bowenBall_mono T n y h)
  unfold localPressureN
  split_ifs with h1 h2 h2
  · exact le_rfl
  · exact absurd (le_antisymm (hsub.trans h1.le) zero_le) h2
  · exact le_top
  · rw [EReal.coe_le_coe_iff]
    refine div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg n)
    have hpos : 0 < (μ (bowenBall T n y ε)).toReal := ENNReal.toReal_pos h2 (measure_ne_top μ _)
    have hle : (μ (bowenBall T n y ε)).toReal ≤ (μ (bowenBall T n y ε')).toReal :=
      ENNReal.toReal_mono (measure_ne_top μ _) hsub
    linarith [Real.logb_le_logb_of_le one_lt_two hpos hle]

/-- For a finite measure the plain lower local pressure is the library's. -/
theorem lowerLocalPressure_eq (μ : Measure X) [IsFiniteMeasure μ] (T : X → X) (φ : X → ℝ)
    (y : X) : lowerLocalPressure μ T φ y = (PointToSet.localPressure μ T φ y).1 := by
  rw [lowerLocalPressure, iSup_pos_eq_iSup_dyadic'
    (fun ε ↦ liminf (fun n ↦ localPressureN μ T φ y n ε) atTop)
    fun _ _ _ h ↦ liminf_le_liminf (.of_forall fun n ↦ localPressureN_anti μ T φ y n h)]
  simp only [localPressureN_eq]
  rfl

/-- For a finite measure the plain upper local pressure is the library's. -/
theorem upperLocalPressure_eq (μ : Measure X) [IsFiniteMeasure μ] (T : X → X) (φ : X → ℝ)
    (y : X) : upperLocalPressure μ T φ y = (PointToSet.localPressure μ T φ y).2 := by
  rw [upperLocalPressure, iSup_pos_eq_iSup_dyadic'
    (fun ε ↦ limsup (fun n ↦ localPressureN μ T φ y n ε) atTop)
    fun _ _ _ h ↦ limsup_le_limsup (.of_forall fun n ↦ localPressureN_anti μ T φ y n h)]
  simp only [localPressureN_eq]
  rfl

/-- The plain local BS rate is the library's `localBSRate`. -/
theorem localBSRate_eq (μ : Measure X) (T : X → X) (u : X → ℝ) (y : X) (n : ℕ) (ε : ℝ) :
    info (μ (bowenBall T n y ε)) / ENNReal.ofReal (birkhoffSum T u n y) =
      PointToSet.localBSRate μ T u y n ε := by
  rw [info_eq, bowenBall_eq]
  rfl

/-- The local BS rate is antitone in the radius. -/
theorem localBSRate_anti (μ : Measure X) (T : X → X) (u : X → ℝ) (y : X) (n : ℕ) {ε ε' : ℝ}
    (h : ε ≤ ε') :
    info (μ (bowenBall T n y ε')) / ENNReal.ofReal (birkhoffSum T u n y) ≤
      info (μ (bowenBall T n y ε)) / ENNReal.ofReal (birkhoffSum T u n y) := by
  rw [info_eq, info_eq]
  exact ENNReal.div_le_div_right
    (PointToSet.infoBits_antitone (measure_mono (bowenBall_mono T n y h))) _

/-- The plain lower local BS dimension is the library's. -/
theorem lowerLocalBSDimension_eq (μ : Measure X) (T : X → X) (u : X → ℝ) (y : X) :
    lowerLocalBSDimension μ T u y = (PointToSet.localBSDimension μ T u y).1 := by
  rw [lowerLocalBSDimension, iSup_pos_eq_iSup_dyadic'
    (fun ε ↦ liminf (fun n ↦ info (μ (bowenBall T n y ε)) /
      ENNReal.ofReal (birkhoffSum T u n y)) atTop)
    fun _ _ _ h ↦ liminf_le_liminf (.of_forall fun n ↦ localBSRate_anti μ T u y n h)]
  simp only [localBSRate_eq]
  rfl

/-- The plain upper local BS dimension is the library's. -/
theorem upperLocalBSDimension_eq (μ : Measure X) (T : X → X) (u : X → ℝ) (y : X) :
    upperLocalBSDimension μ T u y = (PointToSet.localBSDimension μ T u y).2 := by
  rw [upperLocalBSDimension, iSup_pos_eq_iSup_dyadic'
    (fun ε ↦ limsup (fun n ↦ info (μ (bowenBall T n y ε)) /
      ENNReal.ofReal (birkhoffSum T u n y)) atTop)
    fun _ _ _ h ↦ limsup_le_limsup (.of_forall fun n ↦ localBSRate_anti μ T u y n h)]
  simp only [localBSRate_eq]
  rfl

end Local

/-! ### Pressure and BS dimension of sets -/

section Sets

variable {X : Type*} [MetricSpace X]

/-- An infimum over the library's Bowen cover families is the infimum over plain covers, for a
positive order cut-off. -/
theorem iInf_bowenCover_eq {α : Type*} [CompleteLattice α] (T : X → X) (Z : Set X) (r : ℝ)
    {N : ℕ} (hN : 1 ≤ N) (g : (I : Set ℕ) → (I → X) → (I → ℕ) → α) :
    ⨅ (C : PointToSet.BowenCoverFamily X) (_ : PointToSet.IsBowenCover T Z r N C),
        g C.index C.center C.order =
      ⨅ (I : Set ℕ) (c : I → X) (m : I → ℕ) (_ : IsBowenCover T Z r N c m), g I c m := by
  have hmax : max 1 N = N := max_eq_right hN
  apply le_antisymm
  · refine le_iInf fun I ↦ le_iInf fun c ↦ le_iInf fun m ↦ le_iInf fun hc ↦ ?_
    refine iInf₂_le_of_le (⟨I, c, m⟩ : PointToSet.BowenCoverFamily X)
      ⟨fun j ↦ by rw [hmax]; exact hc.1 j, ?_⟩ le_rfl
    simpa only [bowenBall_eq] using hc.2
  · refine le_iInf₂ fun C hC ↦ iInf_le_of_le C.index (iInf_le_of_le C.center
      (iInf_le_of_le C.order (iInf_le_of_le ⟨fun j ↦ by rw [← hmax]; exact hC.1 j, ?_⟩ le_rfl)))
    simpa only [bowenBall_eq] using hC.2

/-- A plain cover at a radius is a cover at every larger radius. -/
theorem IsBowenCover.mono {T : X → X} {Z : Set X} {ε ε' : ℝ} {N : ℕ} {I : Set ℕ} {c : I → X}
    {m : I → ℕ} (hc : IsBowenCover T Z ε N c m) (h : ε ≤ ε') : IsBowenCover T Z ε' N c m :=
  ⟨hc.1, hc.2.trans (iUnion_mono fun j ↦ bowenBall_mono T (m j) (c j) h)⟩

/-! #### Lower pressure -/

/-- The lower pressure at the scale `ε`: the critical exponent of the pressure content. -/
noncomputable def lowerPressureScale (T : X → X) (φ : X → ℝ) (Z : Set X) (ε : ℝ) : EReal :=
  ⨅ (s : ℝ) (_ : ⨆ (N : ℕ) (_ : 1 ≤ N), pressureContent T φ Z s ε N = 0), (s : EReal)

/-- For a positive order cut-off the plain pressure content is the library's `lowerContent`. -/
theorem pressureContent_eq (T : X → X) (φ : X → ℝ) (Z : Set X) (s ε : ℝ) {N : ℕ}
    (hN : 1 ≤ N) :
    pressureContent T φ Z s ε N = PointToSet.lowerContent T φ .centered Z s ε N :=
  (iInf_bowenCover_eq T Z ε hN fun I c m ↦
    ∑' j : I, (2 : ℝ≥0∞) ^ (-s * m j) * (2 : ℝ≥0∞) ^ birkhoffSum T φ (m j) (c j)).symm

/-- The plain lower pressure at a scale is the library's centered `lowerPressureAt`. -/
theorem lowerPressureScale_eq (T : X → X) (φ : X → ℝ) (Z : Set X) (ε : ℝ) :
    lowerPressureScale T φ Z ε = PointToSet.lowerPressureAt T φ .centered Z ε := by
  refine iInf_congr fun s ↦ ?_
  have h : ⨆ (N : ℕ) (_ : 1 ≤ N), pressureContent T φ Z s ε N =
      PointToSet.lowerContentLimit T φ .centered Z s ε :=
    iSup_congr fun N ↦ iSup_congr fun hN ↦ pressureContent_eq T φ Z s ε hN
  rw [h]

/-- The pressure content decreases as the radius grows. -/
theorem pressureContent_anti (T : X → X) (φ : X → ℝ) (Z : Set X) (s : ℝ) (N : ℕ) {ε ε' : ℝ}
    (h : ε ≤ ε') : pressureContent T φ Z s ε' N ≤ pressureContent T φ Z s ε N :=
  iInf_mono fun _ ↦ iInf_mono fun _ ↦ iInf_mono fun _ ↦ iInf_mono' fun hc ↦ ⟨hc.mono h, le_rfl⟩

/-- The lower pressure at a scale is antitone in the scale. -/
theorem lowerPressureScale_anti (T : X → X) (φ : X → ℝ) (Z : Set X) {ε ε' : ℝ} (h : ε ≤ ε') :
    lowerPressureScale T φ Z ε' ≤ lowerPressureScale T φ Z ε :=
  iInf_mono fun s ↦ iInf_mono' fun hs ↦ ⟨nonpos_iff_eq_zero.1
    ((iSup₂_mono fun N _ ↦ pressureContent_anti T φ Z s N h).trans hs.le), le_rfl⟩

/-- The plain lower pressure is the library's, for every scale cut-off `p₀`. -/
theorem lowerPressure_eq (T : X → X) (φ : X → ℝ) (p₀ : ℕ) (Z : Set X) :
    lowerPressure T φ Z = PointToSet.lowerPressure T φ p₀ Z := by
  rw [show lowerPressure T φ Z = ⨆ (ε : ℝ) (_ : 0 < ε), lowerPressureScale T φ Z ε from rfl,
    iSup_pos_eq_iSup_dyadic _ (fun _ _ _ h ↦ lowerPressureScale_anti T φ Z h) p₀]
  exact iSup_congr fun p ↦ iSup_congr fun _ ↦ lowerPressureScale_eq T φ Z _

/-! #### Upper pressure -/

/-- The upper pressure at the scale `ε`: the countably modified upper capacity pressure. -/
noncomputable def upperPressureScale (T : X → X) (φ : X → ℝ) (Z : Set X) (ε : ℝ) : EReal :=
  ⨅ (Y : ℕ → Set X) (_ : Z ⊆ ⋃ k, Y k), ⨆ k,
    limsup (fun n : ℕ ↦ ENNReal.log (pressurePartitionSum T φ (Y k) n ε) *
      (((n * Real.log 2)⁻¹ : ℝ) : EReal)) atTop

/-- The plain partition sum is the library's centered `partitionSum`. -/
theorem pressurePartitionSum_eq (T : X → X) (φ : X → ℝ) (Y : Set X) (n : ℕ) (ε : ℝ) :
    pressurePartitionSum T φ Y n ε = PointToSet.partitionSum T φ .centered Y n ε := by
  simp only [pressurePartitionSum, PointToSet.partitionSum, PointToSet.partitionCoverCost,
    PointToSet.pressureBallWeight, bowenBall_eq]

/-- At positive orders the plain rate `ln q / (n ln 2)` is the library's `pressureRate`. -/
theorem log_mul_eq_pressureRate (q : ℕ → ℝ≥0∞) {n : ℕ} (hn : n ≠ 0) :
    ENNReal.log (q n) * (((n * Real.log 2)⁻¹ : ℝ) : EReal) = PointToSet.pressureRate q n := by
  rw [PointToSet.pressureRate_eq_log_mul q hn, mul_inv, mul_comm (n : ℝ)⁻¹]

/-- The plain upper pressure at a scale is the library's centered `modifiedUpperPressure`. -/
theorem upperPressureScale_eq (T : X → X) (φ : X → ℝ) (Z : Set X) (ε : ℝ) :
    upperPressureScale T φ Z ε = PointToSet.modifiedUpperPressure T φ .centered Z ε := by
  refine iInf_congr fun Y ↦ iInf_congr fun _ ↦ iSup_congr fun k ↦ limsup_congr ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  rw [pressurePartitionSum_eq]
  exact log_mul_eq_pressureRate (fun n ↦ PointToSet.partitionSum T φ .centered (Y k) n ε)
    (by omega)

/-- The partition sum decreases as the radius grows. -/
theorem pressurePartitionSum_anti (T : X → X) (φ : X → ℝ) (Y : Set X) (n : ℕ) {ε ε' : ℝ}
    (h : ε ≤ ε') : pressurePartitionSum T φ Y n ε' ≤ pressurePartitionSum T φ Y n ε :=
  iInf_mono fun _ ↦ iInf_mono' fun hF ↦
    ⟨⟨hF.1, hF.2.trans (iUnion₂_mono fun c _ ↦ bowenBall_mono T n c h)⟩, le_rfl⟩

/-- The upper pressure at a scale is antitone in the scale. -/
theorem upperPressureScale_anti (T : X → X) (φ : X → ℝ) (Z : Set X) {ε ε' : ℝ} (h : ε ≤ ε') :
    upperPressureScale T φ Z ε' ≤ upperPressureScale T φ Z ε := by
  refine iInf_mono fun Y ↦ iInf_mono fun _ ↦ iSup_mono fun k ↦ limsup_le_limsup
    (.of_forall fun n ↦ mul_le_mul_of_nonneg_right
      (ENNReal.log_le_log (pressurePartitionSum_anti T φ (Y k) n h)) ?_)
  exact EReal.coe_nonneg.2 (inv_nonneg.2 (mul_nonneg n.cast_nonneg (Real.log_nonneg one_le_two)))

/-- The plain upper pressure is the library's, for every scale cut-off `p₀`. -/
theorem upperPressure_eq (T : X → X) (φ : X → ℝ) (p₀ : ℕ) (Z : Set X) :
    upperPressure T φ Z = PointToSet.upperPressure T φ p₀ Z := by
  rw [show upperPressure T φ Z = ⨆ (ε : ℝ) (_ : 0 < ε), upperPressureScale T φ Z ε from rfl,
    iSup_pos_eq_iSup_dyadic _ (fun _ _ _ h ↦ upperPressureScale_anti T φ Z h) p₀]
  exact iSup_congr fun p ↦ iSup_congr fun _ ↦ upperPressureScale_eq T φ Z _

/-! #### BS dimensions -/

/-- The plain BS weight is the library's `bsBallWeight`. -/
theorem bsWeight_eq (T : X → X) (u : X → ℝ) (s : ℝ) (n : ℕ) (c : X) (ε : ℝ) :
    bsWeight T u s n c ε = PointToSet.bsBallWeight T u s n c ε := by
  simp only [bsWeight, PointToSet.bsBallWeight, PointToSet.pressureBallWeight, bowenBall_eq]

/-- For `s ≥ 0` the BS weight decreases as the radius grows. -/
theorem bsWeight_anti (T : X → X) (u : X → ℝ) {s : ℝ} (hs : 0 ≤ s) (n : ℕ) (c : X) {ε ε' : ℝ}
    (h : ε ≤ ε') : bsWeight T u s n c ε' ≤ bsWeight T u s n c ε := by
  simp only [bsWeight, ENNReal.rpow_neg]
  exact ENNReal.inv_le_inv.2 (ENNReal.rpow_le_rpow
    (biSup_mono fun z hz ↦ bowenBall_mono T n c h hz) hs)

/-- For a positive order cut-off the plain BS content is the library's `lowerBSMass`. -/
theorem bsContent_eq (T : X → X) (u : X → ℝ) (Z : Set X) (s ε : ℝ) {N : ℕ} (hN : 1 ≤ N) :
    bsContent T u Z s ε N = PointToSet.lowerBSMass T u Z s ε N := by
  simp only [bsContent, bsWeight_eq]
  exact (iInf_bowenCover_eq T Z ε hN fun I c m ↦
    ∑' j : I, PointToSet.bsBallWeight T u s (m j) (c j) ε).symm

/-- For `s ≥ 0` the BS content decreases as the radius grows. -/
theorem bsContent_anti (T : X → X) (u : X → ℝ) (Z : Set X) {s : ℝ} (hs : 0 ≤ s) (N : ℕ)
    {ε ε' : ℝ} (h : ε ≤ ε') : bsContent T u Z s ε' N ≤ bsContent T u Z s ε N :=
  iInf_mono fun _ ↦ iInf_mono fun c ↦ iInf_mono fun m ↦ iInf_mono' fun hc ↦
    ⟨hc.mono h, ENNReal.tsum_le_tsum fun j ↦ bsWeight_anti T u hs (m j) (c j) h⟩

/-- The lower BS dimension at the scale `ε`. -/
noncomputable def lowerBSDimensionScale (T : X → X) (u : X → ℝ) (Z : Set X) (ε : ℝ) : ℝ≥0∞ :=
  ⨅ (s : ℝ) (_ : 0 ≤ s) (_ : ⨆ (N : ℕ) (_ : 1 ≤ N), bsContent T u Z s ε N = 0),
    ENNReal.ofReal s

/-- The plain lower BS dimension at a scale is the library's `lowerBSDimensionAt`. -/
theorem lowerBSDimensionScale_eq (T : X → X) (u : X → ℝ) (Z : Set X) (ε : ℝ) :
    lowerBSDimensionScale T u Z ε = PointToSet.lowerBSDimensionAt T u Z ε := by
  refine iInf_congr fun s ↦ ?_
  have h : ⨆ (N : ℕ) (_ : 1 ≤ N), bsContent T u Z s ε N =
      PointToSet.lowerBSMassLimit T u Z s ε :=
    iSup_congr fun N ↦ iSup_congr fun hN ↦ bsContent_eq T u Z s ε hN
  rw [h]

/-- The lower BS dimension at a scale is antitone in the scale. -/
theorem lowerBSDimensionScale_anti (T : X → X) (u : X → ℝ) (Z : Set X) {ε ε' : ℝ}
    (h : ε ≤ ε') : lowerBSDimensionScale T u Z ε' ≤ lowerBSDimensionScale T u Z ε :=
  iInf_mono fun _ ↦ iInf_mono fun hs ↦ iInf_mono' fun h0 ↦ ⟨nonpos_iff_eq_zero.1
    ((iSup₂_mono fun N _ ↦ bsContent_anti T u Z hs N h).trans h0.le), le_rfl⟩

/-- The plain lower BS dimension is the library's. -/
theorem lowerBSDimension_eq (T : X → X) (u : X → ℝ) (Z : Set X) :
    lowerBSDimension T u Z = PointToSet.lowerBSDimension T u Z := by
  rw [show lowerBSDimension T u Z = ⨆ (ε : ℝ) (_ : 0 < ε), lowerBSDimensionScale T u Z ε
      from rfl,
    iSup_pos_eq_iSup_dyadic' _ (fun _ _ _ h ↦ lowerBSDimensionScale_anti T u Z h)]
  exact iSup_congr fun p ↦ lowerBSDimensionScale_eq T u Z _

/-- The plain fixed-order BS sum is the library's `bsPartitionSum`. -/
theorem bsPartitionSum_eq (T : X → X) (u : X → ℝ) (Y : Set X) (s ε : ℝ) (n : ℕ) :
    bsPartitionSum T u Y s ε n = PointToSet.bsPartitionSum T u Y s ε n := by
  simp only [bsPartitionSum, PointToSet.bsPartitionSum, PointToSet.bsPartitionCoverCost,
    bsWeight_eq, bowenBall_eq]

/-- For `s ≥ 0` the fixed-order BS sum decreases as the radius grows. -/
theorem bsPartitionSum_anti (T : X → X) (u : X → ℝ) (Y : Set X) {s : ℝ} (hs : 0 ≤ s) (n : ℕ)
    {ε ε' : ℝ} (h : ε ≤ ε') : bsPartitionSum T u Y s ε' n ≤ bsPartitionSum T u Y s ε n :=
  iInf_mono fun _ ↦ iInf_mono' fun hF ↦
    ⟨⟨hF.1, hF.2.trans (iUnion₂_mono fun c _ ↦ bowenBall_mono T n c h)⟩,
      ENNReal.tsum_le_tsum fun c ↦ bsWeight_anti T u hs n c h⟩

/-- The upper BS dimension at the scale `ε`. -/
noncomputable def upperBSDimensionScale (T : X → X) (u : X → ℝ) (Z : Set X) (ε : ℝ) : ℝ≥0∞ :=
  ⨅ (Y : ℕ → Set X) (_ : (∀ k, Y k ⊆ Z) ∧ Z ⊆ ⋃ k, Y k), ⨆ k,
    ⨅ (s : ℝ) (_ : 0 ≤ s) (_ : limsup (fun n ↦ bsPartitionSum T u (Y k) s ε n) atTop < ⊤),
      ENNReal.ofReal s

/-- The plain upper BS dimension at a scale is the library's `modifiedUpperBSDimension`. -/
theorem upperBSDimensionScale_eq (T : X → X) (u : X → ℝ) (Z : Set X) (ε : ℝ) :
    upperBSDimensionScale T u Z ε = PointToSet.modifiedUpperBSDimension T u Z ε := by
  simp only [upperBSDimensionScale, bsPartitionSum_eq]
  rfl

/-- The upper BS dimension at a scale is antitone in the scale. -/
theorem upperBSDimensionScale_anti (T : X → X) (u : X → ℝ) (Z : Set X) {ε ε' : ℝ}
    (h : ε ≤ ε') : upperBSDimensionScale T u Z ε' ≤ upperBSDimensionScale T u Z ε :=
  iInf_mono fun Y ↦ iInf_mono fun _ ↦ iSup_mono fun k ↦ iInf_mono fun s ↦ iInf_mono fun hs ↦
    iInf_mono' fun hfin ↦ ⟨(limsup_le_limsup
      (.of_forall fun n ↦ bsPartitionSum_anti T u (Y k) hs n h)).trans_lt hfin, le_rfl⟩

/-- The plain upper BS dimension is the library's. -/
theorem upperBSDimension_eq (T : X → X) (u : X → ℝ) (Z : Set X) :
    upperBSDimension T u Z = PointToSet.upperBSDimension T u Z := by
  rw [show upperBSDimension T u Z = ⨆ (ε : ℝ) (_ : 0 < ε), upperBSDimensionScale T u Z ε
      from rfl,
    iSup_pos_eq_iSup_dyadic' _ (fun _ _ _ h ↦ upperBSDimensionScale_anti T u Z h)]
  exact iSup_congr fun p ↦ upperBSDimensionScale_eq T u Z _

end Sets

/-! ### Pressure data -/

/-- The library's `PressureData` of a presentation, a continuous map and a uniformly continuous
potential, with a modulus of uniform continuity chosen by `small_scale_oscillation`. -/
noncomputable def toPressureData {X : Type*} [MetricSpace X] (P : PointToSet.Presentation X)
    (T : X → X) (hT : Continuous T) (φ : X → ℝ) (hφ : UniformContinuous φ) :
    PointToSet.PressureData X :=
  have h := PointToSet.small_scale_oscillation φ hφ
  { presentation := P
    T := T
    continuous_T := hT
    φ := φ
    uniformContinuous_φ := hφ
    p₀ := h.choose_spec.2.2.choose
    ω := h.choose
    ω_pos := fun p _ ↦ h.choose_spec.1 p
    ω_tendsto := h.choose_spec.2.1
    oscillation := fun p hp a b hab ↦ h.choose_spec.2.2.choose_spec p hp a b
      (hab.trans (by linarith [PointToSet.dyadicRadius_pos p])) }

/-! ### The four statements -/

/-- [N, Theorem 8.3(ii)], pressure, from `pointwisePressure_eq_localPressure`. -/
theorem theorem8_3_pressure : Theorem8_3_pressure.{u} := by
  intro X _ _ _ _ x T φ A μ _ hT hφ hA y hy hb
  let P := toPresentation x hA.presentation.1
  have hA' : PointToSet.IsMeasureAdmissible P T μ A := (isAdmissible_iff P T μ).1 hA
  have hy' : y ∈ PointToSet.randomPoints P A μ := by
    rw [← mlRandom_eq]
    exact hy
  have h := PointToSet.pointwisePressure_eq_localPressure P T hT φ hφ A μ hA' hy' hb
  have e1 : lowerPointwisePressure x T φ A y = _ := lowerPointwisePressure_eq P T φ A y
  have e2 : upperPointwisePressure x T φ A y = _ := upperPointwisePressure_eq P T φ A y
  rw [e1, e2, lowerLocalPressure_eq, upperLocalPressure_eq, h]
  exact ⟨rfl, rfl⟩

/-- [N, Theorem 8.3(ii)], BS dimension, from `pointwiseBSDimension_eq_localBSDimension`. -/
theorem theorem8_3_bsDimension : Theorem8_3_bsDimension.{u} := by
  intro X _ _ _ _ x T u A μ _ hT hu hA y hy hb
  let P := toPresentation x hA.presentation.1
  have hA' : PointToSet.IsMeasureAdmissible P T μ A := (isAdmissible_iff P T μ).1 hA
  have hy' : y ∈ PointToSet.randomPoints P A μ := by
    rw [← mlRandom_eq]
    exact hy
  have h := PointToSet.pointwiseBSDimension_eq_localBSDimension P T hT u hu A μ hA' hy' hb
  have e1 : lowerPointwiseBSDimension x T u A y = _ := lowerPointwiseBSDimension_eq P T u A y
  have e2 : upperPointwiseBSDimension x T u A y = _ := upperPointwiseBSDimension_eq P T u A y
  rw [e1, e2, lowerLocalBSDimension_eq, upperLocalBSDimension_eq, h]
  exact ⟨rfl, rfl⟩

/-- [N, Corollary 8.4(c)], pressure, from `lowerPressure_eq_iInf_measure`,
`exists_atomic_measure_lowerPressure_eq` and their upper versions. -/
theorem corollary8_4_pressure : Corollary8_4_pressure.{u} := by
  intro X _ _ _ _ _ _ T φ hT hφ Z hZ
  obtain ⟨x, hx⟩ := TopologicalSpace.exists_dense_seq X
  let D := toPressureData (toPresentation x hx) T hT φ hφ
  have hl : ∀ μ : Measure X, IsProbabilityMeasure μ →
      ⨆ y ∈ Z, lowerLocalPressure μ T φ y = ⨆ y ∈ Z, (PointToSet.localPressure μ T φ y).1 :=
    fun μ _ ↦ iSup_congr fun y ↦ iSup_congr fun _ ↦ lowerLocalPressure_eq μ T φ y
  have hu : ∀ μ : Measure X, IsProbabilityMeasure μ →
      ⨆ y ∈ Z, upperLocalPressure μ T φ y = ⨆ y ∈ Z, (PointToSet.localPressure μ T φ y).2 :=
    fun μ _ ↦ iSup_congr fun y ↦ iSup_congr fun _ ↦ upperLocalPressure_eq μ T φ y
  refine ⟨?_, ?_, ?_, ?_⟩
  · have h : PointToSet.lowerPressure T φ D.p₀ Z = ⨅ (μ : Measure X) (_ : IsProbabilityMeasure μ),
        ⨆ y ∈ Z, (PointToSet.localPressure μ T φ y).1 :=
      PointToSet.lowerPressure_eq_iInf_measure D hZ
    rw [lowerPressure_eq T φ D.p₀, h]
    exact iInf_congr fun μ ↦ iInf_congr fun hμ ↦ (hl μ hμ).symm
  · obtain ⟨μ, hμ, hS, h⟩ := PointToSet.exists_atomic_measure_lowerPressure_eq D hZ
    have h' : PointToSet.lowerPressure T φ D.p₀ Z =
        ⨆ y ∈ Z, (PointToSet.localPressure μ T φ y).1 := h
    exact ⟨μ, hμ, hS, by rw [lowerPressure_eq T φ D.p₀, h', hl μ hμ]⟩
  · have h : PointToSet.upperPressure T φ D.p₀ Z = ⨅ (μ : Measure X) (_ : IsProbabilityMeasure μ),
        ⨆ y ∈ Z, (PointToSet.localPressure μ T φ y).2 :=
      PointToSet.upperPressure_eq_iInf_measure D hZ
    rw [upperPressure_eq T φ D.p₀, h]
    exact iInf_congr fun μ ↦ iInf_congr fun hμ ↦ (hu μ hμ).symm
  · obtain ⟨μ, hμ, hS, h⟩ := PointToSet.exists_atomic_measure_upperPressure_eq D hZ
    have h' : PointToSet.upperPressure T φ D.p₀ Z =
        ⨆ y ∈ Z, (PointToSet.localPressure μ T φ y).2 := h
    exact ⟨μ, hμ, hS, by rw [upperPressure_eq T φ D.p₀, h', hu μ hμ]⟩

/-- [N, Corollary 8.4(c)], BS dimension, from `lowerBSDimension_eq_iInf_measure`,
`exists_atomic_measure_lowerBSDimension_eq` and their upper versions. -/
theorem corollary8_4_bsDimension : Corollary8_4_bsDimension.{u} := by
  intro X _ _ _ _ _ _ T u hT hu Z hZ
  obtain ⟨x, hx⟩ := TopologicalSpace.exists_dense_seq X
  let P := toPresentation x hx
  have hl : ∀ μ : Measure X, ⨆ y ∈ Z, lowerLocalBSDimension μ T u y =
      ⨆ y ∈ Z, (PointToSet.localBSDimension μ T u y).1 :=
    fun μ ↦ iSup_congr fun y ↦ iSup_congr fun _ ↦ lowerLocalBSDimension_eq μ T u y
  have hu' : ∀ μ : Measure X, ⨆ y ∈ Z, upperLocalBSDimension μ T u y =
      ⨆ y ∈ Z, (PointToSet.localBSDimension μ T u y).2 :=
    fun μ ↦ iSup_congr fun y ↦ iSup_congr fun _ ↦ upperLocalBSDimension_eq μ T u y
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [lowerBSDimension_eq, PointToSet.lowerBSDimension_eq_iInf_measure P T hT u hu hZ]
    exact iInf_congr fun μ ↦ iInf_congr fun _ ↦ (hl μ).symm
  · obtain ⟨μ, hμ, hS, h⟩ := PointToSet.exists_atomic_measure_lowerBSDimension_eq P T hT u hu hZ
    exact ⟨μ, hμ, hS, by rw [lowerBSDimension_eq, h, hl μ]⟩
  · rw [upperBSDimension_eq, PointToSet.upperBSDimension_eq_iInf_measure P T hT u hu hZ]
    exact iInf_congr fun μ ↦ iInf_congr fun _ ↦ (hu' μ).symm
  · obtain ⟨μ, hμ, hS, h⟩ := PointToSet.exists_atomic_measure_upperBSDimension_eq P T hT u hu hZ
    exact ⟨μ, hμ, hS, by rw [upperBSDimension_eq, h, hu' μ]⟩

end Kolmogorov.Trusted
