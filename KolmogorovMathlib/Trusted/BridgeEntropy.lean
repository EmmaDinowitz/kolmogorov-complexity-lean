/-
Copyright (c) 2026 Emma Dinowitz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emma Dinowitz
-/
import KolmogorovMathlib.Trusted.StatementsEntropy
import KolmogorovMathlib.Trusted.Bridge
import KolmogorovMathlib.PointToSet.Pressure.Lower.EntropyPointToSet
import KolmogorovMathlib.PointToSet.Pressure.Upper.PointToSetPrinciple
import KolmogorovMathlib.PointToSet.PackingEquivalences.Pressure.Equivalence
import KolmogorovMathlib.PointToSet.Measure.EntropyLaw
import KolmogorovMathlib.PointToSet.Measure.EssentialBounds
import KolmogorovMathlib.PointToSet.Measure.Variational
import KolmogorovMathlib.PointToSet.Measure.VariationalPacking

/-!
# Bridge: the trusted statements on entropies of sets follow from the library

Proofs of the statements of `KolmogorovMathlib.Trusted.StatementsEntropy`, through equivalences
between the plain definitions and the library's:

* `bowenEntropy_eq`: `bowenEntropy T Z = PointToSet.lowerEntropy T Z`, unconditionally (the
  library takes radii `2⁻ᵖ` and order cutoffs `N ≥ 1`; the critical value is antitone in the
  radius and the content monotone in the cutoff);
* `packingEntropy_coe`: for nonempty `Z`, `packingEntropy T Z` is the library's zero-potential
  packing pressure `PointToSet.packingPressure T 0 Z` (an `EReal`, a `limsup` as `r → 0⁺` of
  critical values over all real exponents, with packing pieces inside `Z`);
* `packingEntropy_eq`: `packingEntropy T Z = PointToSet.upperEntropy P T Z` for continuous `T`,
  from `packingEntropy_coe` and the library's `pressureEquivalence_upper` and
  `entropy_eq_zeroPotentialPressure_of_nonempty_upper` (both sides are `0` for `Z = ∅`);
* `lowerMeasureEntropy_eq`, `upperMeasureEntropy_eq`, `entropyLaw_eq`: `measureEntropy` and
  `entropyLaw`, unconditionally.

The statements are then transported along these and the pilot bridge's lemmas for a dense
sequence `x` and its presentation `toPresentation x hx`.
-/

namespace Kolmogorov.Trusted

open MeasureTheory Filter Set
open scoped ENNReal Computability Topology

universe u

/-! ### Bowen entropy -/

section Bowen

variable {X : Type*} [MetricSpace X]

/-- Bowen balls grow with the radius. -/
private theorem bowenBall_mono_radius (T : X → X) (n : ℕ) (y : X) {ε ε' : ℝ} (h : ε ≤ ε') :
    bowenBall T n y ε ⊆ bowenBall T n y ε' :=
  fun _ hz k hk ↦ (hz k hk).trans_le h

/-- For the zero potential, the library's cost of a cover is the plain cost `Σⱼ 2^{-s nⱼ}`. -/
private theorem bowenCoverCost_zero (T : X → X) (s r : ℝ) (C : PointToSet.BowenCoverFamily X) :
    PointToSet.bowenCoverCost T (fun _ ↦ 0) .centered s r C =
      ∑' j, (2 : ℝ≥0∞) ^ (-s * C.order j) := by
  simp [PointToSet.bowenCoverCost, PointToSet.pressureBallWeight, birkhoffSum]

/-- At cutoffs `N ≥ 1` the plain Bowen content is the library's `lowerContent`. -/
theorem bowenContent_eq (T : X → X) (Z : Set X) (s ε : ℝ) {N : ℕ} (hN : 1 ≤ N) :
    bowenContent T Z s ε N = PointToSet.lowerContent T (fun _ ↦ 0) .centered Z s ε N := by
  refine le_antisymm (le_iInf₂ fun C hC ↦ ?_) (le_iInf fun J ↦ le_iInf fun y ↦ le_iInf
    fun n ↦ le_iInf fun h ↦ ?_)
  · refine iInf_le_of_le C.index (iInf_le_of_le C.center (iInf_le_of_le C.order
      (iInf_le_of_le ⟨fun j ↦ (le_max_right 1 N).trans (hC.1 j), ?_⟩
        (bowenCoverCost_zero T s ε C).ge)))
    simpa only [bowenBall_eq] using hC.2
  · refine iInf₂_le_of_le ⟨J, y, n⟩ ⟨fun j ↦ max_le (hN.trans (h.1 j)) (h.1 j), ?_⟩
      (bowenCoverCost_zero T s ε ⟨J, y, n⟩).le
    simpa only [bowenBall_eq] using h.2

/-- The plain Bowen content is monotone in the order cutoff. -/
theorem bowenContent_mono (T : X → X) (Z : Set X) (s ε : ℝ) {N N' : ℕ} (h : N ≤ N') :
    bowenContent T Z s ε N ≤ bowenContent T Z s ε N' :=
  iInf_mono fun _ ↦ iInf_mono fun _ ↦ iInf_mono fun _ ↦ iInf_mono' fun hc ↦
    ⟨⟨fun j ↦ h.trans (hc.1 j), hc.2⟩, le_rfl⟩

/-- The plain Bowen content is antitone in the radius. -/
theorem bowenContent_anti (T : X → X) (Z : Set X) (s : ℝ) {ε ε' : ℝ} (h : ε ≤ ε') (N : ℕ) :
    bowenContent T Z s ε' N ≤ bowenContent T Z s ε N :=
  iInf_mono fun _ ↦ iInf_mono fun _ ↦ iInf_mono fun _ ↦ iInf_mono' fun hc ↦
    ⟨⟨hc.1, hc.2.trans (iUnion_mono fun _ ↦ bowenBall_mono_radius T _ _ h)⟩, le_rfl⟩

/-- The limit `N → ∞` of the plain Bowen content is the library's `lowerContentLimit`. -/
theorem iSup_bowenContent_eq (T : X → X) (Z : Set X) (s ε : ℝ) :
    ⨆ N, bowenContent T Z s ε N = PointToSet.lowerContentLimit T (fun _ ↦ 0) .centered Z s ε := by
  refine le_antisymm (iSup_le fun N ↦ ?_) (iSup₂_le fun N hN ↦ ?_)
  · refine (bowenContent_mono T Z s ε (le_max_left N 1)).trans ?_
    rw [bowenContent_eq T Z s ε (le_max_right N 1)]
    exact le_iSup₂_of_le (max N 1) (le_max_right N 1) le_rfl
  · rw [← bowenContent_eq T Z s ε hN]
    exact le_iSup (fun N ↦ bowenContent T Z s ε N) N

/-- The plain critical value at radius `ε`. -/
private noncomputable def bowenCritical (T : X → X) (Z : Set X) (ε : ℝ) : ℝ≥0∞ :=
  ⨅ (s : ℝ) (_ : 0 ≤ s) (_ : ⨆ N, bowenContent T Z s ε N = 0), ENNReal.ofReal s

/-- The critical value is antitone in the radius. -/
private theorem bowenCritical_anti (T : X → X) (Z : Set X) {ε ε' : ℝ} (h : ε ≤ ε') :
    bowenCritical T Z ε' ≤ bowenCritical T Z ε :=
  iInf_mono fun s ↦ iInf_mono fun _ ↦ iInf_mono' fun hs ↦
    ⟨nonpos_iff_eq_zero.1 ((iSup_mono fun N ↦ bowenContent_anti T Z s h N).trans hs.le), le_rfl⟩

/-- Every positive radius is above some dyadic radius. -/
private theorem exists_dyadicRadius_le {ε : ℝ} (hε : 0 < ε) :
    ∃ p, PointToSet.dyadicRadius p ≤ ε := by
  obtain ⟨p, hp⟩ := exists_pow_lt_of_lt_one hε (by norm_num : (2 : ℝ)⁻¹ < 1)
  exact ⟨p, hp.le⟩

/-- The plain Bowen entropy is the library's `lowerEntropy`. -/
theorem bowenEntropy_eq (T : X → X) (Z : Set X) :
    bowenEntropy T Z = PointToSet.lowerEntropy T Z := by
  have hc : ∀ ε, bowenCritical T Z ε = ⨅ (s : ℝ) (_ : 0 ≤ s)
      (_ : PointToSet.lowerContentLimit T (fun _ ↦ 0) .centered Z s ε = 0), ENNReal.ofReal s :=
    fun ε ↦ by simp only [bowenCritical, iSup_bowenContent_eq]
  change ⨆ (ε : ℝ) (_ : 0 < ε), bowenCritical T Z ε = _
  simp only [PointToSet.lowerEntropy, ← hc]
  refine le_antisymm (iSup₂_le fun ε hε ↦ ?_) (iSup_le fun p ↦ ?_)
  · obtain ⟨p, hp⟩ := exists_dyadicRadius_le hε
    exact (bowenCritical_anti T Z hp).trans (le_iSup (fun p ↦ bowenCritical T Z _) p)
  · exact le_iSup₂_of_le (PointToSet.dyadicRadius p) (PointToSet.dyadicRadius_pos p) le_rfl

end Bowen

/-! ### Packing entropy -/

section Packing

variable {X : Type*} [MetricSpace X]

/-- The packing condition of the plain definition. -/
private def IsPacking (T : X → X) (Z : Set X) (ε : ℝ) (N : ℕ) (F : Set (X × ℕ)) : Prop :=
  F.Countable ∧ (∀ a ∈ F, a.1 ∈ Z ∧ N ≤ a.2) ∧
    F.Pairwise fun a b ↦ Disjoint (bowenBall T a.2 a.1 ε) (bowenBall T b.2 b.1 ε)

/-- The plain packing content, written with `IsPacking`. -/
private theorem packingContent_def (T : X → X) (Z : Set X) (s ε : ℝ) (N : ℕ) :
    packingContent T Z s ε N =
      ⨆ (F : Set (X × ℕ)) (_ : IsPacking T Z ε N F), ∑' a : F, (2 : ℝ≥0∞) ^ (-s * a.1.2) :=
  rfl

/-- For the zero potential and a positive radius, the library's supremum weight is `1`. -/
private theorem pressureBallWeight_zero {T : X → X} (n : ℕ) (y : X) {r : ℝ} (hr : 0 < r) :
    PointToSet.pressureBallWeight T (fun _ ↦ 0) .supremum n y r = 1 := by
  simp only [PointToSet.pressureBallWeight, birkhoffSum, Finset.sum_const_zero,
    ENNReal.rpow_zero]
  exact biSup_const ⟨y, PointToSet.self_mem_bowenBall T n y r hr⟩

/-- At a positive radius and cutoffs `N ≥ 1` the plain packing content is the library's. -/
theorem packingContent_eq (T : X → X) (Z : Set X) (s : ℝ) {r : ℝ} (hr : 0 < r) {N : ℕ}
    (hN : 1 ≤ N) :
    packingContent T Z s r N = PointToSet.packingPressureContent T (fun _ ↦ 0) Z s r N := by
  have hiff : ∀ F, IsPacking T Z r N F ↔ PointToSet.IsBowenPacking T Z r N F := fun F ↦ by
    simp only [IsPacking, PointToSet.IsBowenPacking, bowenBall_eq, max_eq_right hN]
  rw [packingContent_def, PointToSet.packingPressureContent]
  refine iSup_congr fun F ↦ iSup_congr_Prop (hiff F) fun _ ↦ ?_
  simp only [PointToSet.packingPressureSum, pressureBallWeight_zero _ _ hr, mul_one]

/-- The plain packing content is antitone in the order cutoff. -/
theorem packingContent_anti_cutoff (T : X → X) (Z : Set X) (s ε : ℝ) {N N' : ℕ}
    (h : N ≤ N') : packingContent T Z s ε N' ≤ packingContent T Z s ε N :=
  iSup_mono fun _ ↦ iSup_mono' fun hF ↦
    ⟨⟨hF.1, fun a ha ↦ ⟨(hF.2.1 a ha).1, h.trans (hF.2.1 a ha).2⟩, hF.2.2⟩, le_rfl⟩

/-- The plain packing content is monotone in the set. -/
theorem packingContent_mono_set (T : X → X) {Y Z : Set X} (hYZ : Y ⊆ Z) (s ε : ℝ) (N : ℕ) :
    packingContent T Y s ε N ≤ packingContent T Z s ε N :=
  iSup_mono fun _ ↦ iSup_mono' fun hF ↦
    ⟨⟨hF.1, fun a ha ↦ ⟨hYZ (hF.2.1 a ha).1, (hF.2.1 a ha).2⟩, hF.2.2⟩, le_rfl⟩

/-- The plain packing content is antitone in the radius. -/
theorem packingContent_anti_radius (T : X → X) (Z : Set X) (s : ℝ) {ε ε' : ℝ} (h : ε ≤ ε')
    (N : ℕ) : packingContent T Z s ε' N ≤ packingContent T Z s ε N :=
  iSup_mono fun _ ↦ iSup_mono' fun hF ↦
    ⟨⟨hF.1, hF.2.1, fun _ ha _ hb hab ↦ (hF.2.2 ha hb hab).mono
      (bowenBall_mono_radius T _ _ h) (bowenBall_mono_radius T _ _ h)⟩, le_rfl⟩

/-- At a positive radius the limit `N → ∞` of the plain packing content is the library's
`packingPressurePrecontent`. -/
theorem iInf_packingContent_eq (T : X → X) (Z : Set X) (s : ℝ) {r : ℝ} (hr : 0 < r) :
    ⨅ N, packingContent T Z s r N =
      PointToSet.packingPressurePrecontent T (fun _ ↦ 0) Z s r := by
  refine le_antisymm (le_iInf₂ fun N hN ↦ ?_) (le_iInf fun N ↦ ?_)
  · rw [← packingContent_eq T Z s hr hN]
    exact iInf_le (fun N ↦ packingContent T Z s r N) N
  · refine le_trans ?_ (packingContent_anti_cutoff T Z s r (le_max_left N 1))
    rw [packingContent_eq T Z s hr (le_max_right N 1)]
    exact iInf₂_le (max N 1) (le_max_right N 1)

/-- At a positive radius the plain packing measure is the library's `pressureOuterEnvelope`
(whose covering pieces lie in `Z`; intersecting the pieces with `Z` does not increase the
plain packing contents). -/
theorem packingMeasure_eq (T : X → X) (Z : Set X) (s : ℝ) {r : ℝ} (hr : 0 < r) :
    packingMeasure T Z s r = PointToSet.pressureOuterEnvelope T (fun _ ↦ 0) Z s r := by
  simp only [packingMeasure, PointToSet.pressureOuterEnvelope, ← iInf_packingContent_eq T _ s hr]
  refine le_antisymm (le_iInf₂ fun Y hY ↦ iInf₂_le_of_le Y hY.2 le_rfl)
    (le_iInf₂ fun Y hY ↦ ?_)
  refine iInf₂_le_of_le (fun j ↦ Y j ∩ Z) ⟨fun j ↦ inter_subset_right, fun z hz ↦ ?_⟩ ?_
  · obtain ⟨j, hj⟩ := mem_iUnion.1 (hY hz)
    exact mem_iUnion.2 ⟨j, hj, hz⟩
  · exact ENNReal.tsum_le_tsum fun j ↦ iInf_mono fun N ↦
      packingContent_mono_set T inter_subset_left s r N

/-- The plain packing measure is antitone in the radius. -/
theorem packingMeasure_anti_radius (T : X → X) (Z : Set X) (s : ℝ) {ε ε' : ℝ} (h : ε ≤ ε') :
    packingMeasure T Z s ε' ≤ packingMeasure T Z s ε :=
  iInf₂_mono fun _ _ ↦ ENNReal.tsum_le_tsum fun _ ↦ iInf_mono fun N ↦
    packingContent_anti_radius T _ s h N

/-- For nonempty `Z`, the packing measure at a negative exponent is at least `1`: a single ball
centered in a piece meeting `Z` is a packing. -/
theorem one_le_packingMeasure (T : X → X) {Z : Set X} (hZ : Z.Nonempty) {s : ℝ} (hs : s ≤ 0)
    (ε : ℝ) : 1 ≤ packingMeasure T Z s ε := by
  obtain ⟨z, hz⟩ := hZ
  refine le_iInf₂ fun Y hY ↦ ?_
  obtain ⟨j, hj⟩ := mem_iUnion.1 (hY hz)
  refine le_trans ?_ (ENNReal.le_tsum j)
  refine le_iInf fun N ↦ ?_
  have hF : IsPacking T (Y j) ε N {(z, N)} :=
    ⟨countable_singleton _, fun a ha ↦ by simp_all, pairwise_singleton _ _⟩
  refine le_trans ?_ (le_iSup₂_of_le (f := fun (F : Set (X × ℕ)) (_ : IsPacking T (Y j) ε N F) ↦
    ∑' a : F, (2 : ℝ≥0∞) ^ (-s * a.1.2)) {(z, N)} hF le_rfl)
  rw [tsum_singleton (f := fun a : X × ℕ ↦ (2 : ℝ≥0∞) ^ (-s * a.2))]
  have h1 := ENNReal.rpow_le_rpow_of_exponent_le (x := 2) (by norm_num)
    (mul_nonneg (neg_nonneg.2 hs) (Nat.cast_nonneg N))
  simpa using h1

/-- The plain critical value at radius `ε`. -/
private noncomputable def packingCritical (T : X → X) (Z : Set X) (ε : ℝ) : ℝ≥0∞ :=
  ⨅ (s : ℝ) (_ : 0 ≤ s) (_ : packingMeasure T Z s ε = 0), ENNReal.ofReal s

/-- The critical value is antitone in the radius. -/
private theorem packingCritical_anti (T : X → X) (Z : Set X) :
    Antitone (packingCritical T Z) := fun _ _ h ↦
  iInf_mono fun s ↦ iInf_mono fun _ ↦ iInf_mono' fun hs ↦
    ⟨nonpos_iff_eq_zero.1 ((packingMeasure_anti_radius T Z s h).trans hs.le), le_rfl⟩

/-- For nonempty `Z` and a positive radius, the plain critical value is the library's
`packingPressureAt` (an infimum over all real exponents, in `EReal`). -/
private theorem packingCritical_coe (T : X → X) {Z : Set X} (hZ : Z.Nonempty) {r : ℝ}
    (hr : 0 < r) :
    (packingCritical T Z r : EReal) = PointToSet.packingPressureAt T (fun _ ↦ 0) Z r := by
  simp only [packingCritical, PointToSet.packingPressureAt, EReal.coe_ennreal_iInf,
    ← packingMeasure_eq T Z _ hr]
  refine iInf_congr fun s ↦ ?_
  by_cases hs : 0 ≤ s
  · rw [iInf_pos hs]
    refine iInf_congr fun _ ↦ ?_
    rw [EReal.coe_ennreal_ofReal, max_eq_left hs]
  · have hne : packingMeasure T Z s r ≠ 0 :=
      (zero_lt_one.trans_le (one_le_packingMeasure T hZ (not_le.1 hs).le r)).ne'
    simp [hs, hne]

/-- The `limsup` as `r → 0⁺` of an antitone function is its supremum over `r > 0`. -/
private theorem limsup_nhdsGT_zero_of_antitone {f : ℝ → EReal} (hf : Antitone f) :
    limsup f (𝓝[>] 0) = ⨆ (r : ℝ) (_ : 0 < r), f r := by
  refine le_antisymm (limsup_le_of_le ?_ ?_) (iSup₂_le fun r hr ↦ ?_)
  · isBoundedDefault
  · filter_upwards [self_mem_nhdsWithin] with r hr
    exact le_iSup₂_of_le r hr le_rfl
  · refine le_trans ?_ liminf_le_limsup
    refine le_liminf_of_le ?_ ?_
    · isBoundedDefault
    · filter_upwards [Ioo_mem_nhdsGT hr] with t ht
      exact hf ht.2.le

/-- For nonempty `Z` the plain packing entropy is the library's zero-potential packing
pressure. -/
theorem packingEntropy_coe (T : X → X) {Z : Set X} (hZ : Z.Nonempty) :
    (packingEntropy T Z : EReal) = PointToSet.packingPressure T (fun _ ↦ 0) Z := by
  have h : PointToSet.packingPressure T (fun _ ↦ 0) Z =
      limsup (fun r ↦ (packingCritical T Z r : EReal)) (𝓝[>] 0) := by
    refine limsup_congr ?_
    filter_upwards [self_mem_nhdsWithin] with r hr
    exact (packingCritical_coe T hZ hr).symm
  rw [h, limsup_nhdsGT_zero_of_antitone fun _ _ hab ↦
      EReal.coe_ennreal_le_coe_ennreal_iff.2 (packingCritical_anti T Z hab)]
  exact EReal.coe_ennreal_biSup nonempty_Ioi (packingCritical T Z)

/-- The plain packing entropy of the empty set is `0`. -/
theorem packingEntropy_empty (T : X → X) : packingEntropy T (∅ : Set X) = 0 := by
  refine le_antisymm (iSup₂_le fun ε _ ↦ ?_) bot_le
  refine iInf_le_of_le 0 (iInf_le_of_le le_rfl (iInf_le_of_le ?_ (by simp)))
  refine le_antisymm (iInf₂_le_of_le (fun _ ↦ ∅) (empty_subset _) ?_) bot_le
  refine le_of_eq (ENNReal.tsum_eq_zero.2 fun _ ↦ le_antisymm ?_ bot_le)
  refine iInf_le_of_le 0 (iSup₂_le fun F hF ↦ ?_)
  have : F = ∅ := eq_empty_of_forall_notMem fun a ha ↦ (hF.2.1 a ha).1
  subst this
  simp

/-- For continuous `T` the plain packing entropy is the library's `upperEntropy` (for any
presentation `P`). -/
theorem packingEntropy_eq (P : PointToSet.Presentation X) {T : X → X} (hT : Continuous T)
    (Z : Set X) : packingEntropy T Z = PointToSet.upperEntropy P T Z := by
  rcases Z.eq_empty_or_nonempty with rfl | hZ
  · rw [packingEntropy_empty, PointToSet.entropiesAndOrbitComplexities_empty_upper]
  have : TopologicalSpace.SeparableSpace X := P.dense.separableSpace continuous_of_discreteTopology
  refine EReal.coe_ennreal_injective ?_
  rw [packingEntropy_coe T hZ, PointToSet.pressureEquivalence_upper T hT _ uniformContinuous_const,
    PointToSet.entropy_eq_zeroPotentialPressure_of_nonempty_upper P T hT Z hZ]

end Packing

/-! ### Feng–Huang entropies and the entropy law -/

section MeasureEntropy

variable {X : Type*} [MetricSpace X] [MeasurableSpace X]

/-- The plain lower local entropy, as a function, is the first coordinate of the library's. -/
private theorem lowerLocalEntropy_fun (μ : Measure X) (T : X → X) :
    lowerLocalEntropy μ T = fun y ↦ (PointToSet.localEntropy μ T y).1 :=
  funext (lowerLocalEntropy_eq μ T)

/-- The plain upper local entropy, as a function, is the second coordinate of the library's. -/
private theorem upperLocalEntropy_fun (μ : Measure X) (T : X → X) :
    upperLocalEntropy μ T = fun y ↦ (PointToSet.localEntropy μ T y).2 :=
  funext (upperLocalEntropy_eq μ T)

/-- The plain lower Feng–Huang entropy is the library's. -/
theorem lowerMeasureEntropy_eq (μ : Measure X) (T : X → X) :
    lowerMeasureEntropy μ T = (PointToSet.measureEntropy μ T).1 := by
  simp only [lowerMeasureEntropy, PointToSet.measureEntropy, lowerLocalEntropy_eq]

/-- The plain upper Feng–Huang entropy is the library's. -/
theorem upperMeasureEntropy_eq (μ : Measure X) (T : X → X) :
    upperMeasureEntropy μ T = (PointToSet.measureEntropy μ T).2 := by
  simp only [upperMeasureEntropy, PointToSet.measureEntropy, upperLocalEntropy_eq]

/-- The plain entropy law is the library's. -/
theorem entropyLaw_eq (μ : Measure X) (T : X → X) :
    entropyLaw μ T = PointToSet.entropyLaw μ T := by
  simp only [entropyLaw, PointToSet.entropyLaw, lowerLocalEntropy_eq, upperLocalEntropy_eq]

end MeasureEntropy

/-! ### Transport along a dense sequence -/

section Transport

variable {X : Type*} [MetricSpace X] [CompleteSpace X] {x : ℕ → X} (hx : DenseRange x)

/-- The plain lower orbit complexity relative to `x` is the library's, for the presentation
given by `x` and continuous `T`. -/
private theorem lowerOrbitComplexity_eq' {T : X → X} (hT : Continuous T) (A : Set ℕ) (y : X) :
    lowerOrbitComplexity x T A y =
      (PointToSet.orbitComplexities (toPresentation x hx) T A y).1 :=
  lowerOrbitComplexity_eq (toPresentation x hx) A hT y

/-- The plain upper orbit complexity relative to `x` is the library's, for continuous `T`. -/
private theorem upperOrbitComplexity_eq' {T : X → X} (hT : Continuous T) (A : Set ℕ) (y : X) :
    upperOrbitComplexity x T A y =
      (PointToSet.orbitComplexities (toPresentation x hx) T A y).2 :=
  upperOrbitComplexity_eq (toPresentation x hx) A hT y

variable [MeasurableSpace X]

/-- The plain random points relative to `x` are the library's. -/
private theorem mlRandom_eq' (A : Set ℕ) (μ : Measure X) :
    MLRandom x A μ = PointToSet.randomPoints (toPresentation x hx) A μ :=
  mlRandom_eq (toPresentation x hx) μ

/-- Plain admissibility relative to `x` is the library's. -/
private theorem isAdmissible_iff' (T : X → X) (μ : Measure X) (A : Set ℕ) :
    IsAdmissible x T μ A ↔ PointToSet.IsMeasureAdmissible (toPresentation x hx) T μ A :=
  isAdmissible_iff (toPresentation x hx) T μ

end Transport

/-! ### Theorem 2.1 -/

/-- [N, Theorem 2.1], Bowen entropy, from `entropy_effectiveCharacterization_allOracles_pointToSet`
and `entropy_effectiveCharacterization_allOracles_cone`. -/
theorem theorem2_1_lower : Theorem2_1_lower.{u} := by
  intro X _ _ x T hx hT Z
  simp only [bowenEntropy_eq, lowerOrbitComplexity_eq' hx hT]
  exact ⟨PointToSet.entropy_effectiveCharacterization_allOracles_pointToSet _ T hT Z,
    PointToSet.entropy_effectiveCharacterization_allOracles_cone _ T hT Z⟩

/-- [N, Theorem 2.1], packing entropy, from `upperEntropy_pointToSet` and
`upperEntropy_pointToSet_cone`. -/
theorem theorem2_1_upper : Theorem2_1_upper.{u} := by
  intro X _ _ x T hx hT Z
  simp only [packingEntropy_eq (toPresentation x hx) hT, upperOrbitComplexity_eq' hx hT]
  exact ⟨PointToSet.upperEntropy_pointToSet _ T hT Z,
    PointToSet.upperEntropy_pointToSet_cone _ T hT Z⟩

/-! ### The variational principle and Corollary 4.2 -/

/-- A nonempty compact metric space has a dense sequence. -/
private theorem exists_denseRange_of_compact {X : Type*} [MetricSpace X] [CompactSpace X]
    {K : Set X} (hne : K.Nonempty) : ∃ x : ℕ → X, DenseRange x := by
  have : Nonempty X := ⟨hne.some⟩
  exact TopologicalSpace.exists_dense_seq X

/-- The Feng–Huang variational principle, from `lowerEntropy_eq_iSup_measureEntropy` and
`upperEntropy_eq_iSup_measureEntropy`. -/
theorem variationalPrinciple : VariationalPrinciple.{u} := by
  intro X _ _ _ _ T K hT hK hne
  obtain ⟨x, hx⟩ := exists_denseRange_of_compact hne
  simp only [bowenEntropy_eq, packingEntropy_eq (toPresentation x hx) hT, lowerMeasureEntropy_eq,
    upperMeasureEntropy_eq]
  exact ⟨PointToSet.lowerEntropy_eq_iSup_measureEntropy (toPresentation x hx) hT hK hne,
    PointToSet.upperEntropy_eq_iSup_measureEntropy _ hT hK hne⟩

/-- The packing variational inequality, from `packingPressure_zero_le_iSup_measureEntropy`. -/
theorem packingVariationalInequality : PackingVariationalInequality.{u} := by
  intro X _ _ _ _ T K hT hK hne
  obtain ⟨x, hx⟩ := exists_denseRange_of_compact hne
  have h := PointToSet.packingPressure_zero_le_iSup_measureEntropy (toPresentation x hx) hT hK hne
  rw [← packingEntropy_coe T hne] at h
  simp only [upperMeasureEntropy_eq]
  exact EReal.coe_ennreal_le_coe_ennreal_iff.1 h

/-- [N, Corollary 4.2], from `iInf_iSup_orbitComplexities_eq_iSup_lintegral`. -/
theorem corollary4_2 : Corollary4_2.{u} := by
  intro X _ _ _ _ x T K Aμ hT hK hne hA
  have hx : DenseRange x := (hA (Measure.dirac hne.some) inferInstance).presentation.1
  have hA' : ∀ μ : Measure X, IsProbabilityMeasure μ →
      PointToSet.IsMeasureAdmissible (toPresentation x hx) T μ (Aμ μ) :=
    fun μ hμ ↦ (isAdmissible_iff' hx T μ (Aμ μ)).1 (hA μ hμ)
  simp only [lowerOrbitComplexity_eq' hx hT, upperOrbitComplexity_eq' hx hT]
  exact PointToSet.iInf_iSup_orbitComplexities_eq_iSup_lintegral _ hT hK hne Aμ hA'

/-! ### Theorem 4.3 -/

/-- [N, Theorem 4.3(a)], from `iSup_randomPoints_orbitComplexities_fst`,
`lowerEntropy_randomPoints` and `essSup_lowerLocalEntropy_eq_iInf_lowerEntropy`. -/
theorem theorem4_3_a : Theorem4_3_a.{u} := by
  intro X _ _ _ _ x T A μ _ hT hA
  have hx : DenseRange x := hA.presentation.1
  have hA' := (isAdmissible_iff' hx T μ A).1 hA
  simp only [lowerLocalEntropy_fun, lowerOrbitComplexity_eq' hx hT, mlRandom_eq' hx,
    bowenEntropy_eq]
  exact ⟨(PointToSet.iSup_randomPoints_orbitComplexities_fst _ T hT A μ hA').symm,
    (PointToSet.lowerEntropy_randomPoints _ T hT A μ hA').symm,
    PointToSet.essSup_lowerLocalEntropy_eq_iInf_lowerEntropy (toPresentation x hx) T hT μ⟩

/-- [N, Theorem 4.3(b)], from `essSup_upperLocalEntropy_le_iSup_randomPoints`,
`essSup_upperLocalEntropy_eq_iInf_oracle`, `exists_cone_iSup_randomPoints_snd` and
`essSup_upperLocalEntropy_eq_iInf_upperEntropy`. -/
theorem theorem4_3_b : Theorem4_3_b.{u} := by
  intro X _ _ _ _ x T μ _ hx hT
  simp only [upperLocalEntropy_fun, upperOrbitComplexity_eq' hx hT, mlRandom_eq' hx,
    isAdmissible_iff' hx, packingEntropy_eq (toPresentation x hx) hT]
  exact ⟨fun B hB ↦ PointToSet.essSup_upperLocalEntropy_le_iSup_randomPoints _ T hT B μ hB,
    PointToSet.essSup_upperLocalEntropy_eq_iInf_oracle _ T hT μ,
    PointToSet.exists_cone_iSup_randomPoints_snd _ T hT μ,
    PointToSet.essSup_upperLocalEntropy_eq_iInf_upperEntropy _ T hT μ⟩

/-- [N, Theorem 4.3(c)], from `iInf_randomPoints_orbitComplexities_le_essInf`,
`exists_cone_iInf_randomPoints`, `essInf_localEntropy_eq_iSup_oracle` and
`essInf_localEntropy_eq_iInf_entropy`. -/
theorem theorem4_3_c : Theorem4_3_c.{u} := by
  intro X _ _ _ _ x T μ _ hx hT
  simp only [lowerLocalEntropy_fun, upperLocalEntropy_fun, lowerOrbitComplexity_eq' hx hT,
    upperOrbitComplexity_eq' hx hT, mlRandom_eq' hx, isAdmissible_iff' hx, bowenEntropy_eq,
    packingEntropy_eq (toPresentation x hx) hT]
  exact ⟨fun B hB ↦ PointToSet.iInf_randomPoints_orbitComplexities_le_essInf _ T hT B μ hB,
    PointToSet.exists_cone_iInf_randomPoints _ T hT μ,
    PointToSet.essInf_localEntropy_eq_iSup_oracle _ T hT μ,
    PointToSet.essInf_localEntropy_eq_iInf_entropy _ T hT μ⟩

/-! ### Corollary 6.5 -/

/-- [N, Corollary 6.5(a)], from `measureEntropy_eq_lintegral_entropyLaw`. -/
theorem corollary6_5_a : Corollary6_5_a.{u} := by
  intro X _ _ _ T μ hT
  simp only [lowerMeasureEntropy_eq, upperMeasureEntropy_eq, entropyLaw_eq]
  exact PointToSet.measureEntropy_eq_lintegral_entropyLaw hT μ

/-- [N, Corollary 6.5(b)], from `essSup_localEntropy_eq_essSup_entropyLaw`. -/
theorem corollary6_5_b : Corollary6_5_b.{u} := by
  intro X _ _ _ T μ hT
  simp only [lowerLocalEntropy_fun, upperLocalEntropy_fun, entropyLaw_eq]
  obtain ⟨⟨h1, h2⟩, h3, h4⟩ := PointToSet.essSup_localEntropy_eq_essSup_entropyLaw hT μ
  exact ⟨h1, h2, h3, h4⟩

/-- [N, Corollary 6.5(c)], from `lowerEntropy_eq_iSup_essInf`,
`lowerEntropy_eq_iSup_measureEntropy`, `upperEntropy_eq_iSup_measureEntropy` and
`lowerEntropy_eq_iSup_essSup`. -/
theorem corollary6_5_c : Corollary6_5_c.{u} := by
  intro X _ _ _ _ T K hT hK hne
  obtain ⟨x, hx⟩ := exists_denseRange_of_compact hne
  let P := toPresentation x hx
  simp only [bowenEntropy_eq, packingEntropy_eq P hT, lowerLocalEntropy_fun,
    upperLocalEntropy_fun, lowerMeasureEntropy_eq, upperMeasureEntropy_eq]
  have h1 := PointToSet.lowerEntropy_eq_iSup_essInf P hT hK hne
  have h2 := PointToSet.lowerEntropy_eq_iSup_measureEntropy P hT hK hne
  have h3 := PointToSet.upperEntropy_eq_iSup_measureEntropy P hT hK hne
  have h4 := PointToSet.lowerEntropy_eq_iSup_essSup P hT hK hne
  exact ⟨⟨h1.1, h2, h4.1⟩, ⟨h1.2, h3, h4.2⟩⟩

end Kolmogorov.Trusted
