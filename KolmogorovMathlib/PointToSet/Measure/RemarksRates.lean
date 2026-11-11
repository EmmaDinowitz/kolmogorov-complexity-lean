/-
Copyright (c) 2026 Emma Dinowitz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emma Dinowitz
-/
import KolmogorovMathlib.PointToSet.Measure.ShiftBernoulli
import KolmogorovMathlib.PointToSet.Measure.ShiftProduct
import KolmogorovMathlib.PointToSet.Measure.PressurePointwise
import KolmogorovMathlib.PointToSet.Conformal.Defs
import KolmogorovMathlib.PointToSet.ComputableMetric.StaticDimensions

/-!
# Remarks 6.9, 6.17, 7.2 and 8.5

TODO module docstring.
-/

namespace Kolmogorov.PointToSet

open Filter Set MeasureTheory
open scoped Topology ENNReal NNReal Computability

/-! ### Remark 6.17: concavity and convexity of the information rates -/

section concavity

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

/-- Remark 6.17. -/
theorem informationRate_sum_eq (P : Presentation X) (T : X → X) (hT : Continuous T)
    {ι : Type*} [Countable ι] (t : ι → ℝ≥0∞) (μs : ι → Measure X)
    [∀ j, IsProbabilityMeasure (μs j)] (ht : ∑' j, t j = 1)
    (hH : ∑' j, t j * infoBits (t j) ≠ ⊤) :
    informationRate (Measure.sum fun j ↦ t j • μs j) T =
      (⨆ p : ℕ, liminf (fun n : ℕ ↦
          (∑' j, t j * bowenInformation (μs j) T n (dyadicRadius p)) / n) atTop,
        ⨆ p : ℕ, limsup (fun n : ℕ ↦
          (∑' j, t j * bowenInformation (μs j) T n (dyadicRadius p)) / n) atTop) := by
  set μ := Measure.sum fun j ↦ t j • μs j with hμ
  have : IsProbabilityMeasure μ := ⟨by
    rw [hμ, Measure.sum_apply _ MeasurableSet.univ]
    simp [ht]⟩
  set W : ℕ → ℕ → ℝ≥0∞ := fun p n ↦
    ∑' j, t j * bowenInformation (μs j) T n (dyadicRadius p) with hW
  set H := ∑' j, t j * infoBits (t j) with hHdef
  -- the mixture costs at most `H(t)` bits more than the average (Proposition 6.16(ii))
  have hup : ∀ p : ℕ,
      (informationRateAt μ T (dyadicRadius p)).1 ≤ liminf (fun n : ℕ ↦ W p n / n) atTop ∧
      (informationRateAt μ T (dyadicRadius p)).2 ≤ limsup (fun n : ℕ ↦ W p n / n) atTop := by
    intro p
    have hd : Tendsto (fun n : ℕ ↦ H / n) atTop (𝓝 0) := by
      have := ENNReal.Tendsto.const_mul ENNReal.tendsto_inv_nat_nhds_zero (Or.inr hH)
      simpa [div_eq_mul_inv] using this
    have h : ∀ᶠ n : ℕ in atTop,
        bowenInformation μ T n (dyadicRadius p) / n ≤ W p n / n + H / n :=
      Eventually.of_forall fun n ↦ by
        rw [← ENNReal.add_div]
        exact ENNReal.div_le_div_right (bowenInformation_sum_le t μs n _) _
    exact ⟨liminf_le_liminf_of_le_add_tendsto_zero h hd,
      limsup_le_limsup_of_le_add_tendsto_zero h hd⟩
  -- the average costs at most a logarithmic term more, at a finer scale
  -- (Proposition 6.16(iii), with an oracle admissible for the mixture)
  obtain ⟨C, hC⟩ := exists_measureAdmissible_base P T hT μ
  have hA := hC C (TuringReducible.refl _)
  have hlow : ∀ p : ℕ, liminf (fun n : ℕ ↦ W p n / n) atTop ≤ (informationRate μ T).1 ∧
      limsup (fun n : ℕ ↦ W p n / n) atTop ≤ (informationRate μ T).2 := by
    intro p
    set ε : ℚ := (2 : ℚ)⁻¹ ^ (p + 4) with hεdef
    have hε : 0 < ε := by positivity
    have hε' : (0 : ℝ) < ε := by exact_mod_cast hε
    have h12 : 12 * (ε : ℝ) ≤ dyadicRadius p := by
      have h0 : (0 : ℝ) ≤ (2 : ℝ)⁻¹ ^ p := by positivity
      rw [hεdef, dyadicRadius]
      push_cast
      rw [pow_add]
      norm_num
      linarith
    obtain ⟨c, hc⟩ := sum_bowenInformation_le P T hT C t μs ht hA ε hε
    have hle := liminf_limsup_le_of_forall_lt_ofReal
      (a := fun n : ℕ ↦ bowenInformation μ T n ε / n) (b := fun n : ℕ ↦ W p n / n) ?_
    · have h3 := informationRateAt_le_informationRate μ T hε'
      exact ⟨hle.1.trans h3.1, hle.2.trans h3.2⟩
    intro s hs
    refine ⟨fun n ↦ ENNReal.ofReal ((c + 2 * Real.logb 2 (s + 2) + 6 * Real.logb 2 n) / n),
      ?_, ?_⟩
    · rw [← ENNReal.ofReal_zero]
      exact ENNReal.tendsto_ofReal (tendsto_add_mul_logb_div_nat _ _)
    filter_upwards [eventually_ge_atTop 1] with n hn hlt
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    have hnE : (n : ℝ≥0∞) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
    set I := bowenInformation μ T n ε with hI
    have hlt' : I < ENNReal.ofReal (s * n) := by
      rw [ENNReal.div_lt_iff (Or.inl hnE) (Or.inl (ENNReal.natCast_ne_top n))] at hlt
      rwa [ENNReal.ofReal_mul hs.le, ENNReal.ofReal_natCast]
    have hItop : I ≠ ⊤ := (hlt'.trans ENNReal.ofReal_lt_top).ne
    have hIr : I.toReal < s * n := (ENNReal.lt_ofReal_iff_toReal_lt hItop).1 hlt'
    have hI0 : 0 ≤ I.toReal := ENNReal.toReal_nonneg
    have hL : 0 ≤ Real.logb 2 n := Real.logb_nonneg one_lt_two (by exact_mod_cast hn)
    have hlog : Real.logb 2 (I.toReal + 2) ≤ Real.logb 2 (s + 2) + Real.logb 2 n := by
      rw [← Real.logb_mul (by positivity) hn0.ne']
      refine Real.logb_le_logb_of_le one_lt_two (by positivity) ?_
      have : (1 : ℝ) ≤ n := by exact_mod_cast hn
      nlinarith
    have hlog0 : 0 ≤ Real.logb 2 (I.toReal + 2) := Real.logb_nonneg one_lt_two (by linarith)
    have hWle : W p n ≤ ∑' j, t j * bowenInformation (μs j) T n (12 * (ε : ℝ)) :=
      ENNReal.tsum_le_tsum fun j ↦ by
        gcongr
        exact bowenInformation_antitone _ _ _ h12
    have hE := hWle.trans (hc n hn)
    rw [← hI] at hE
    have hE' : W p n ≤
        ENNReal.ofReal (s * n + (c + 2 * Real.logb 2 (s + 2) + 6 * Real.logb 2 n)) := by
      have heq : I + ENNReal.ofReal (4 * Real.logb 2 n) +
          ENNReal.ofReal (2 * Real.logb 2 (I.toReal + 2)) + c = ENNReal.ofReal
            (I.toReal + 4 * Real.logb 2 n + 2 * Real.logb 2 (I.toReal + 2) + c) := by
        rw [ENNReal.ofReal_add (by linarith) (by positivity),
          ENNReal.ofReal_add (by linarith) (by linarith),
          ENNReal.ofReal_add hI0 (by linarith), ENNReal.ofReal_toReal hItop,
          ENNReal.ofReal_natCast]
      rw [heq] at hE
      refine hE.trans (ENNReal.ofReal_le_ofReal ?_)
      linarith
    calc W p n / n
        ≤ ENNReal.ofReal (s * n + (c + 2 * Real.logb 2 (s + 2) + 6 * Real.logb 2 n)) / n := by
          gcongr
      _ = ENNReal.ofReal (s + (c + 2 * Real.logb 2 (s + 2) + 6 * Real.logb 2 n) / n) := by
          rw [ofReal_div_natCast hn]
          congr 1
          field_simp
      _ ≤ _ := ENNReal.ofReal_add_le
  refine Prod.ext (le_antisymm ?_ ?_) (le_antisymm ?_ ?_)
  · exact iSup_le fun p ↦ (hup p).1.trans
      (le_iSup (fun q ↦ liminf (fun n : ℕ ↦ W q n / n) atTop) p)
  · exact iSup_le fun p ↦ (hlow p).1
  · exact iSup_le fun p ↦ (hup p).2.trans
      (le_iSup (fun q ↦ limsup (fun n : ℕ ↦ W q n / n) atTop) p)
  · exact iSup_le fun p ↦ (hlow p).2

/-- In `ℝ≥0∞` the lower limit is superadditive. -/
private theorem le_liminf_add' (u v : ℕ → ℝ≥0∞) :
    liminf u atTop + liminf v atTop ≤ liminf (fun n ↦ u n + v n) atTop := by
  simp only [liminf_eq_iSup_iInf_of_nat]
  have hm : ∀ w : ℕ → ℝ≥0∞, Monotone fun N : ℕ ↦ ⨅ i ≥ N, w i := fun w _ _ h ↦
    le_iInf₂ fun i hi ↦ iInf₂_le i (h.trans hi)
  rw [ENNReal.iSup_add_iSup_of_monotone (hm u) (hm v)]
  exact iSup_mono fun N ↦ le_iInf₂ fun i hi ↦ add_le_add (iInf₂_le i hi) (iInf₂_le i hi)

/-- In `ℝ≥0∞` the upper limit is subadditive. -/
private theorem limsup_add_le' (u v : ℕ → ℝ≥0∞) :
    limsup (fun n ↦ u n + v n) atTop ≤ limsup u atTop + limsup v atTop := by
  simp only [limsup_eq_iInf_iSup_of_nat]
  rw [ENNReal.iInf_add]
  refine le_iInf fun N ↦ ?_
  rw [ENNReal.add_iInf]
  refine le_iInf fun M ↦ (iInf_le _ (max N M)).trans ?_
  exact iSup₂_le fun i hi ↦ add_le_add (le_iSup₂_of_le i ((le_max_left _ _).trans hi) le_rfl)
    (le_iSup₂_of_le i ((le_max_right _ _).trans hi) le_rfl)

/-- The entropy `H(t) = ∑_j t_j (-log₂ t_j)` of a finite probability vector is finite. -/
theorem weightEntropy_ne_top {ι : Type*} [Fintype ι] (t : ι → ℝ≥0∞) (ht : ∑ j, t j = 1) :
    ∑' j, t j * infoBits (t j) ≠ ⊤ := by
  rw [tsum_fintype]
  refine ENNReal.sum_ne_top.2 fun j _ ↦ ?_
  have hle : t j ≤ 1 := ht ▸ Finset.single_le_sum (fun _ _ ↦ bot_le) (Finset.mem_univ j)
  rcases eq_or_ne (t j) 0 with h | h
  · simp [h]
  exact ENNReal.mul_ne_top (ne_top_of_le_ne_top ENNReal.one_ne_top hle) (infoBits_lt_top h).ne

/-- The weights `a t + (1 - a) t'` of a mixture of two probability vectors add up to one. -/
private theorem sum_mix_eq_one {ι : Type*} [Fintype ι] {t t' : ι → ℝ≥0∞} (ht : ∑ j, t j = 1)
    (ht' : ∑ j, t' j = 1) {a : ℝ≥0∞} (ha : a ≤ 1) :
    ∑' j, (a * t j + (1 - a) * t' j) = 1 := by
  rw [tsum_fintype, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ht, ht',
    mul_one, mul_one, add_tsub_cancel_of_le ha]

/-- The averaged mean information is affine in the weights. -/
private theorem tsum_mix_div {ι : Type*} (t t' : ι → ℝ≥0∞) (a : ℝ≥0∞) (B : ι → ℝ≥0∞)
    (n : ℕ) :
    (∑' j, (a * t j + (1 - a) * t' j) * B j) / n =
      a * ((∑' j, t j * B j) / n) + (1 - a) * ((∑' j, t' j * B j) / n) := by
  simp_rw [add_mul, mul_assoc]
  rw [ENNReal.tsum_add, ENNReal.tsum_mul_left, ENNReal.tsum_mul_left, ENNReal.add_div,
    mul_div_assoc, mul_div_assoc]

omit [BorelSpace X] in
/-- The averaged mean information at the scale `2^{-p}` increases with `p`. -/
private theorem monotone_tsum_bowenInformation {ι : Type*} (T : X → X) (s : ι → ℝ≥0∞)
    (μs : ι → Measure X) (n : ℕ) :
    Monotone fun p : ℕ ↦ (∑' j, s j * bowenInformation (μs j) T n (dyadicRadius p)) / n :=
  fun _ _ h ↦ ENNReal.div_le_div_right (ENNReal.tsum_le_tsum fun _ ↦
    by gcongr; exact bowenInformation_antitone _ _ _ (dyadicRadius_antitone h)) _

/-- Remark 6.17, concavity. -/
theorem informationRate_fst_concave (P : Presentation X) (T : X → X) (hT : Continuous T)
    {ι : Type*} [Fintype ι] (μs : ι → Measure X) [∀ j, IsProbabilityMeasure (μs j)]
    (t t' : ι → ℝ≥0∞) (ht : ∑ j, t j = 1) (ht' : ∑ j, t' j = 1) {a : ℝ≥0∞} (ha : a ≤ 1) :
    a * (informationRate (Measure.sum fun j ↦ t j • μs j) T).1 +
        (1 - a) * (informationRate (Measure.sum fun j ↦ t' j • μs j) T).1 ≤
      (informationRate (Measure.sum fun j ↦ (a * t j + (1 - a) * t' j) • μs j) T).1 := by
  have hsum : ∀ s : ι → ℝ≥0∞, ∑ j, s j = 1 → ∑' j, s j = 1 := fun s hs ↦ by
    rw [tsum_fintype]; exact hs
  have hmix := sum_mix_eq_one ht ht' ha
  have hmix' : ∑ j, (a * t j + (1 - a) * t' j) = 1 := by rwa [tsum_fintype] at hmix
  rw [informationRate_sum_eq P T hT t μs (hsum t ht) (weightEntropy_ne_top t ht),
    informationRate_sum_eq P T hT t' μs (hsum t' ht') (weightEntropy_ne_top t' ht'),
    informationRate_sum_eq P T hT _ μs hmix (weightEntropy_ne_top _ hmix')]
  dsimp only
  have ha' : a ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top ha
  have hb' : 1 - a ≠ ⊤ := ENNReal.sub_ne_top ENNReal.one_ne_top
  have hm : ∀ s : ι → ℝ≥0∞, Monotone fun p : ℕ ↦ liminf (fun n : ℕ ↦
      (∑' j, s j * bowenInformation (μs j) T n (dyadicRadius p)) / n) atTop := fun s _ _ h ↦
    liminf_le_liminf (Eventually.of_forall fun n ↦ monotone_tsum_bowenInformation T s μs n h)
  rw [ENNReal.mul_iSup, ENNReal.mul_iSup,
    ENNReal.iSup_add_iSup_of_monotone (fun _ _ h ↦ by gcongr; exact hm t h)
      (fun _ _ h ↦ by gcongr; exact hm t' h)]
  refine iSup_mono fun p ↦ ?_
  simp_rw [tsum_mix_div]
  rw [← ENNReal.liminf_const_mul_of_ne_top ha', ← ENNReal.liminf_const_mul_of_ne_top hb']
  exact le_liminf_add' _ _

/-- Remark 6.17, convexity. -/
theorem informationRate_snd_convex (P : Presentation X) (T : X → X) (hT : Continuous T)
    {ι : Type*} [Fintype ι] (μs : ι → Measure X) [∀ j, IsProbabilityMeasure (μs j)]
    (t t' : ι → ℝ≥0∞) (ht : ∑ j, t j = 1) (ht' : ∑ j, t' j = 1) {a : ℝ≥0∞} (ha : a ≤ 1) :
    (informationRate (Measure.sum fun j ↦ (a * t j + (1 - a) * t' j) • μs j) T).2 ≤
      a * (informationRate (Measure.sum fun j ↦ t j • μs j) T).2 +
        (1 - a) * (informationRate (Measure.sum fun j ↦ t' j • μs j) T).2 := by
  have hsum : ∀ s : ι → ℝ≥0∞, ∑ j, s j = 1 → ∑' j, s j = 1 := fun s hs ↦ by
    rw [tsum_fintype]; exact hs
  have hmix := sum_mix_eq_one ht ht' ha
  have hmix' : ∑ j, (a * t j + (1 - a) * t' j) = 1 := by rwa [tsum_fintype] at hmix
  rw [informationRate_sum_eq P T hT t μs (hsum t ht) (weightEntropy_ne_top t ht),
    informationRate_sum_eq P T hT t' μs (hsum t' ht') (weightEntropy_ne_top t' ht'),
    informationRate_sum_eq P T hT _ μs hmix (weightEntropy_ne_top _ hmix')]
  dsimp only
  refine iSup_le fun p ↦ ?_
  simp_rw [tsum_mix_div]
  refine (limsup_add_le' _ _).trans ?_
  rw [ENNReal.limsup_const_mul_of_ne_top (ne_top_of_le_ne_top ENNReal.one_ne_top ha),
    ENNReal.limsup_const_mul_of_ne_top (ENNReal.sub_ne_top ENNReal.one_ne_top)]
  gcongr
  · exact le_iSup (fun q ↦ limsup (fun n : ℕ ↦
      (∑' j, t j * bowenInformation (μs j) T n (dyadicRadius q)) / n) atTop) p
  · exact le_iSup (fun q ↦ limsup (fun n : ℕ ↦
      (∑' j, t' j * bowenInformation (μs j) T n (dyadicRadius q)) / n) atTop) p

end concavity

/-! ### Remark 6.9 -/

section supportFunction

attribute [local instance] cantorMetricSpace

/-- The normalized mean cylinder information. -/
noncomputable def cylinderInfoRate (ν : Measure (ℕ → Bool)) (n : ℕ) : ℝ :=
  ((∫⁻ x, infoBits (ν (PiNat.cylinder x n)) ∂ν) / n).toReal

/-- Remark 6.9, bounds. -/
theorem lintegral_infoBits_mixture_bounds {ι : Type*} [Fintype ι] (t : ι → ℝ≥0)
    (ht : ∑ j, t j = 1) (μs : ι → Measure (ℕ → Bool)) [∀ j, IsProbabilityMeasure (μs j)]
    (hpos : ∀ j x n, μs j (PiNat.cylinder x n) ≠ 0) (n : ℕ) :
    ∑ j, (t j : ℝ≥0∞) * ∫⁻ x, infoBits (μs j (PiNat.cylinder x n)) ∂μs j ≤
        ∫⁻ x, infoBits ((Measure.sum fun j ↦ (t j : ℝ≥0∞) • μs j) (PiNat.cylinder x n))
          ∂(Measure.sum fun j ↦ (t j : ℝ≥0∞) • μs j) ∧
      ∫⁻ x, infoBits ((Measure.sum fun j ↦ (t j : ℝ≥0∞) • μs j) (PiNat.cylinder x n))
          ∂(Measure.sum fun j ↦ (t j : ℝ≥0∞) • μs j) ≤
        ∑ j, (t j : ℝ≥0∞) * ∫⁻ x, infoBits (μs j (PiNat.cylinder x n)) ∂μs j +
          ∑ j, (t j : ℝ≥0∞) * infoBits (t j) := by
  sorry

/-- Remark 6.9, support function. -/
theorem informationRate_mixture_isLeast_isGreatest {ι : Type*} [Fintype ι] (t : ι → ℝ≥0)
    (ht : ∑ j, t j = 1) (μs : ι → Measure (ℕ → Bool)) [∀ j, IsProbabilityMeasure (μs j)]
    (hpos : ∀ j x n, μs j (PiNat.cylinder x n) ≠ 0) :
    (∃ m : ℝ, IsLeast ((fun c : ι → ℝ ↦ ∑ j, (t j : ℝ) * c j) ''
          {c | MapClusterPt c atTop fun n j ↦ cylinderInfoRate (μs j) n}) m ∧
        (informationRate (Measure.sum fun j ↦ (t j : ℝ≥0∞) • μs j) shiftMap).1 =
          ENNReal.ofReal m) ∧
      ∃ M : ℝ, IsGreatest ((fun c : ι → ℝ ↦ ∑ j, (t j : ℝ) * c j) ''
          {c | MapClusterPt c atTop fun n j ↦ cylinderInfoRate (μs j) n}) M ∧
        (informationRate (Measure.sum fun j ↦ (t j : ℝ≥0∞) • μs j) shiftMap).2 =
          ENNReal.ofReal M := by
  sorry

end supportFunction

end Kolmogorov.PointToSet
