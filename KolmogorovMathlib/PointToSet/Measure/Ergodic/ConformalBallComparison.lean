/-
Copyright (c) 2026 Emma Dinowitz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emma Dinowitz
-/
import KolmogorovMathlib.PointToSet.Measure.RemarksRates

/-!
# Remark 8.5: local BS dimension and round-ball local dimension for conformal maps

For uniform conformal data `C` (local distance law `d(Tx, Ty) = 2 ^ ζ(x, y) d(x, y)`, potential
`u(x) = ζ(x, x)`), a measure `μ` and a point `x` of the conformal locus of Theorem E, the lower
local BS dimension `d̲_μ(x, T, u)` of `μ` is the lower round-ball local dimension
`liminf_{r → 0+} -log₂ μ(B(x, r)) / -log₂ r` (the step of Remark 8.5 of E. Dinowitz, *Entropy of
non-invariant measures and orbit complexity of random points*, marked as unchecked there).

The proof follows Theorem E (`pointwiseDimensionEqBS`), with the masses `-log₂ μ(·)` in place of
the complexities, and is simpler since the denominator `S_n u(x)` of the local BS rate is taken
at the centre:

* `ballInclusion` puts the Bowen ball `B_{n+1}(x, T, δ)` between the round balls of the orbit
  radii `r_n^- = η δ 2^{-S_n u(x) - nτ}` and `r_n^+ = δ 2^{-S_n u(x) + nτ}`, and
  `orbitScaleDenominators_bounds` (at the centre) gives
  `(1 - c)(-log₂ r_n^-) ≤ S_{n+1} u(x) ≤ (1 + c)(-log₂ r_n^+)`;
* `confBall_localDimension_fst_eq_liminf` (nonmonotone scale sampling,
  `nonmonotoneScaleSampling`, applied to the nondecreasing `t ↦ -log₂ μ(B(x, 2^{-t}))`) computes
  the round-ball lower local dimension along the radii `r_n^±`;
* the multiplicative error `1 ± c` is removed by letting the Bowen radius go to zero and then
  `c → 0`.

Neither randomness, nor admissibility of the oracle, nor `μ` being a probability measure is used:
the comparison holds for every measure (`confBall_localBSDimension_fst_eq_localDimension_fst`).
The statement of the leaf `localBSDimension_eq_localDimension_conformal` of
`Measure/RemarksRates.lean` is `localBSDimension_eq_localDimension_conformal`.

Blueprint node `meas:remarks`.
-/

namespace Kolmogorov.PointToSet

open Filter Set MeasureTheory
open scoped Topology ENNReal

section comparison

variable {X : Type*} [MetricSpace X] [MeasurableSpace X]

/-- Nonmonotone scale sampling for the round-ball lower local dimension: if the logarithmic
precisions `-log₂ (r n)` of positive radii tend to infinity with adjacent ratio tending to one,
the lower local dimension of `μ` at `x` is the lower limit of
`-log₂ μ(B(x, r n)) / -log₂ (r n)`. -/
theorem confBall_localDimension_fst_eq_liminf (μ : Measure X) (x : X) (r : ℕ → ℝ)
    (hpos : ∀ n, 0 < r n)
    (ht : Tendsto (fun n ↦ -Real.logb 2 (r n)) atTop atTop)
    (hratio : Tendsto (fun n ↦ (-Real.logb 2 (r (n + 1))) / (-Real.logb 2 (r n))) atTop (𝓝 1)) :
    (localDimension μ x).1 = liminf (fun n ↦ infoBits (μ (Metric.ball x (r n))) /
      ENNReal.ofReal (-Real.logb 2 (r n))) atTop := by
  let g : ℝ → ℝ≥0∞ := fun s ↦
    infoBits (μ (Metric.ball x s)) / ENNReal.ofReal (-Real.logb 2 s)
  let R : ℝ → ℝ := fun t ↦ (2 : ℝ) ^ (-t)
  let F : ℝ → ℝ≥0∞ := fun t ↦ infoBits (μ (Metric.ball x (R t)))
  have hRpos (t : ℝ) : 0 < R t := by dsimp [R]; positivity
  have hR : Tendsto R atTop (𝓝[>] (0 : ℝ)) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, Eventually.of_forall hRpos⟩
    exact (_root_.tendsto_rpow_atBot_of_base_gt_one 2 (by norm_num)).comp
      tendsto_neg_atTop_atBot
  have hprec : Tendsto (fun s : ℝ ↦ -Real.logb 2 s) (𝓝[>] 0) atTop :=
    tendsto_neg_atBot_atTop.comp (Real.tendsto_logb_nhdsGT_zero (by norm_num))
  have hRprec (s : ℝ) (hs : 0 < s) : R (-Real.logb 2 s) = s := by
    dsimp [R]
    rw [neg_neg, Real.rpow_logb (by norm_num) (by norm_num) hs]
  have hden (t : ℝ) : -Real.logb 2 (R t) = t := by
    dsimp [R]
    rw [Real.logb_rpow (by norm_num) (by norm_num), neg_neg]
  have hF : MonotoneOn F (Set.Ici 0) := by
    intro s _ t _ hst
    have hr : R t ≤ R s := Real.rpow_le_rpow_of_exponent_le (by norm_num) (neg_le_neg hst)
    exact infoBits_antitone (measure_mono (Metric.ball_subset_ball hr))
  have hnorm (t : ℝ) : F t / ENNReal.ofReal t = g (R t) := by
    simp only [g, F, hden]
  have hloc : (localDimension μ x).1 = liminf (fun t ↦ F t / ENNReal.ofReal t) atTop := by
    apply le_antisymm
    · have h := hR.liminf_le_liminf_comp (u := g)
      have heq : g ∘ R = fun t ↦ F t / ENNReal.ofReal t := funext fun t ↦ (hnorm t).symm
      rwa [heq] at h
    · have h := hprec.liminf_le_liminf_comp (u := fun t ↦ F t / ENNReal.ofReal t)
      have heq : ((fun t ↦ F t / ENNReal.ofReal t) ∘ (fun s : ℝ ↦ -Real.logb 2 s)) =ᶠ[𝓝[>] 0]
          g := by
        filter_upwards [self_mem_nhdsWithin] with s hs
        simp only [Function.comp_def, hnorm, hRprec s hs]
      rwa [liminf_congr heq] at h
  rw [hloc, nonmonotoneScaleSampling F 0 hF _ ht (ht.eventually (eventually_gt_atTop 0)) hratio]
  congr 1
  funext n
  rw [hnorm, hRprec _ (hpos n)]

/-- If the Bowen ball of order `n` lies in the round ball of radius `r` and
`S_n u(x) ≤ (1 + c)(-log₂ r)`, then the round-ball ratio at `r` is at most `1 + c` times the
local BS rate. -/
theorem confBall_ratio_le_mul_localBSRate (μ : Measure X) (T : X → X) (u : X → ℝ) (x : X)
    (n : ℕ) (δ r c : ℝ) (hc : 0 ≤ c) (hout : bowenBall T n x δ ⊆ Metric.ball x r)
    (hden : birkhoffSum T u n x ≤ (1 + c) * (-Real.logb 2 r)) :
    infoBits (μ (Metric.ball x r)) / ENNReal.ofReal (-Real.logb 2 r) ≤
      ENNReal.ofReal (1 + c) * localBSRate μ T u x n δ := by
  have hplus : 0 < 1 + c := by linarith
  have h0 : ENNReal.ofReal (1 + c) ≠ 0 := (ENNReal.ofReal_pos.2 hplus).ne'
  rw [localBSRate]
  calc infoBits (μ (Metric.ball x r)) / ENNReal.ofReal (-Real.logb 2 r)
      = ENNReal.ofReal (1 + c) * infoBits (μ (Metric.ball x r)) /
          (ENNReal.ofReal (1 + c) * ENNReal.ofReal (-Real.logb 2 r)) :=
        (ENNReal.mul_div_mul_left _ _ h0 ENNReal.ofReal_ne_top).symm
    _ ≤ ENNReal.ofReal (1 + c) * infoBits (μ (bowenBall T n x δ)) /
          (ENNReal.ofReal (1 + c) * ENNReal.ofReal (-Real.logb 2 r)) :=
        ENNReal.div_le_div_right
          (mul_le_mul' le_rfl (infoBits_antitone (measure_mono hout))) _
    _ = ENNReal.ofReal (1 + c) * infoBits (μ (bowenBall T n x δ)) /
          ENNReal.ofReal ((1 + c) * (-Real.logb 2 r)) := by
        rw [ENNReal.ofReal_mul hplus.le]
    _ ≤ ENNReal.ofReal (1 + c) * infoBits (μ (bowenBall T n x δ)) /
          ENNReal.ofReal (birkhoffSum T u n x) :=
        ENNReal.div_le_div_left (ENNReal.ofReal_le_ofReal hden) _
    _ = _ := mul_div_assoc _ _ _

/-- If the round ball of radius `r` lies in the Bowen ball of order `n` and
`(1 - c)(-log₂ r) ≤ S_n u(x)` with `c < 1`, then `1 - c` times the local BS rate is at most the
round-ball ratio at `r`. -/
theorem confBall_mul_localBSRate_le_ratio (μ : Measure X) (T : X → X) (u : X → ℝ) (x : X)
    (n : ℕ) (δ r c : ℝ) (hc1 : c < 1) (hin : Metric.ball x r ⊆ bowenBall T n x δ)
    (hden : (1 - c) * (-Real.logb 2 r) ≤ birkhoffSum T u n x) :
    ENNReal.ofReal (1 - c) * localBSRate μ T u x n δ ≤
      infoBits (μ (Metric.ball x r)) / ENNReal.ofReal (-Real.logb 2 r) := by
  have hminus : 0 < 1 - c := sub_pos.mpr hc1
  have h0 : ENNReal.ofReal (1 - c) ≠ 0 := (ENNReal.ofReal_pos.2 hminus).ne'
  rw [localBSRate]
  calc ENNReal.ofReal (1 - c) *
        (infoBits (μ (bowenBall T n x δ)) / ENNReal.ofReal (birkhoffSum T u n x))
      = ENNReal.ofReal (1 - c) * infoBits (μ (bowenBall T n x δ)) /
          ENNReal.ofReal (birkhoffSum T u n x) := (mul_div_assoc _ _ _).symm
    _ ≤ ENNReal.ofReal (1 - c) * infoBits (μ (Metric.ball x r)) /
          ENNReal.ofReal (birkhoffSum T u n x) :=
        ENNReal.div_le_div_right
          (mul_le_mul' le_rfl (infoBits_antitone (measure_mono hin))) _
    _ ≤ ENNReal.ofReal (1 - c) * infoBits (μ (Metric.ball x r)) /
          ENNReal.ofReal ((1 - c) * (-Real.logb 2 r)) :=
        ENNReal.div_le_div_left (ENNReal.ofReal_le_ofReal hden) _
    _ = ENNReal.ofReal (1 - c) * infoBits (μ (Metric.ball x r)) /
          (ENNReal.ofReal (1 - c) * ENNReal.ofReal (-Real.logb 2 r)) := by
        rw [ENNReal.ofReal_mul hminus.le]
    _ = _ := ENNReal.mul_div_mul_left _ _ h0 ENNReal.ofReal_ne_top

/-- Time-limit form of the squeeze: if the Bowen balls of order `n + 1` lie between the round
balls of radii `rlo n` and `rhi n`, with `S_{n+1} u(x)` squeezed by `1 ± c` times the logarithmic
precisions, and `d` is the lower limit of the round-ball ratios along both radius sequences, then
`d` is squeezed by `1 ± c` times the lower local BS dimension at the scale `δ`. -/
theorem confBall_squeeze_localBSDimensionAt (μ : Measure X) (T : X → X) (u : X → ℝ) (x : X)
    (δ c : ℝ) (hc : 0 ≤ c) (hc1 : c < 1) (rlo rhi : ℕ → ℝ) (d : ℝ≥0∞)
    (hslo : d = liminf (fun n ↦ infoBits (μ (Metric.ball x (rlo n))) /
      ENNReal.ofReal (-Real.logb 2 (rlo n))) atTop)
    (hshi : d = liminf (fun n ↦ infoBits (μ (Metric.ball x (rhi n))) /
      ENNReal.ofReal (-Real.logb 2 (rhi n))) atTop)
    (hballs : ∀ n, Metric.ball x (rlo n) ⊆ bowenBall T (n + 1) x δ ∧
      bowenBall T (n + 1) x δ ⊆ Metric.ball x (rhi n))
    (hden : ∀ᶠ n in atTop,
      (1 - c) * (-Real.logb 2 (rlo n)) ≤ birkhoffSum T u (n + 1) x ∧
      birkhoffSum T u (n + 1) x ≤ (1 + c) * (-Real.logb 2 (rhi n))) :
    d ≤ ENNReal.ofReal (1 + c) * (localBSDimensionAt μ T u x δ).1 ∧
      ENNReal.ofReal (1 - c) * (localBSDimensionAt μ T u x δ).1 ≤ d := by
  have hevent : ∀ᶠ n in atTop,
      infoBits (μ (Metric.ball x (rhi n))) / ENNReal.ofReal (-Real.logb 2 (rhi n)) ≤
          ENNReal.ofReal (1 + c) * localBSRate μ T u x (n + 1) δ ∧
        ENNReal.ofReal (1 - c) * localBSRate μ T u x (n + 1) δ ≤
          infoBits (μ (Metric.ball x (rlo n))) / ENNReal.ofReal (-Real.logb 2 (rlo n)) := by
    filter_upwards [hden] with n hn
    exact ⟨confBall_ratio_le_mul_localBSRate μ T u x (n + 1) δ _ c hc (hballs n).2 hn.2,
      confBall_mul_localBSRate_le_ratio μ T u x (n + 1) δ _ c hc1 (hballs n).1 hn.1⟩
  have hshift : liminf (fun n ↦ localBSRate μ T u x (n + 1) δ) atTop =
      (localBSDimensionAt μ T u x δ).1 :=
    liminf_nat_add (fun n ↦ localBSRate μ T u x n δ) 1
  constructor
  · rw [hshi]
    have h := liminf_le_liminf (hevent.mono fun _ hn ↦ hn.1)
    rwa [ENNReal.liminf_const_mul_of_ne_top ENNReal.ofReal_ne_top, hshift] at h
  · rw [hslo]
    have h := liminf_le_liminf (hevent.mono fun _ hn ↦ hn.2)
    rwa [ENNReal.liminf_const_mul_of_ne_top ENNReal.ofReal_ne_top, hshift] at h

/-- The lower local BS dimension at the scale `2^{-p}` is nondecreasing in `p`. -/
theorem confBall_monotone_localBSDimensionAt (μ : Measure X) (T : X → X) (u : X → ℝ) (x : X) :
    Monotone (fun p ↦ (localBSDimensionAt μ T u x (dyadicRadius p)).1) :=
  fun _ _ hpq ↦ liminf_le_liminf (Eventually.of_forall fun _ ↦ ENNReal.div_le_div_right
    (infoBits_antitone (measure_mono (bowenBall_subset_of_le _ _ _ (dyadicRadius_antitone hpq))))
    _)

/-- Remark 8.5 (conformal maps), comparison of Bowen balls with round balls: for every measure
`μ` and every point `x` of the conformal locus of Theorem E, the lower local BS dimension of the
potential `u = C.potential` is the lower round-ball local dimension of `μ` at `x`. No
randomness, admissibility or normalisation of `μ` is needed. Blueprint node `meas:remarks`. -/
theorem confBall_localBSDimension_fst_eq_localDimension_fst (C : UniformConformalData X)
    (μ : Measure X) {x : X} (hx : x ∈ conformalLocus C) :
    (localBSDimension μ C.T C.potential x).1 = (localDimension μ x).1 := by
  have havg : x ∈ positiveFiniteAverageLocus C.T C.potential := hx.1.1
  have htemp : HasTemperedContraction C.T C.potential x := hx.1.2
  have hgrowth : HasSublinearOrbitGrowth C.T C.potential x := hx.2
  have hfinite : lowerBirkhoffAverage C.T C.potential x ≠ ⊤ :=
    ne_top_of_lt (havg.2.1.trans_lt havg.2.2)
  have hbot : lowerBirkhoffAverage C.T C.potential x ≠ ⊥ := ne_bot_of_gt havg.1
  let α := (lowerBirkhoffAverage C.T C.potential x).toReal
  have hα : lowerBirkhoffAverage C.T C.potential x = (α : EReal) :=
    (EReal.coe_toReal hfinite hbot).symm
  have hαpos : 0 < α := EReal.coe_pos.mp (hα ▸ havg.1)
  have hbs : (localBSDimension μ C.T C.potential x).1 =
      ⨆ p, (localBSDimensionAt μ C.T C.potential x (dyadicRadius p)).1 := rfl
  rw [hbs]
  refine (eq_of_forall_mul_ofReal_squeeze _ _ fun c hc hc1 ↦ ?_).symm
  obtain ⟨τ, η, δ₀, hτ, hτα, hη, hηone, hδ₀, hspec⟩ :=
    exists_orbit_scale_parameters C x htemp α c hαpos hc hc1
  refine squeeze_iSup_of_monotone _
    (confBall_monotone_localBSDimensionAt μ C.T C.potential x) _ c ?_
  have hd : Tendsto dyadicRadius atTop (𝓝 (0 : ℝ)) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  filter_upwards [hd.eventually (gt_mem_nhds hδ₀)] with p hp
  have hδ : 0 < dyadicRadius p := by unfold dyadicRadius; positivity
  obtain ⟨hvar, herror, hballs⟩ := hspec (dyadicRadius p) hδ hp
  have hrpos (side : LimitSide) (n : ℕ) :
      0 < conformalOrbitRadius C side x η (dyadicRadius p) τ n := by
    cases side <;> dsimp [conformalOrbitRadius, LimitSide.choose] <;> positivity
  have ht (side : LimitSide) := orbitScaleDenominators C x α τ η (dyadicRadius p)
    hα hτ hτα hη hδ side
  have hpos (side : LimitSide) :
      ∀ᶠ n in atTop, 0 < conformalOrbitPrecision C side x η (dyadicRadius p) τ n :=
    (ht side).eventually (eventually_gt_atTop 0)
  have hsample (side : LimitSide) := confBall_localDimension_fst_eq_liminf μ x
    (conformalOrbitRadius C side x η (dyadicRadius p) τ) (hrpos side) (ht side)
    (orbitScaleDenominators_ratio C x hgrowth α τ η (dyadicRadius p)
      hα hτ hτα hη hδ side)
  refine confBall_squeeze_localBSDimensionAt μ C.T C.potential x (dyadicRadius p) c hc.le hc1
    (conformalOrbitRadius C .lower x η (dyadicRadius p) τ)
    (conformalOrbitRadius C .upper x η (dyadicRadius p) τ) _
    (hsample .lower) (hsample .upper) hballs ?_
  have hdb (side : LimitSide) := orbitScaleDenominators_bounds C x hgrowth α τ η
    (dyadicRadius p) hα hτ hη hδ hvar (α / 2) c (by linarith) (by linarith) herror side
  have hxx (n : ℕ) : x ∈ bowenBall C.T (n + 1) x (dyadicRadius p) :=
    mem_bowenBall_iff.2 fun k _ ↦ by simpa using hδ
  filter_upwards [hpos .lower, hpos .upper, hdb .lower, hdb .upper] with n hnlo hnhi hdlo hdhi
  exact ⟨(le_div_iff₀ hnlo).mp (hdlo x (hxx n)).1, (div_le_iff₀ hnhi).mp (hdhi x (hxx n)).2⟩

end comparison

section remark

variable {X : Type*} [MetricSpace X] [MeasurableSpace X]

/-- Remark 8.5 (conformal maps), second step (the statement of the leaf
`localBSDimension_eq_localDimension_conformal` of `Measure/RemarksRates.lean`): at a `μ`-random
point of the conformal locus, the lower local BS dimension `d̲_μ(x, T, u)` of the potential
`u = C.potential` is the lower round-ball local dimension of `μ` at `x`. The proof is the
comparison of Bowen balls with round balls,
`confBall_localBSDimension_fst_eq_localDimension_fst`; the presentation, the oracle, its
admissibility and the randomness of `x` are not used. Blueprint node `meas:remarks`. -/
theorem localBSDimension_eq_localDimension_conformal [BorelSpace X] (P : Presentation X)
    (C : UniformConformalData X) (A : Set ℕ) (μ : Measure X) [IsProbabilityMeasure μ]
    (_hA : IsMeasureAdmissible P C.T μ A) {x : X} (_hxr : x ∈ randomPoints P A μ)
    (hx : x ∈ conformalLocus C) :
    (localBSDimension μ C.T C.potential x).1 = (localDimension μ x).1 :=
  confBall_localBSDimension_fst_eq_localDimension_fst C μ hx

end remark

end Kolmogorov.PointToSet
