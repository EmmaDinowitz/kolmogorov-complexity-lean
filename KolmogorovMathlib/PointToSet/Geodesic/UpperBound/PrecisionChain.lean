/-
Copyright (c) 2026 Emma Dinowitz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emma Dinowitz
-/
import KolmogorovMathlib.PointToSet.Geodesic.UpperBound.Returns
import KolmogorovMathlib.PointToSet.Geodesic.OrbitToLocation

/-!
# The orbit-to-location interface and the precision chain (Chapter I, part 2)

`OrbitToLocationEstimate G P A` is the conclusion of Chapter H for the oracle `A`: for every
regular `x`, all compact regular endpoint sets and every rational loss `ρ`, there is a time
shift `|t₀| ≤ aMax` such that the estimate of `orbit_to_location` holds at the shifted section
point `φ t₀ x` with constants independent of the durations. Chapter H discharges it above the
base oracle (`orbitToLocationEstimate_of_base`). The precision chain (`precision_chain`, node
`geo:precision-chain`) turns the estimate into a chain of dyadic precisions `δ p` at which the
precision complexity of the section point is bounded by the two orbit complexities at the
stopping times; the limit helpers `limsup_comp_le_of_tendsto_atTop`,
`liminf_nhdsWithin_le_liminf_seq` and `ennreal_limsup_add_le` serve both section-point bounds.

Conventions: `dim^A(x), Dim^A(x) = (staticPointDimensions P A x).1, .2`;
`dim^A_BS, Dim^A_BS = (pointwiseBSDimension P T u A x).1, .2`. All dimensions are `ℝ≥0∞`.
-/

namespace Kolmogorov.PointToSet

open Filter Set
open scoped Topology ENNReal Computability

variable {X : Type*} [MetricSpace X] [CompactSpace X]

/-! ### The interface to Chapter H -/

/-- The conclusion of `orbit_to_location` for the oracle `A`: for every regular `x`, all compact
regular endpoint sets and every rational loss there is a time shift `t₀` with `|t₀| ≤ aMax` (the
shifted section point `z = φ t₀ x` of the localization of `x` for these parameters) such that the
estimate holds with constants independent of the durations. The section point depends on the
parameters; the flow-coordinate step (`flow_coordinate`, `Dim x ≤ 1 + Dim z` for `|t₀| ≤ aMax`)
absorbs this variation before the limits are taken. Blueprint nodes `geo:orbit-to-location`,
`geo:precision-chain`. -/
def OrbitToLocationEstimate (G : GeodesicReconstructionData X) (P : Presentation X)
    (A : Set ℕ) : Prop :=
  ∀ x ∈ G.Reg, ∀ Pp Pm : Set X, IsCompact Pp → Pp ⊆ G.Reg → IsCompact Pm → Pm ⊆ G.Reg →
    ∀ ρ : ℚ, 0 < ρ → ∃ t₀ : ℝ, |t₀| ≤ G.aMax ∧
      ∃ ε : ℝ, 0 < ε ∧ ∃ C : ℝ, 1 < C ∧ ∃ c₀ : ℕ, ∀ Tp Tm : ℕ,
        G.φ (Tp : ℝ) x ∈ Pp → G.φ (-(Tm : ℝ)) x ∈ Pm →
        precisionComplexityNat P A (G.φ t₀ x) (C * G.combinedScale ρ Tp Tm x) ≤
          orbitComplexityNat P G.f A x (Tp + 1) ε + orbitComplexityNat P G.finv A x (Tm + 1) ε +
            oraclePairComplexity A Tp Tm + c₀

namespace EffectiveGeodesicData

variable {G : GeodesicReconstructionData X} {P : Presentation X} {B : Set ℕ}
  (E : EffectiveGeodesicData G P B)
include E

/-- Chapter H gives the interface above the base oracle: the plaque hypothesis of
`orbit_to_location` is discharged by `G.smallPlaques` (radius-indexed plaque families of
Chapter B). Blueprint nodes `geo:orbit-to-location`, `geo:bracket-approx` (`SmallPlaques`). -/
theorem orbitToLocationEstimate_of_base {A : Set ℕ} (hBA : charOracle B ≤ᵀ charOracle A) :
    OrbitToLocationEstimate G P A := by
  intro x hx Pp Pm hPp hPpR hPm hPmR ρ hρ
  obtain ⟨ε₀, -, Q, -, -, -, h⟩ := E.orbit_to_location hPp hPpR hPm hPmR ρ hρ
  exact h (G.smallPlaques Q ε₀) A hBA x hx

/-- The interface under the (now redundant) plaque hypothesis; kept for the blueprint node
names. -/
theorem orbitToLocationEstimate_of_smallPlaques
    (_hsmall : ∀ Q : Set X, IsCompact Q → Q ⊆ G.Reg → ∀ ε₀ : ℝ, 0 < ε₀ → G.SmallPlaques Q ε₀)
    {A : Set ℕ} (hBA : charOracle B ≤ᵀ charOracle A) :
    OrbitToLocationEstimate G P A :=
  E.orbitToLocationEstimate_of_base hBA


end EffectiveGeodesicData

section limits

variable {G : GeodesicReconstructionData X} (P : Presentation X) {A : Set ℕ}

/-! ### `geo:precision-chain` -/

/-- The scale sequence `δ p = a r ^ p` with `0 < r < 1` has logarithmic ratios tending to one. -/
lemma tendsto_log_geometric_ratio {a r : ℝ} (ha : 0 < a) (hr0 : 0 < r) (hr1 : r < 1) :
    Tendsto (fun p : ℕ ↦ Real.log (a * r ^ (p + 1)) / Real.log (a * r ^ p)) atTop (𝓝 1) := by
  have hlr : Real.log r < 0 := Real.log_neg hr0 hr1
  have hlog : ∀ p : ℕ, Real.log (a * r ^ p) = Real.log a + p * Real.log r := fun p ↦ by
    rw [Real.log_mul ha.ne' (pow_ne_zero p hr0.ne'), Real.log_pow]
  have h1 : Tendsto (fun p : ℕ ↦ Real.log a / p + Real.log r + Real.log r / p) atTop
      (𝓝 (0 + Real.log r + 0)) :=
    ((tendsto_const_div_atTop_nhds_zero_nat _).add tendsto_const_nhds).add
      (tendsto_const_div_atTop_nhds_zero_nat _)
  have h2 : Tendsto (fun p : ℕ ↦ Real.log a / p + Real.log r) atTop (𝓝 (0 + Real.log r)) :=
    (tendsto_const_div_atTop_nhds_zero_nat _).add tendsto_const_nhds
  have h3 := h1.div h2 (by rw [zero_add]; exact hlr.ne)
  have h4 : (0 + Real.log r + 0) / (0 + Real.log r) = 1 := by
    rw [zero_add, add_zero, div_self hlr.ne]
  rw [h4] at h3
  refine h3.congr' ?_
  filter_upwards [eventually_ne_atTop 0] with p hp
  have hp' : (p : ℝ) ≠ 0 := by exact_mod_cast hp
  simp only [Pi.div_apply]
  rw [hlog, hlog]
  have e1 : Real.log a / p + Real.log r + Real.log r / p = (Real.log a + ((p + 1 : ℕ) : ℝ) *
      Real.log r) / p := by
    field_simp
    push_cast
    ring
  have e2 : Real.log a / p + Real.log r = (Real.log a + p * Real.log r) / p := by
    field_simp
  rw [e1, e2, div_div_div_cancel_right₀ hp']

/-- `precision_chain` under the additional hypothesis `θ = 2ρ(c-1)/λ̲ < 1`, which is needed for
`δ p → 0` (see the notes on `precision_chain`). -/
lemma precision_chain_aux (hA : OrbitToLocationEstimate G P A) {x : X}
    (hx : G.ControlledReturns x) (hpos : G.PositiveRates x) :
    ∃ lam : ℝ, 0 < lam ∧ ∃ N₀ : ℕ,
      ∀ c : ℝ, 1 < c → ∀ ρ : ℚ, 0 < ρ → (ρ : ℝ) < lam / 2 → 2 * (ρ : ℝ) * (c - 1) < lam →
        ∃ t₀ : ℝ, |t₀| ≤ G.aMax ∧
        ∃ ε : ℝ, 0 < ε ∧ ∃ Tp Tm : ℕ → ℕ, ∃ δ : ℕ → ℝ, ∃ c₀ : ℝ, ∃ p₀ : ℕ,
          (∀ p, 0 < δ p) ∧ Tendsto δ atTop (𝓝 0) ∧
          Tendsto (fun p ↦ Real.log (δ (p + 1)) / Real.log (δ p)) atTop (𝓝 1) ∧
          (∀ p, -Real.logb 2 (δ p) ≤ (1 - 2 * ρ * (c - 1) / lam) * p + c₀) ∧
          (∀ p, (1 - 2 * ρ * (c - 1) / lam) * p - c₀ ≤ -Real.logb 2 (δ p)) ∧
          Tendsto Tp atTop atTop ∧ Tendsto Tm atTop atTop ∧
          (∀ p, (Tp p : ℝ) ≤ c * (2 * p / lam + N₀ + 1) ∧
            (Tm p : ℝ) ≤ c * (2 * p / lam + N₀ + 1)) ∧
          (∀ p, birkhoffSum G.f G.uPlus (Tp p) x ≤ (1 + 2 * (ρ + G.Λ' * (c - 1)) / lam) * p + c₀) ∧
          (∀ p, birkhoffSum G.finv G.uMinus (Tm p) x ≤
            (1 + 2 * (ρ + G.Λ' * (c - 1)) / lam) * p + c₀) ∧
          ∀ p : ℕ, p₀ ≤ p →
            (precisionComplexityNat P A (G.φ t₀ x) (δ p) : ℝ) ≤
              orbitComplexityNat P G.f A x (Tp p + 1) ε +
                orbitComplexityNat P G.finv A x (Tm p + 1) ε +
                2 * Real.logb 2 ((Tp p : ℝ) + 1) + 2 * Real.logb 2 ((Tm p : ℝ) + 1) + c₀ := by
  have hest := hA x hx.mem_Reg
  obtain ⟨lam, hlam, N₀, hret⟩ := G.return_adjustment hx hpos
  obtain ⟨-, hu0, huM⟩ := G.uPlus_props
  obtain ⟨-, hv0, hvM⟩ := G.uMinus_props
  replace huM : ∀ y, G.uPlus y ≤ G.Λ' := huM
  replace hvM : ∀ y, G.uMinus y ≤ G.Λ' := hvM
  have hΛ0 : 0 ≤ G.Λ' := (hu0 x).trans (huM x)
  refine ⟨lam, hlam, N₀, fun c hc ρ hρ hρlam hθ ↦ ?_⟩
  obtain ⟨Pp, Pm, hPp, hPpR, hPm, hPmR, hret'⟩ := hret c hc
  have hρ' : (0 : ℝ) < ρ := by exact_mod_cast hρ
  obtain ⟨Tp, Tm, p₀, hTp, hTm, hbound, hest'⟩ := hret' ρ hρ' hρlam
  obtain ⟨t₀, ht₀, ε, hε, C, hC, c₀, hchain⟩ := hest Pp Pm hPp hPpR hPm hPmR ρ hρ
  obtain ⟨cpair, hpair⟩ := oraclePairComplexity_le_log A
  have hc1 : 0 ≤ c - 1 := by linarith
  have hθ1 : 0 < 1 - 2 * (ρ : ℝ) * (c - 1) / lam := by
    rw [sub_pos, div_lt_one hlam]; exact hθ
  have hκ₀ : 0 ≤ (ρ : ℝ) * (c - 1) * (N₀ + 1) := by positivity
  have hθ'0 : 0 ≤ 2 * ((ρ : ℝ) + G.Λ' * (c - 1)) / lam := by positivity
  -- the scale sequence
  set r : ℝ := (2 : ℝ) ^ (-(1 - 2 * (ρ : ℝ) * (c - 1) / lam)) with hr
  have hr0 : 0 < r := Real.rpow_pos_of_pos two_pos _
  have hr1 : r < 1 := Real.rpow_lt_one_of_one_lt_of_neg one_lt_two (by linarith)
  set a : ℝ := C * (2 : ℝ) ^ ((ρ : ℝ) * (c - 1) * (N₀ + 1)) with ha_def
  have ha : 0 < a := mul_pos (by linarith) (Real.rpow_pos_of_pos two_pos _)
  have hlogC : 0 < Real.logb 2 C := Real.logb_pos one_lt_two hC
  have hlogδ : ∀ p : ℕ, Real.logb 2 (a * r ^ p) = Real.logb 2 C + ρ * (c - 1) * (N₀ + 1) -
      (1 - 2 * ρ * (c - 1) / lam) * p := by
    intro p
    rw [Real.logb_mul ha.ne' (pow_ne_zero _ hr0.ne'), Real.logb_pow, hr, ha_def,
      Real.logb_mul (by linarith) (Real.rpow_pos_of_pos two_pos _).ne',
      Real.logb_rpow two_pos (by norm_num), Real.logb_rpow two_pos (by norm_num)]
    ring
  -- the constant
  set κ₁ : ℝ := ((ρ : ℝ) + G.Λ' * (c - 1)) * (N₀ + 1) + G.Λ' + ρ with hκ₁
  set c₀' : ℝ := max (max (Real.logb 2 C + ρ * (c - 1) * (N₀ + 1)) κ₁)
    (max (c₀ + cpair) (G.Λ' * (c * (2 * p₀ / lam + N₀ + 1)))) with hc₀'
  have hc₀'1 : Real.logb 2 C + ρ * (c - 1) * (N₀ + 1) ≤ c₀' :=
    (le_max_left _ _).trans (le_max_left _ _)
  have hc₀'2 : κ₁ ≤ c₀' := (le_max_right _ _).trans (le_max_left _ _)
  have hc₀'3 : c₀ + cpair ≤ c₀' := (le_max_left _ _).trans (le_max_right _ _)
  have hc₀'4 : G.Λ' * (c * (2 * p₀ / lam + N₀ + 1)) ≤ c₀' :=
    (le_max_right _ _).trans (le_max_right _ _)
  have hc₀'0 : 0 ≤ c₀' := by linarith
  -- bounds on Birkhoff sums below the threshold
  have hSlin : ∀ (T : X → X) (u : X → ℝ), (∀ y, 0 ≤ u y) → (∀ y, u y ≤ G.Λ') →
      ∀ (Tf : ℕ → ℕ), (∀ p, (Tf p : ℝ) ≤ c * (2 * p / lam + N₀ + 1)) → ∀ p, p < p₀ →
      birkhoffSum T u (Tf p) x ≤ (1 + 2 * (ρ + G.Λ' * (c - 1)) / lam) * p + c₀' := by
    intro T u hu0 huM Tf hTf p hp
    have h1 := (GeodesicReconstructionData.birkhoffSum_bounds_of_le (T := T) hu0 huM x
      (Nat.zero_le (Tf p))).2
    simp only [birkhoffSum_zero, Pi.zero_apply, Nat.sub_zero, zero_add] at h1
    have h2 : (p : ℝ) ≤ p₀ := by exact_mod_cast hp.le
    have h3 : c * (2 * p / lam + N₀ + 1) ≤ c * (2 * p₀ / lam + N₀ + 1) := by
      apply mul_le_mul_of_nonneg_left _ (by linarith)
      have : 2 * (p : ℝ) / lam ≤ 2 * p₀ / lam := by gcongr
      linarith
    have h4 : G.Λ' * (Tf p : ℝ) ≤ G.Λ' * (c * (2 * p₀ / lam + N₀ + 1)) :=
      mul_le_mul_of_nonneg_left ((hTf p).trans h3) hΛ0
    have h5 : 0 ≤ (1 + 2 * ((ρ : ℝ) + G.Λ' * (c - 1)) / lam) * p := by positivity
    linarith
  refine ⟨t₀, ht₀, ε, hε, Tp, Tm, fun p ↦ a * r ^ p, c₀', p₀, fun p ↦ mul_pos ha (pow_pos hr0 p),
    ?_,
    tendsto_log_geometric_ratio ha hr0 hr1, fun p ↦ ?_, fun p ↦ ?_, hTp, hTm, hbound,
    fun p ↦ ?_, fun p ↦ ?_, fun p hp ↦ ?_⟩
  · have := (tendsto_pow_atTop_nhds_zero_of_lt_one hr0.le hr1).const_mul a
    rwa [mul_zero] at this
  · rw [hlogδ]; linarith
  · rw [hlogδ]; linarith
  · rcases lt_or_ge p p₀ with hp | hp
    · exact hSlin G.f G.uPlus hu0 huM Tp (fun p ↦ (hbound p).1) p hp
    · have := (hest' p hp).2.2.2.1
      linarith
  · rcases lt_or_ge p p₀ with hp | hp
    · exact hSlin G.finv G.uMinus hv0 hvM Tm (fun p ↦ (hbound p).2) p hp
    · have := (hest' p hp).2.2.2.2
      linarith
  · obtain ⟨hmemp, hmemm, hmin, -, -⟩ := hest' p hp
    have hcs := hchain (Tp p) (Tm p) hmemp hmemm
    have hpr := hpair (Tp p) (Tm p)
    -- the scale comparison
    have hscale : C * G.combinedScale ρ (Tp p) (Tm p) x ≤ a * r ^ p := by
      rw [G.combinedScale_eq, ha_def, hr, mul_assoc]
      refine mul_le_mul_of_nonneg_left ?_ (by linarith)
      rw [← Real.rpow_mul_natCast two_pos.le, ← Real.rpow_add two_pos]
      apply Real.rpow_le_rpow_of_exponent_le one_le_two
      linarith
    have hanti := precisionComplexityNat_anti P A (x := G.φ t₀ x)
      (mul_pos (by linarith) (G.combinedScale_pos _ _ _ _)) hscale
    have hcsR : ((precisionComplexityNat P A (G.φ t₀ x)
        (C * G.combinedScale ρ (Tp p) (Tm p) x) : ℕ) : ℝ) ≤
        (orbitComplexityNat P G.f A x (Tp p + 1) ε : ℝ) +
          orbitComplexityNat P G.finv A x (Tm p + 1) ε + oraclePairComplexity A (Tp p) (Tm p) +
          c₀ := by
      exact_mod_cast hcs
    have hantiR : ((precisionComplexityNat P A (G.φ t₀ x) (a * r ^ p) : ℕ) : ℝ) ≤
        precisionComplexityNat P A (G.φ t₀ x)
          (C * G.combinedScale ρ (Tp p) (Tm p) x) := by
      exact_mod_cast hanti
    linarith

/-- The complexity chain at every large precision. For `x ∈ 𝓡` with positive rates, a rational
loss `ρ < λ̲/2` and `c > 1`, with the box `j`, tolerance `ε`, constant `C` of the interface and
the return times `Tp, Tm` of `return_adjustment`: along the geometric scales
`δ p = C 2^{κ₀} 2^{-(1-θ) p}` (positive, tending to zero, with `log δ(p+1) / log δ p → 1`),
```
K^A_{δ p}(z) ≤ K^A_{Tp p + 1}(x,f,ε) + K^A_{Tm p + 1}(x,f⁻¹,ε)
                + 2 log₂(Tp p + 1) + 2 log₂(Tm p + 1) + c₀
```
for all `p ≥ p₀`, where `z = φ t₀ x` is the shifted section point of the interface for the
parameters `(c, ρ)` (`|t₀| ≤ aMax`). The hypothesis `2ρ(c-1) < λ̲` (i.e. `θ < 1`) is
necessary for `δ p → 0`; it was missing from the blueprint statement. Blueprint node
`geo:precision-chain`. -/
theorem precision_chain (hA : OrbitToLocationEstimate G P A) {x : X} (hx : G.ControlledReturns x)
    (hpos : G.PositiveRates x) :
    ∃ lam : ℝ, 0 < lam ∧ ∃ N₀ : ℕ,
      ∀ c : ℝ, 1 < c → ∀ ρ : ℚ, 0 < ρ → (ρ : ℝ) < lam / 2 → 2 * (ρ : ℝ) * (c - 1) < lam →
        ∃ t₀ : ℝ, |t₀| ≤ G.aMax ∧
        ∃ ε : ℝ, 0 < ε ∧ ∃ Tp Tm : ℕ → ℕ, ∃ δ : ℕ → ℝ, ∃ c₀ : ℝ, ∃ p₀ : ℕ,
          (∀ p, 0 < δ p) ∧ Tendsto δ atTop (𝓝 0) ∧
          Tendsto (fun p ↦ Real.log (δ (p + 1)) / Real.log (δ p)) atTop (𝓝 1) ∧
          (∀ p, -Real.logb 2 (δ p) ≤ (1 - 2 * ρ * (c - 1) / lam) * p + c₀) ∧
          (∀ p, (1 - 2 * ρ * (c - 1) / lam) * p - c₀ ≤ -Real.logb 2 (δ p)) ∧
          Tendsto Tp atTop atTop ∧ Tendsto Tm atTop atTop ∧
          (∀ p, (Tp p : ℝ) ≤ c * (2 * p / lam + N₀ + 1) ∧
            (Tm p : ℝ) ≤ c * (2 * p / lam + N₀ + 1)) ∧
          (∀ p, birkhoffSum G.f G.uPlus (Tp p) x ≤ (1 + 2 * (ρ + G.Λ' * (c - 1)) / lam) * p + c₀) ∧
          (∀ p, birkhoffSum G.finv G.uMinus (Tm p) x ≤
            (1 + 2 * (ρ + G.Λ' * (c - 1)) / lam) * p + c₀) ∧
          ∀ p : ℕ, p₀ ≤ p →
            (precisionComplexityNat P A (G.φ t₀ x) (δ p) : ℝ) ≤
              orbitComplexityNat P G.f A x (Tp p + 1) ε +
                orbitComplexityNat P G.finv A x (Tm p + 1) ε +
                2 * Real.logb 2 ((Tp p : ℝ) + 1) + 2 * Real.logb 2 ((Tm p : ℝ) + 1) + c₀ :=
  precision_chain_aux P hA hx hpos

/-! ### Limit helpers for `geo:section-point-upper` and `geo:section-point-mixed` -/

/-- A limsup along a subsequence tending to infinity is at most the limsup. -/
theorem limsup_comp_le_of_tendsto_atTop {u : ℕ → ℝ≥0∞} {T : ℕ → ℕ}
    (hT : Tendsto T atTop atTop) : limsup (fun p ↦ u (T p)) atTop ≤ limsup u atTop := by
  exact hT.limsup_comp_le_limsup (u := u)

/-- A liminf over the right filter at `0` is at most the liminf along any positive sequence
tending to `0`. -/
theorem liminf_nhdsWithin_le_liminf_seq {g : ℝ → ℝ≥0∞} {δ : ℕ → ℝ} (hpos : ∀ p, 0 < δ p)
    (hδ : Tendsto δ atTop (𝓝 0)) :
    liminf g (𝓝[>] (0 : ℝ)) ≤ liminf (fun p ↦ g (δ p)) atTop := by
  have ht : Tendsto δ atTop (𝓝[>] (0 : ℝ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hδ, Eventually.of_forall hpos⟩
  exact ht.liminf_le_liminf_comp (u := g)

omit [MetricSpace X] [CompactSpace X] in
/-- Subadditivity of `limsup` in `ℝ≥0∞` along `atTop` (the library lemma `ENNReal.limsup_add_le`
needs a countably closed filter, which `atTop` on `ℕ` is not). -/
lemma ennreal_limsup_add_le (u v : ℕ → ℝ≥0∞) :
    limsup (u + v) atTop ≤ limsup u atTop + limsup v atTop := by
  by_cases hu : limsup u atTop = ⊤
  · simp [hu]
  by_cases hv : limsup v atTop = ⊤
  · simp [hv]
  refine ENNReal.le_of_forall_pos_le_add fun ε hε _ ↦ ?_
  have hε2 : (ε : ℝ≥0∞) / 2 ≠ 0 := (ENNReal.half_pos (by exact_mod_cast hε.ne')).ne'
  have ha : limsup u atTop < limsup u atTop + ε / 2 := ENNReal.lt_add_right hu hε2
  have hb : limsup v atTop < limsup v atTop + ε / 2 := ENNReal.lt_add_right hv hε2
  refine limsup_le_of_le (by isBoundedDefault) ?_
  filter_upwards [eventually_lt_of_limsup_lt ha, eventually_lt_of_limsup_lt hb] with n h1 h2
  calc (u + v) n = u n + v n := rfl
    _ ≤ (limsup u atTop + ε / 2) + (limsup v atTop + ε / 2) := add_le_add h1.le h2.le
    _ = limsup u atTop + limsup v atTop + ε := by rw [add_add_add_comm, ENNReal.add_halves]

end limits

end Kolmogorov.PointToSet
