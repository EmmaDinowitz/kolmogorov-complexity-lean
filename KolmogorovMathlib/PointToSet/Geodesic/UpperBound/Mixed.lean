/-
Copyright (c) 2026 Emma Dinowitz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emma Dinowitz
-/
import KolmogorovMathlib.PointToSet.Geodesic.UpperBound.SectionPoint
import KolmogorovMathlib.PointToSet.Geodesic.FlowInterface.OrbitExtension

/-!
# The mixed section-point bound (Chapter I, part 4)

The node `geo:section-point-mixed` of `geodesic_upper_bound_blueprint.md`: the Hausdorff-side
bound `dim^A(x) ≤ 1 + min (dim^A_BS(x,f,u⁺) + Dim^A_BS(x,f⁻¹,u⁻), Dim^A_BS(x,f,u⁺) +
dim^A_BS(x,f⁻¹,u⁻))`. The analytic core `mixed_core` is stated for abstract two-sided data:
the side whose lower limit appears is followed along a sequence realizing the `liminf` of the
centered costs, its regular return is reached by padding the orbit description by a constant
number of steps (`orbit_extension`, Chapter A), and the other side uses stopping times and
returns as in `return_adjustment`. `sectionPoint_mixed` instantiates it for both orders of the
two sides.
-/

namespace Kolmogorov.PointToSet

open Filter Set
open scoped Topology ENNReal Computability

variable {X : Type*} [MetricSpace X] [CompactSpace X]

section limits

variable {G : GeodesicReconstructionData X} (P : Presentation X) {A : Set ℕ}

/-! ### `geo:section-point-mixed` -/

set_option maxHeartbeats 1600000 in
-- The two-sided `limsup`/`liminf` bookkeeping below elaborates many `ℝ≥0∞` inequalities in one
-- proof and exceeds the default heartbeat budget.
/-- The analytic core of `sectionPoint_mixed`, for abstract two-sided data. Side `1` is the side
whose lower limit appears: its duration is chosen along a sequence `n k` realizing the `liminf`
of the centered costs, and the regular return in `[n k / c, n k + c]` is reached by padding the
orbit description by the constant `⌈c⌉₊` steps (`orbit_extension`), at cost `O(log n k)`. Side
`2` uses stopping times and returns as in `return_adjustment`. (This replaces the blueprint's
padding from `n k` to `c n k`, whose cost `(c-1) n_k ⌈log₂ N(ε)⌉` cannot be made small because
`ε` depends on the return sets, hence on `c`.) -/
private lemma mixed_core {T₁ T₂ : X → X} (hT₁ : Continuous T₁) (hT₂ : Continuous T₂)
    {u₁ u₂ : X → ℝ} (hu₁ : UniformContinuous u₁) (hu₂ : UniformContinuous u₂)
    (hu₁0 : ∀ y, 0 ≤ u₁ y) (hu₂0 : ∀ y, 0 ≤ u₂ y) {M : ℝ} (hu₁M : ∀ y, u₁ y ≤ M)
    (hu₂M : ∀ y, u₂ y ≤ M) (hP : ComputablePresentationIn P A)
    (hT₁A : IsRepresentedMapIn P P A T₁) {x : X}
    (hpos₁ : 0 < lowerBirkhoffAverage T₁ u₁ x) (hpos₂ : 0 < lowerBirkhoffAverage T₂ u₂ x)
    {σ₁ σ₂ : ℝ → ℝ}
    (hret : ∀ c : ℝ, 1 < c → ∃ P₁ P₂ : Set X, IsCompact P₁ ∧ P₁ ⊆ G.Reg ∧ IsCompact P₂ ∧
      P₂ ⊆ G.Reg ∧ ∃ K : ℕ, ∀ n : ℕ, K < n →
        (∃ T : ℕ, n ≤ T ∧ (T : ℝ) ≤ c * n ∧ G.φ (σ₁ T) x ∈ P₁) ∧
        (∃ T : ℕ, n ≤ T ∧ (T : ℝ) ≤ c * n ∧ G.φ (σ₂ T) x ∈ P₂))
    (hest : ∀ P₁ P₂ : Set X, IsCompact P₁ → P₁ ⊆ G.Reg → IsCompact P₂ → P₂ ⊆ G.Reg →
      ∀ ρ : ℚ, 0 < ρ → ∃ z : X,
        (staticPointDimensions P A x).1 ≤ 1 + (staticPointDimensions P A z).1 ∧
        ∃ ε : ℝ, 0 < ε ∧ ∃ C : ℝ, 1 < C ∧ ∃ c₀ : ℝ, ∀ n₁ n₂ : ℕ,
        G.φ (σ₁ n₁) x ∈ P₁ → G.φ (σ₂ n₂) x ∈ P₂ →
        (precisionComplexityNat P A z (C * (2 : ℝ) ^ (-min (birkhoffSum T₁ u₁ n₁ x - ρ * n₁)
          (birkhoffSum T₂ u₂ n₂ x - ρ * n₂))) : ℝ) ≤
          orbitComplexityNat P T₁ A x (n₁ + 1) ε + orbitComplexityNat P T₂ A x (n₂ + 1) ε +
            2 * Real.logb 2 ((n₁ : ℝ) + 1) + 2 * Real.logb 2 ((n₂ : ℝ) + 1) + c₀) :
    (staticPointDimensions P A x).1 ≤
      1 + ((pointwiseBSDimension P T₁ u₁ A x).1 + (pointwiseBSDimension P T₂ u₂ A x).2) := by
  classical
  obtain ⟨lam₁, hlam₁, N₁, hN₁⟩ :=
    GeodesicReconstructionData.exists_linear_of_lowerBirkhoffAverage_pos hpos₁
  obtain ⟨lam₂, hlam₂, N₂, hN₂⟩ :=
    GeodesicReconstructionData.exists_linear_of_lowerBirkhoffAverage_pos hpos₂
  have hM0 : 0 ≤ M := (hu₁0 x).trans (hu₁M x)
  set lam : ℝ := min (min lam₁ lam₂) (2 / (N₂ + 1)) with hlam_def
  have hlam : 0 < lam := lt_min (lt_min hlam₁ hlam₂) (by positivity)
  have hlam₁' : lam ≤ lam₁ := (min_le_left _ _).trans (min_le_left _ _)
  have hlam₂' : lam ≤ lam₂ := (min_le_left _ _).trans (min_le_right _ _)
  have hlamN : lam * (N₂ + 1) ≤ 2 := by
    have := min_le_right (min lam₁ lam₂) (2 / ((N₂ : ℝ) + 1))
    rwa [le_div_iff₀ (by positivity)] at this
  obtain ⟨q₁, η₁, hη₁, hbs₁⟩ :=
    centeredBSCost_timeLimit_le_pointwiseBSDimension P T₁ hT₁ u₁ hu₁ A x hpos₁ .lower
  obtain ⟨q₂, η₂, hη₂, hbs₂⟩ :=
    centeredBSCost_timeLimit_le_pointwiseBSDimension P T₂ hT₂ u₂ hu₂ A x hpos₂ .upper
  set d₁ := (pointwiseBSDimension P T₁ u₁ A x).1 with hd₁
  set D₂ := (pointwiseBSDimension P T₂ u₂ A x).2 with hD₂
  /- Claim A: the bound with multiplicative losses, for fixed admissible parameters. -/
  have claimA : ∀ c : ℝ, 1 < c → ∀ ρ : ℚ, 0 < ρ → (ρ : ℝ) < lam / 2 →
      2 * ((ρ : ℝ) + M) * (c - 1) < lam → ∀ M₁ M₂ : ℝ,
      (1 + 2 * (ρ : ℝ) / lam) / (1 - 2 * ((ρ : ℝ) + M) * (c - 1) / lam) < M₁ →
      (1 + 2 * ((ρ : ℝ) + M * (c - 1)) / lam) / (1 - 2 * ((ρ : ℝ) + M) * (c - 1) / lam) < M₂ →
      ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q →
        (staticPointDimensions P A x).1 ≤ 1 +
          (ENNReal.ofReal M₁ * ((1 + η₁ (q + 1)) * d₁) +
            ENNReal.ofReal M₂ * ((1 + η₂ q) * D₂)) := by
    intro c hc ρ hρ hρlam hϑ M₁ M₂ hM₁ hM₂
    set ϑ : ℝ := 2 * ((ρ : ℝ) + M) * (c - 1) / lam with hϑdef
    have hρ' : (0 : ℝ) < ρ := by exact_mod_cast hρ
    have hc0 : 0 < c := by linarith
    have hc1 : 0 ≤ c - 1 := by linarith
    have hϑ0 : 0 ≤ ϑ := by rw [hϑdef]; positivity
    have hϑ1 : 0 < 1 - ϑ := by rw [hϑdef, sub_pos, div_lt_one hlam]; exact hϑ
    have hM₁' : 1 + 2 * (ρ : ℝ) / lam < M₁ * (1 - ϑ) := by rwa [div_lt_iff₀ hϑ1] at hM₁
    have hM₂' : 1 + 2 * ((ρ : ℝ) + M * (c - 1)) / lam < M₂ * (1 - ϑ) := by
      rwa [div_lt_iff₀ hϑ1] at hM₂
    have hM₁0 : 0 < M₁ := lt_trans (div_pos (by positivity) hϑ1) hM₁
    have hM₂0 : 0 < M₂ := lt_trans (div_pos (by positivity) hϑ1) hM₂
    obtain ⟨P₁, P₂, hP₁, hP₁R, hP₂, hP₂R, K, hK⟩ := hret c hc
    obtain ⟨z, hzx, ε, hε, C, hC, c₀, hchain⟩ := hest P₁ P₂ hP₁ hP₁R hP₂ hP₂R ρ hρ
    -- side 2: stopping times and returns
    obtain ⟨nm, hnm, hnmb, hnmS⟩ := GeodesicReconstructionData.stopping_time_aux hu₂0 hu₂M x hN₂
      hlam hlam₂' hlamN hρ' hρlam
    have hT₂ex : ∀ p, ∃ T : ℕ, nm p ≤ T ∧ (T : ℝ) ≤ c * nm p ∧
        (K < nm p → G.φ (σ₂ T) x ∈ P₂) := by
      intro p
      by_cases hp : K < nm p
      · obtain ⟨T, h1, h2, h3⟩ := (hK (nm p) hp).2
        exact ⟨T, h1, h2, fun _ ↦ h3⟩
      · exact ⟨nm p, le_rfl, le_mul_of_one_le_left (Nat.cast_nonneg _) hc.le,
          fun h' ↦ (hp h').elim⟩
    choose Tm hTm using hT₂ex
    have hTmtend : Tendsto Tm atTop atTop := tendsto_atTop_mono (fun p ↦ (hTm p).1) hnm
    -- the dyadic precision
    obtain ⟨q₀, hq₀⟩ := exists_dyadicRadius_lt hε
    refine ⟨max q₀ (max q₁ q₂), fun q hq ↦ ?_⟩
    have hqε : dyadicRadius q ≤ ε :=
      (dyadicRadius_antitone (le_of_max_le_left hq)).trans hq₀.le
    have hq₁ : q₁ ≤ q + 1 := (le_of_max_le_left (le_of_max_le_right hq)).trans (Nat.le_succ q)
    have hq₂ : q₂ ≤ q := le_of_max_le_right (le_of_max_le_right hq)
    -- orbit extension at radius `2^{-(q+1)}`
    obtain ⟨Next, cext, hext⟩ := orbit_extension P T₁ hT₁ A hP hT₁A
      (ε := (2 : ℚ)⁻¹ ^ (q + 1)) (by positivity)
    have hcast : (((2 : ℚ)⁻¹ ^ (q + 1) : ℚ) : ℝ) = dyadicRadius (q + 1) := by
      simp only [dyadicRadius, Rat.cast_pow, Rat.cast_inv, Rat.cast_ofNat]
    rw [hcast] at hext
    have h2dy : 2 * dyadicRadius (q + 1) = dyadicRadius q := by
      simp only [dyadicRadius, pow_succ]
      ring
    rw [h2dy] at hext
    -- side 1: the sequence realizing the lower limit
    set w : ℕ → ℝ≥0∞ := fun n ↦ centeredBSCost P T₁ u₁ A x (n + 1) (dyadicRadius (q + 1))
      with hw
    obtain ⟨n, hwn, hntend⟩ := exists_seq_tendsto_liminf (u := w) (f := atTop)
    have hliminf_w : liminf w atTop ≤ (1 + η₁ (q + 1)) * d₁ := by
      have h1 := orbitComplexityNat_timeLimit_order_shift P T₁ A x (dyadicRadius (q + 1))
        (fun n ↦ ENNReal.ofReal (birkhoffSum T₁ u₁ n x)) .lower
      have h2 := hbs₁ (q + 1) hq₁
      calc liminf w atTop
          = liminf (fun n ↦ centeredBSCost P T₁ u₁ A x n (dyadicRadius (q + 1))) atTop := h1
        _ ≤ (1 + η₁ (q + 1)) * d₁ := h2
    -- the precisions `p k`
    set p : ℕ → ℕ := fun k ↦ ⌊birkhoffSum T₁ u₁ (n k) x - ρ * n k⌋₊ with hp
    have hpk : ∀ k, N₁ ≤ n k →
        (p k : ℝ) ≤ birkhoffSum T₁ u₁ (n k) x - ρ * n k ∧
        birkhoffSum T₁ u₁ (n k) x - ρ * n k < p k + 1 ∧ lam / 2 * n k ≤ p k + 1 := by
      intro k hk
      have h1 := hN₁ (n k) hk
      have h2 : ρ * (n k : ℝ) ≤ lam / 2 * n k :=
        mul_le_mul_of_nonneg_right hρlam.le (Nat.cast_nonneg _)
      have h3 : lam * (n k : ℝ) ≤ lam₁ * n k :=
        mul_le_mul_of_nonneg_right hlam₁' (Nat.cast_nonneg _)
      have h0 : 0 ≤ lam / 2 * (n k : ℝ) := by positivity
      have hnn : 0 ≤ birkhoffSum T₁ u₁ (n k) x - ρ * n k := by linarith
      have h4 := Nat.lt_floor_add_one (birkhoffSum T₁ u₁ (n k) x - ρ * n k)
      exact ⟨Nat.floor_le hnn, h4, by linarith only [h1, h2, h3, h4]⟩
    have hptend : Tendsto p atTop atTop := by
      rw [← tendsto_natCast_atTop_iff (R := ℝ)]
      have h1 : Tendsto (fun k ↦ lam / 2 * ((n k : ℕ) : ℝ) + (-1)) atTop atTop :=
        tendsto_atTop_add_const_right atTop (-1)
          ((tendsto_natCast_atTop_atTop.comp hntend).const_mul_atTop (half_pos hlam))
      refine tendsto_atTop_mono' atTop ?_ h1
      filter_upwards [hntend.eventually_ge_atTop N₁] with k hk
      have := (hpk k hk).2.2
      change lam / 2 * (n k : ℝ) + -1 ≤ (p k : ℝ)
      linarith
    -- side 1: return times in `[n k / c, n k + c]`
    have hT₁ex : ∀ k, ∃ T : ℕ, K < ⌈(n k : ℝ) / c⌉₊ →
        ⌈(n k : ℝ) / c⌉₊ ≤ T ∧ (T : ℝ) ≤ c * ⌈(n k : ℝ) / c⌉₊ ∧ G.φ (σ₁ T) x ∈ P₁ := by
      intro k
      by_cases hk : K < ⌈(n k : ℝ) / c⌉₊
      · obtain ⟨T, h1, h2, h3⟩ := (hK _ hk).1
        exact ⟨T, fun _ ↦ ⟨h1, h2, h3⟩⟩
      · exact ⟨0, fun h ↦ (hk h).elim⟩
    choose Tp hTp using hT₁ex
    set m : ℕ := ⌈c⌉₊ with hm
    have hcm : c ≤ m := Nat.le_ceil c
    have hTpf : ∀ k, K < ⌈(n k : ℝ) / c⌉₊ →
        (n k : ℝ) / c ≤ Tp k ∧ (Tp k : ℝ) ≤ n k + c ∧ Tp k + 1 ≤ n k + 1 + m := by
      intro k hk
      obtain ⟨h1, h2, -⟩ := hTp k hk
      have hceil := Nat.le_ceil ((n k : ℝ) / c)
      have hceil' : (⌈(n k : ℝ) / c⌉₊ : ℝ) < (n k : ℝ) / c + 1 :=
        Nat.ceil_lt_add_one (by positivity)
      have h3 : c * (⌈(n k : ℝ) / c⌉₊ : ℝ) ≤ c * ((n k : ℝ) / c + 1) :=
        mul_le_mul_of_nonneg_left hceil'.le hc0.le
      have h4 : c * ((n k : ℝ) / c + 1) = n k + c := by field_simp
      have h5 : (Tp k : ℝ) ≤ n k + c := by linarith
      refine ⟨hceil.trans (by exact_mod_cast h1), h5, ?_⟩
      exact_mod_cast (show (Tp k : ℝ) + 1 ≤ n k + 1 + m by linarith)
    have hKev : ∀ᶠ k in atTop, K < ⌈(n k : ℝ) / c⌉₊ := by
      filter_upwards [hntend.eventually_ge_atTop ⌈((K : ℝ) + 1) * c⌉₊] with k hk
      have h1 : ((K : ℝ) + 1) * c ≤ n k := (Nat.le_ceil _).trans (by exact_mod_cast hk)
      have h2 : (K : ℝ) + 1 ≤ (n k : ℝ) / c := by rw [le_div_iff₀ hc0]; exact h1
      have h3 : (K : ℝ) < ⌈(n k : ℝ) / c⌉₊ := by linarith [Nat.le_ceil ((n k : ℝ) / c)]
      exact_mod_cast h3
    -- the constants and the scale sequence
    set κ : ℝ := 2 * M * (c - 1) / lam + ρ * c + ρ * (c - 1) with hκ
    have hκ0 : 0 ≤ κ := by rw [hκ]; positivity
    set r : ℝ := (2 : ℝ) ^ (-(1 - ϑ)) with hr
    have hr0 : 0 < r := Real.rpow_pos_of_pos two_pos _
    have hr1 : r < 1 := Real.rpow_lt_one_of_one_lt_of_neg one_lt_two (by linarith)
    set a : ℝ := C * (2 : ℝ) ^ κ with ha_def
    have ha : 0 < a := mul_pos (by linarith) (Real.rpow_pos_of_pos two_pos _)
    have hlogC : 0 < Real.logb 2 C := Real.logb_pos one_lt_two hC
    set δ : ℕ → ℝ := fun k ↦ a * r ^ p k with hδ
    have hδpos : ∀ k, 0 < δ k := fun k ↦ mul_pos ha (pow_pos hr0 _)
    have hδ0 : Tendsto δ atTop (𝓝 0) := by
      have := ((tendsto_pow_atTop_nhds_zero_of_lt_one hr0.le hr1).comp hptend).const_mul a
      rwa [mul_zero] at this
    set c₀' : ℝ := Real.logb 2 C + κ with hc₀'
    have hlogδ : ∀ k, -Real.logb 2 (δ k) = (1 - ϑ) * p k - c₀' := by
      intro k
      simp only [hδ]
      rw [Real.logb_mul ha.ne' (pow_ne_zero _ hr0.ne'), Real.logb_pow, hr, ha_def,
        Real.logb_mul (by linarith) (Real.rpow_pos_of_pos two_pos _).ne',
        Real.logb_rpow two_pos (by norm_num), Real.logb_rpow two_pos (by norm_num), hc₀']
      ring
    -- eventual facts
    have hd₀ : Tendsto (fun k : ℕ ↦ (1 - ϑ) * p k - c₀') atTop atTop := by
      have := tendsto_atTop_add_const_right atTop (-c₀')
        ((tendsto_natCast_atTop_atTop.comp hptend).const_mul_atTop hϑ1)
      refine this.congr fun k ↦ ?_
      simp only [Function.comp_apply, sub_eq_add_neg]
    have hsl₁ : 0 < M₁ * (1 - ϑ) - (1 + 2 * (ρ : ℝ) / lam) := by linarith
    have hsl₂ : 0 < M₂ * (1 - ϑ) - (1 + 2 * ((ρ : ℝ) + M * (c - 1)) / lam) := by linarith
    have hMd₁ : Tendsto (fun k : ℕ ↦ (M₁ * (1 - ϑ) - (1 + 2 * (ρ : ℝ) / lam)) * p k) atTop
        atTop := (tendsto_natCast_atTop_atTop.comp hptend).const_mul_atTop hsl₁
    have hMd₂ : Tendsto (fun k : ℕ ↦ (M₂ * (1 - ϑ) - (1 + 2 * ((ρ : ℝ) + M * (c - 1)) / lam)) *
        p k) atTop atTop := (tendsto_natCast_atTop_atTop.comp hptend).const_mul_atTop hsl₂
    have hev : ∀ᶠ k : ℕ in atTop, N₁ ≤ n k ∧ K < ⌈(n k : ℝ) / c⌉₊ ∧ K < nm (p k) ∧
        0 < (1 - ϑ) * p k - c₀' ∧
        2 * ρ / lam + 1 + M + M₁ * c₀' ≤ (M₁ * (1 - ϑ) - (1 + 2 * (ρ : ℝ) / lam)) * p k ∧
        (ρ : ℝ) + M * (c - 1) + 2 * M + ρ + M₂ * c₀' ≤
          (M₂ * (1 - ϑ) - (1 + 2 * ((ρ : ℝ) + M * (c - 1)) / lam)) * p k ∧
        N₂ ≤ Tm (p k) + 1 := by
      filter_upwards [hntend.eventually_ge_atTop N₁, hKev,
        (hnm.comp hptend).eventually_gt_atTop K, hd₀.eventually_gt_atTop 0,
        hMd₁.eventually_ge_atTop _, hMd₂.eventually_ge_atTop _,
        (hTmtend.comp hptend).eventually_ge_atTop N₂] with k h1 h2 h3 h4 h5 h6 h7
      exact ⟨h1, h2, h3, h4, h5, h6, h7.trans (Nat.le_succ _)⟩
    -- the pointwise bound
    have hpt : ∀ᶠ k : ℕ in atTop, normalizedPrecisionComplexity P A z (δ k) ≤
        ENNReal.ofReal M₁ * w (n k) +
        ENNReal.ofReal M₂ * centeredBSCost P T₂ u₂ A x (Tm (p k) + 1) (dyadicRadius q) +
        ENNReal.ofReal ((2 * Real.logb 2 ((Tp k : ℝ) + 1) + 2 * Real.logb 2 ((Tm (p k) : ℝ) + 1) +
          |c₀| + m * (Nat.clog 2 Next : ℝ) + 2 * Real.logb 2 ((n k : ℝ) + 1 + 1) +
          2 * Real.logb 2 ((m : ℝ) + 1) + (cext : ℝ)) / ((1 - ϑ) * p k - c₀')) := by
      filter_upwards [hev] with k hk
      obtain ⟨hkN, hkK, hkK', hd, hMd₁', hMd₂', hN₂'⟩ := hk
      obtain ⟨hp1, hp2, hp3⟩ := hpk k hkN
      obtain ⟨hTp1, hTp2, hTp3⟩ := hTpf k hkK
      have hmem₁ : G.φ (σ₁ (Tp k)) x ∈ P₁ := (hTp k hkK).2.2
      obtain ⟨hTm1, hTm2, hTm3⟩ := hTm (p k)
      have hmem₂ : G.φ (σ₂ (Tm (p k))) x ∈ P₂ := hTm3 hkK'
      obtain ⟨hS1, hS2⟩ := hnmS (p k)
      have hnmb' := hnmb (p k)
      have hn2p : (n k : ℝ) ≤ 2 * (p k + 1) / lam := by
        rw [le_div_iff₀ hlam]; linarith only [hp3]
      have hSm1 := (GeodesicReconstructionData.birkhoffSum_bounds_of_le (T := T₂) hu₂0 hu₂M x
        hTm1).1
      -- side 1 lower bound on the Birkhoff sum at the return time
      have hS₁Tp : birkhoffSum T₁ u₁ (n k) x - M * (c - 1) * n k ≤ birkhoffSum T₁ u₁ (Tp k) x := by
        rcases le_total (Tp k) (n k) with hle | hle
        · have h1 := (GeodesicReconstructionData.birkhoffSum_bounds_of_le (T := T₁) hu₁0 hu₁M x
            hle).2
          rw [Nat.cast_sub hle] at h1
          have h2 : (n k : ℝ) - Tp k ≤ (c - 1) * n k := by
            have h3 : (n k : ℝ) / c * c = n k := div_mul_cancel₀ _ hc0.ne'
            have h4 : (n k : ℝ) / c * c ≤ (Tp k : ℝ) * c :=
              mul_le_mul_of_nonneg_right hTp1 hc0.le
            have h5 : (n k : ℝ) ≤ Tp k * c := by rw [← h3]; exact h4
            have h6 : 0 ≤ (n k : ℝ) * (c - 1) ^ 2 :=
              mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)
            have h7 : (2 - c) * (n k : ℝ) * c ≤ (Tp k : ℝ) * c := by linarith only [h5, h6]
            have h8 : (2 - c) * (n k : ℝ) ≤ Tp k := le_of_mul_le_mul_right h7 hc0
            linarith only [h8]
          have h5 : M * ((n k : ℝ) - Tp k) ≤ M * ((c - 1) * n k) :=
            mul_le_mul_of_nonneg_left h2 hM0
          linarith only [h1, h5]
        · have h1 := (GeodesicReconstructionData.birkhoffSum_bounds_of_le (T := T₁) hu₁0 hu₁M x
            hle).1
          have h2 : 0 ≤ M * (c - 1) * n k := by positivity
          linarith only [h1, h2]
      -- the scale comparison
      have hmin : (1 - ϑ) * p k - κ ≤ min (birkhoffSum T₁ u₁ (Tp k) x - ρ * Tp k)
          (birkhoffSum T₂ u₂ (Tm (p k)) x - ρ * Tm (p k)) := by
        have hϑp : 2 * M * (c - 1) / lam * p k ≤ ϑ * p k := by
          apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
          rw [hϑdef]
          apply div_le_div_of_nonneg_right _ hlam.le
          linarith only [mul_nonneg hρ'.le hc1]
        have hϑp' : 2 * ρ * (c - 1) / lam * p k ≤ ϑ * p k := by
          apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
          rw [hϑdef]
          apply div_le_div_of_nonneg_right _ hlam.le
          linarith only [mul_nonneg hM0 hc1]
        refine le_min ?_ ?_
        · have e1 : M * (c - 1) * (n k : ℝ) ≤ M * (c - 1) * (2 * (p k + 1) / lam) :=
            mul_le_mul_of_nonneg_left hn2p (by positivity)
          have e2 : ρ * (Tp k : ℝ) ≤ ρ * (n k + c) := mul_le_mul_of_nonneg_left hTp2 hρ'.le
          have e3 : M * (c - 1) * (2 * ((p k : ℝ) + 1) / lam) =
              2 * M * (c - 1) / lam * p k + 2 * M * (c - 1) / lam := by ring
          have e4 : 0 ≤ ρ * (c - 1) := by positivity
          rw [hκ]
          linarith only [hS₁Tp, hp1, e1, e2, e3, e4, hϑp]
        · have e1 : ρ * ((Tm (p k) : ℝ) - nm (p k)) ≤ ρ * ((c - 1) * nm (p k)) :=
            mul_le_mul_of_nonneg_left (by linarith) hρ'.le
          have e2 : ρ * (c - 1) * (nm (p k) : ℝ) ≤ ρ * (c - 1) * (2 * p k / lam + 1) :=
            mul_le_mul_of_nonneg_left hnmb' (by positivity)
          have e3 : ρ * (c - 1) * (2 * (p k : ℝ) / lam + 1) =
              2 * ρ * (c - 1) / lam * p k + ρ * (c - 1) := by ring
          have e4 : 0 ≤ 2 * M * (c - 1) / lam + ρ * c := by positivity
          rw [hκ]
          linarith only [hSm1, hS1, e1, e2, e3, e4, hϑp']
      have hscale : C * (2 : ℝ) ^ (-min (birkhoffSum T₁ u₁ (Tp k) x - ρ * Tp k)
          (birkhoffSum T₂ u₂ (Tm (p k)) x - ρ * Tm (p k))) ≤ δ k := by
        simp only [hδ]
        rw [ha_def, hr, mul_assoc]
        refine mul_le_mul_of_nonneg_left ?_ (by linarith)
        rw [← Real.rpow_mul_natCast two_pos.le, ← Real.rpow_add two_pos]
        apply Real.rpow_le_rpow_of_exponent_le one_le_two
        linarith only [hmin]
      -- positivity and upper bounds of the Birkhoff denominators
      have hSppos : 0 < birkhoffSum T₁ u₁ (n k + 1) x :=
        lt_of_lt_of_le (mul_pos hlam₁ (Nat.cast_pos.2 (Nat.succ_pos _)))
          (hN₁ _ (hkN.trans (Nat.le_succ _)))
      have hSmpos : 0 < birkhoffSum T₂ u₂ (Tm (p k) + 1) x :=
        lt_of_lt_of_le (mul_pos hlam₂ (Nat.cast_pos.2 (Nat.succ_pos _))) (hN₂ _ hN₂')
      have hSple : birkhoffSum T₁ u₁ (n k + 1) x ≤ M₁ * ((1 - ϑ) * p k - c₀') := by
        have h1 := (GeodesicReconstructionData.birkhoffSum_bounds_of_le (T := T₁) hu₁0 hu₁M x
          (show n k ≤ n k + 1 by omega)).2
        simp only [add_tsub_cancel_left, Nat.cast_one, mul_one] at h1
        have h2 : ρ * (n k : ℝ) ≤ ρ * (2 * (p k + 1) / lam) :=
          mul_le_mul_of_nonneg_left hn2p hρ'.le
        have h3 : ρ * (2 * ((p k : ℝ) + 1) / lam) = 2 * ρ / lam * p k + 2 * ρ / lam := by ring
        linarith only [h1, hp2, h2, h3, hMd₁']
      have hSmle : birkhoffSum T₂ u₂ (Tm (p k) + 1) x ≤ M₂ * ((1 - ϑ) * p k - c₀') := by
        have h1 := (GeodesicReconstructionData.birkhoffSum_bounds_of_le (T := T₂) hu₂0 hu₂M x
          (show Tm (p k) ≤ Tm (p k) + 1 by omega)).2
        simp only [add_tsub_cancel_left, Nat.cast_one, mul_one] at h1
        have h2 := (GeodesicReconstructionData.birkhoffSum_bounds_of_le (T := T₂) hu₂0 hu₂M x
          hTm1).2
        rw [Nat.cast_sub hTm1] at h2
        have h3 : M * ((Tm (p k) : ℝ) - nm (p k)) ≤ M * ((c - 1) * nm (p k)) :=
          mul_le_mul_of_nonneg_left (by linarith) hM0
        have h4 : (ρ + M * (c - 1)) * (nm (p k) : ℝ) ≤ (ρ + M * (c - 1)) * (2 * p k / lam + 1) :=
          mul_le_mul_of_nonneg_left hnmb' (by positivity)
        have h5 : ((ρ : ℝ) + M * (c - 1)) * (2 * (p k : ℝ) / lam + 1) =
            2 * ((ρ : ℝ) + M * (c - 1)) / lam * p k + (ρ + M * (c - 1)) := by ring
        linarith only [h1, h2, hS2, h3, h4, h5, hMd₂']
      -- the complexity chain in `ℝ`
      have hKR : (precisionComplexityNat P A z (δ k) : ℝ) ≤
          (orbitComplexityNat P T₁ A x (n k + 1) (dyadicRadius (q + 1)) : ℝ) +
          orbitComplexityNat P T₂ A x (Tm (p k) + 1) (dyadicRadius q) +
          (2 * Real.logb 2 ((Tp k : ℝ) + 1) + 2 * Real.logb 2 ((Tm (p k) : ℝ) + 1) + |c₀| +
            m * (Nat.clog 2 Next : ℝ) + 2 * Real.logb 2 ((n k : ℝ) + 1 + 1) +
            2 * Real.logb 2 ((m : ℝ) + 1) + (cext : ℝ)) := by
        have h1 := hchain (Tp k) (Tm (p k)) hmem₁ hmem₂
        have h2 : (precisionComplexityNat P A z (δ k) : ℝ) ≤
            precisionComplexityNat P A z (C * (2 : ℝ) ^ (-min
              (birkhoffSum T₁ u₁ (Tp k) x - ρ * Tp k)
              (birkhoffSum T₂ u₂ (Tm (p k)) x - ρ * Tm (p k)))) := by
          exact_mod_cast precisionComplexityNat_anti P A
            (mul_pos (by linarith) (Real.rpow_pos_of_pos two_pos _)) hscale
        have h3 : (orbitComplexityNat P T₁ A x (Tp k + 1) ε : ℝ) ≤
            orbitComplexityNat P T₁ A x (Tp k + 1) (dyadicRadius q) := by
          exact_mod_cast orbitComplexityNat_anti_radius P T₁ A x hT₁ (Tp k + 1)
            (dyadicRadius_pos q) hqε
        have h4 : (orbitComplexityNat P T₂ A x (Tm (p k) + 1) ε : ℝ) ≤
            orbitComplexityNat P T₂ A x (Tm (p k) + 1) (dyadicRadius q) := by
          exact_mod_cast orbitComplexityNat_anti_radius P T₂ A x hT₂ (Tm (p k) + 1)
            (dyadicRadius_pos q) hqε
        have h5 : (orbitComplexityNat P T₁ A x (Tp k + 1) (dyadicRadius q) : ℝ) ≤
            orbitComplexityNat P T₁ A x (n k + 1 + m) (dyadicRadius q) := by
          exact_mod_cast orbitComplexityNat_mono_order P T₁ A x hT₁ (dyadicRadius_pos q) hTp3
        have h6 := hext x (n k + 1) m (by omega)
        push_cast at h6
        linarith only [h1, h2, h3, h4, h5, h6, le_abs_self c₀]
      -- the real inequality
      have hreal : (precisionComplexityNat P A z (δ k) : ℝ) / ((1 - ϑ) * p k - c₀') ≤
          M₁ * ((orbitComplexityNat P T₁ A x (n k + 1) (dyadicRadius (q + 1)) : ℝ) /
              birkhoffSum T₁ u₁ (n k + 1) x) +
            M₂ * ((orbitComplexityNat P T₂ A x (Tm (p k) + 1) (dyadicRadius q) : ℝ) /
              birkhoffSum T₂ u₂ (Tm (p k) + 1) x) +
            (2 * Real.logb 2 ((Tp k : ℝ) + 1) + 2 * Real.logb 2 ((Tm (p k) : ℝ) + 1) + |c₀| +
              m * (Nat.clog 2 Next : ℝ) + 2 * Real.logb 2 ((n k : ℝ) + 1 + 1) +
              2 * Real.logb 2 ((m : ℝ) + 1) + (cext : ℝ)) / ((1 - ϑ) * p k - c₀') := by
        have h2 := div_le_div_of_nonneg_right hKR hd.le
        have h4 : (orbitComplexityNat P T₁ A x (n k + 1) (dyadicRadius (q + 1)) : ℝ) /
            birkhoffSum T₁ u₁ (n k + 1) x * (birkhoffSum T₁ u₁ (n k + 1) x /
              ((1 - ϑ) * p k - c₀')) =
            orbitComplexityNat P T₁ A x (n k + 1) (dyadicRadius (q + 1)) /
              ((1 - ϑ) * p k - c₀') := by
          rw [div_mul_div_comm, mul_comm (birkhoffSum T₁ u₁ (n k + 1) x) ((1 - ϑ) * p k - c₀'),
            mul_div_mul_right _ _ hSppos.ne']
        have h5 : (orbitComplexityNat P T₂ A x (Tm (p k) + 1) (dyadicRadius q) : ℝ) /
            birkhoffSum T₂ u₂ (Tm (p k) + 1) x * (birkhoffSum T₂ u₂ (Tm (p k) + 1) x /
              ((1 - ϑ) * p k - c₀')) =
            orbitComplexityNat P T₂ A x (Tm (p k) + 1) (dyadicRadius q) /
              ((1 - ϑ) * p k - c₀') := by
          rw [div_mul_div_comm,
            mul_comm (birkhoffSum T₂ u₂ (Tm (p k) + 1) x) ((1 - ϑ) * p k - c₀'),
            mul_div_mul_right _ _ hSmpos.ne']
        have h6 : birkhoffSum T₁ u₁ (n k + 1) x / ((1 - ϑ) * p k - c₀') ≤ M₁ := by
          rw [div_le_iff₀ hd]; exact hSple
        have h7 : birkhoffSum T₂ u₂ (Tm (p k) + 1) x / ((1 - ϑ) * p k - c₀') ≤ M₂ := by
          rw [div_le_iff₀ hd]; exact hSmle
        have h8 := mul_le_mul_of_nonneg_left h6 (div_nonneg
          (Nat.cast_nonneg (orbitComplexityNat P T₁ A x (n k + 1) (dyadicRadius (q + 1))))
          hSppos.le)
        have h9 := mul_le_mul_of_nonneg_left h7 (div_nonneg
          (Nat.cast_nonneg (orbitComplexityNat P T₂ A x (Tm (p k) + 1) (dyadicRadius q)))
          hSmpos.le)
        rw [h4] at h8
        rw [h5] at h9
        rw [add_div, add_div] at h2
        rw [mul_comm M₁, mul_comm M₂]
        linarith only [h2, h8, h9]
      -- back to `ℝ≥0∞`
      have eK : normalizedPrecisionComplexity P A z (δ k) =
          ENNReal.ofReal ((precisionComplexityNat P A z (δ k) : ℝ) /
            ((1 - ϑ) * p k - c₀')) := by
        rw [normalizedPrecisionComplexity, hlogδ, ENNReal.ofReal_div_of_pos hd,
          ENNReal.ofReal_natCast]
      have eP : w (n k) =
          ENNReal.ofReal ((orbitComplexityNat P T₁ A x (n k + 1) (dyadicRadius (q + 1)) : ℝ) /
            birkhoffSum T₁ u₁ (n k + 1) x) := by
        simp only [hw]
        rw [centeredBSCost, ENNReal.ofReal_div_of_pos hSppos, ENNReal.ofReal_natCast]
      have eM : centeredBSCost P T₂ u₂ A x (Tm (p k) + 1) (dyadicRadius q) =
          ENNReal.ofReal ((orbitComplexityNat P T₂ A x (Tm (p k) + 1) (dyadicRadius q) : ℝ) /
            birkhoffSum T₂ u₂ (Tm (p k) + 1) x) := by
        rw [centeredBSCost, ENNReal.ofReal_div_of_pos hSmpos, ENNReal.ofReal_natCast]
      rw [eK, eP, eM, ← ENNReal.ofReal_mul hM₁0.le, ← ENNReal.ofReal_mul hM₂0.le]
      refine (ENNReal.ofReal_le_ofReal hreal).trans ?_
      refine ENNReal.ofReal_add_le.trans ?_
      exact add_le_add ENNReal.ofReal_add_le le_rfl
    -- the error term tends to zero
    have he : Tendsto (fun k : ℕ ↦ ENNReal.ofReal ((2 * Real.logb 2 ((Tp k : ℝ) + 1) +
        2 * Real.logb 2 ((Tm (p k) : ℝ) + 1) + |c₀| + m * (Nat.clog 2 Next : ℝ) +
        2 * Real.logb 2 ((n k : ℝ) + 1 + 1) + 2 * Real.logb 2 ((m : ℝ) + 1) + (cext : ℝ)) /
        ((1 - ϑ) * p k - c₀'))) atTop (𝓝 0) := by
      rw [← ENNReal.ofReal_zero]
      apply ENNReal.tendsto_ofReal
      set α : ℝ := 2 * c / lam with hα
      set β : ℝ := 2 * c / lam + c + 2 with hβ
      have hα0 : 0 < α := by rw [hα]; positivity
      have hβ0 : 0 < β := by rw [hβ]; positivity
      obtain ⟨κ', hκ'⟩ : ∃ κ' : ℝ, κ' = |c₀| + m * (Nat.clog 2 Next : ℝ) +
          2 * Real.logb 2 ((m : ℝ) + 1) + (cext : ℝ) := ⟨_, rfl⟩
      have hκ'0 : 0 ≤ κ' := by
        rw [hκ']
        have := Real.logb_nonneg one_lt_two
          (show (1 : ℝ) ≤ m + 1 by linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)])
        positivity
      have hy : Tendsto (fun k : ℕ ↦ α * p k + β) atTop atTop :=
        tendsto_atTop_add_const_right atTop β
          ((tendsto_natCast_atTop_atTop.comp hptend).const_mul_atTop hα0)
      have hlog0 : Tendsto (fun k : ℕ ↦ Real.log (α * p k + β) / ((1 - ϑ) * p k - c₀')) atTop
          (𝓝 0) := by
        have hden : ∀ k : ℕ, (1 - ϑ) / α * (α * p k + β) + (-c₀' - (1 - ϑ) / α * β) =
            (1 - ϑ) * p k - c₀' := by
          intro k
          field_simp
          ring
        have h1 := (Real.tendsto_pow_log_div_mul_add_atTop ((1 - ϑ) / α) (-c₀' - (1 - ϑ) / α * β)
          1 (div_pos hϑ1 hα0).ne').comp hy
        refine h1.congr fun k ↦ ?_
        simp only [Function.comp, pow_one, hden]
      have hlogb0 : Tendsto (fun k : ℕ ↦ Real.logb 2 (α * p k + β) / ((1 - ϑ) * p k - c₀'))
          atTop (𝓝 0) := by
        have := hlog0.div_const (Real.log 2)
        rw [zero_div] at this
        refine this.congr fun k ↦ ?_
        rw [Real.logb, div_right_comm]
      have hconst : Tendsto (fun k : ℕ ↦ κ' / ((1 - ϑ) * p k - c₀')) atTop (𝓝 0) :=
        tendsto_const_nhds.div_atTop hd₀
      have hupper : Tendsto (fun k : ℕ ↦ (6 * Real.logb 2 (α * p k + β) + κ') /
          ((1 - ϑ) * p k - c₀')) atTop (𝓝 0) := by
        have := (hlogb0.const_mul 6).add hconst
        rw [mul_zero, add_zero] at this
        refine this.congr fun k ↦ ?_
        ring
      have hbnd : ∀ᶠ k in atTop, (Tp k : ℝ) + 1 ≤ α * p k + β ∧ (Tm (p k) : ℝ) + 1 ≤ α * p k + β ∧
          (n k : ℝ) + 1 + 1 ≤ α * p k + β := by
        filter_upwards [hev] with k hk
        obtain ⟨hkN, hkK, -, -, -, -, -⟩ := hk
        obtain ⟨-, -, hp3⟩ := hpk k hkN
        obtain ⟨-, hTp2, -⟩ := hTpf k hkK
        obtain ⟨hTm1, hTm2, -⟩ := hTm (p k)
        have hn2p : (n k : ℝ) ≤ 2 * (p k + 1) / lam := by rw [le_div_iff₀ hlam]; linarith
        have h1 : 2 * ((p k : ℝ) + 1) / lam ≤ α * p k + 2 * c / lam := by
          rw [hα]
          have : 2 * ((p k : ℝ) + 1) / lam = 2 / lam * p k + 2 / lam := by ring
          rw [this]
          have h2 : 2 / lam * (p k : ℝ) ≤ 2 * c / lam * p k := by
            apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
            apply div_le_div_of_nonneg_right _ hlam.le
            linarith
          have h3 : 2 / lam ≤ 2 * c / lam := by
            apply div_le_div_of_nonneg_right _ hlam.le
            linarith
          linarith
        have h4 : c * (2 * (p k : ℝ) / lam + 1) = α * p k + c := by rw [hα]; ring
        have h5 : c * (nm (p k) : ℝ) ≤ c * (2 * p k / lam + 1) :=
          mul_le_mul_of_nonneg_left (hnmb (p k)) hc0.le
        have h6 : 0 ≤ 2 * c / lam := by positivity
        refine ⟨?_, ?_, ?_⟩
        · rw [hβ]; linarith only [hTp2, hn2p, h1]
        · rw [hβ]; linarith only [hTm2, h5, h4, h6]
        · rw [hβ]; linarith only [hn2p, h1, hc0]
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper ?_ ?_
      · filter_upwards [hd₀.eventually_gt_atTop 0] with k hd
        apply div_nonneg _ hd.le
        have h1 : 0 ≤ Real.logb 2 ((Tp k : ℝ) + 1) :=
          Real.logb_nonneg one_lt_two (by linarith [(Nat.cast_nonneg (Tp k) : (0 : ℝ) ≤ Tp k)])
        have h2 : 0 ≤ Real.logb 2 ((Tm (p k) : ℝ) + 1) :=
          Real.logb_nonneg one_lt_two
            (by linarith [(Nat.cast_nonneg (Tm (p k)) : (0 : ℝ) ≤ Tm (p k))])
        have h3 : 0 ≤ Real.logb 2 ((n k : ℝ) + 1 + 1) :=
          Real.logb_nonneg one_lt_two (by linarith [(Nat.cast_nonneg (n k) : (0 : ℝ) ≤ n k)])
        linarith only [h1, h2, h3, hκ'0, hκ']
      · filter_upwards [hd₀.eventually_gt_atTop 0, hbnd] with k hd hb
        obtain ⟨hb1, hb2, hb3⟩ := hb
        apply div_le_div_of_nonneg_right _ hd.le
        have h1 : Real.logb 2 ((Tp k : ℝ) + 1) ≤ Real.logb 2 (α * p k + β) :=
          Real.logb_le_logb_of_le one_lt_two (by positivity) hb1
        have h2 : Real.logb 2 ((Tm (p k) : ℝ) + 1) ≤ Real.logb 2 (α * p k + β) :=
          Real.logb_le_logb_of_le one_lt_two (by positivity) hb2
        have h3 : Real.logb 2 ((n k : ℝ) + 1 + 1) ≤ Real.logb 2 (α * p k + β) :=
          Real.logb_le_logb_of_le one_lt_two (by positivity) hb3
        linarith only [h1, h2, h3, hκ']
    -- the two limits
    have hlimp : limsup (fun k ↦ w (n k)) atTop ≤ (1 + η₁ (q + 1)) * d₁ :=
      le_of_eq_of_le hwn.limsup_eq hliminf_w
    have hlimm : limsup (fun k ↦ centeredBSCost P T₂ u₂ A x (Tm (p k) + 1) (dyadicRadius q))
        atTop ≤ (1 + η₂ q) * D₂ := by
      refine le_trans (limsup_comp_le_of_tendsto_atTop
        (u := fun n ↦ centeredBSCost P T₂ u₂ A x n (dyadicRadius q))
        ((tendsto_add_atTop_nat 1).comp (hTmtend.comp hptend))) ?_
      exact hbs₂ q hq₂
    -- assemble
    refine hzx.trans (add_le_add le_rfl ?_)
    calc (staticPointDimensions P A z).1
        ≤ liminf (fun k ↦ normalizedPrecisionComplexity P A z (δ k)) atTop :=
          liminf_nhdsWithin_le_liminf_seq hδpos hδ0
      _ ≤ limsup (fun k ↦ normalizedPrecisionComplexity P A z (δ k)) atTop := liminf_le_limsup
      _ ≤ limsup ((fun k ↦ ENNReal.ofReal M₁ * w (n k) +
            ENNReal.ofReal M₂ * centeredBSCost P T₂ u₂ A x (Tm (p k) + 1) (dyadicRadius q)) +
            fun k ↦ ENNReal.ofReal ((2 * Real.logb 2 ((Tp k : ℝ) + 1) +
              2 * Real.logb 2 ((Tm (p k) : ℝ) + 1) + |c₀| + m * (Nat.clog 2 Next : ℝ) +
              2 * Real.logb 2 ((n k : ℝ) + 1 + 1) + 2 * Real.logb 2 ((m : ℝ) + 1) + (cext : ℝ)) /
              ((1 - ϑ) * p k - c₀'))) atTop :=
          limsup_le_limsup hpt
      _ = limsup ((fun k ↦ ENNReal.ofReal M₁ * w (n k)) + fun k ↦ ENNReal.ofReal M₂ *
            centeredBSCost P T₂ u₂ A x (Tm (p k) + 1) (dyadicRadius q)) atTop :=
          ENNReal.limsup_add_of_right_tendsto_zero he _
      _ ≤ limsup (fun k ↦ ENNReal.ofReal M₁ * w (n k)) atTop +
          limsup (fun k ↦ ENNReal.ofReal M₂ *
            centeredBSCost P T₂ u₂ A x (Tm (p k) + 1) (dyadicRadius q)) atTop :=
          ennreal_limsup_add_le _ _
      _ = ENNReal.ofReal M₁ * limsup (fun k ↦ w (n k)) atTop +
          ENNReal.ofReal M₂ *
            limsup (fun k ↦ centeredBSCost P T₂ u₂ A x (Tm (p k) + 1) (dyadicRadius q)) atTop := by
          rw [ENNReal.limsup_const_mul_of_ne_top ENNReal.ofReal_ne_top,
            ENNReal.limsup_const_mul_of_ne_top ENNReal.ofReal_ne_top]
      _ ≤ ENNReal.ofReal M₁ * ((1 + η₁ (q + 1)) * d₁) + ENNReal.ofReal M₂ * ((1 + η₂ q) * D₂) := by
          gcongr
  /- Claim B: a single multiplicative loss `κ > 1`. -/
  have claimB : ∀ κ : ℝ, 1 < κ → (staticPointDimensions P A x).1 ≤
      1 + ENNReal.ofReal κ * (d₁ + D₂) := by
    intro κ hκ
    set r : ℝ := Real.sqrt κ with hr
    have hr1 : 1 < r := by
      rw [hr, Real.lt_sqrt zero_le_one]
      linarith
    have hr0 : 0 < r := by linarith
    have hrr : r * r = κ := Real.mul_self_sqrt (by linarith)
    set t₀ : ℝ := min 1 (min (lam / 4) (min (lam / (2 * (1 + M)))
      ((r - 1) * lam / (2 * (1 + M) * (1 + r) + 2)))) with ht₀
    have ht₀pos : 0 < t₀ := by
      rw [ht₀]
      refine lt_min one_pos (lt_min (by positivity) (lt_min (by positivity)
        (div_pos (mul_pos (by linarith) hlam) (by positivity))))
    obtain ⟨ρ, hρ0, hρt⟩ := exists_rat_btwn ht₀pos
    have hρ' : (0 : ℝ) < ρ := by exact_mod_cast hρ0
    have hρ0' : (0 : ℚ) < ρ := by exact_mod_cast hρ0
    have hρ1 : (ρ : ℝ) ≤ 1 := hρt.le.trans (min_le_left _ _)
    have hρ4 : (ρ : ℝ) < lam / 4 := hρt.trans_le ((min_le_right _ _).trans (min_le_left _ _))
    have hρM : (ρ : ℝ) < lam / (2 * (1 + M)) :=
      hρt.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
    have hρr : (ρ : ℝ) < (r - 1) * lam / (2 * (1 + M) * (1 + r) + 2) :=
      hρt.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
    have hρρ : (ρ : ℝ) * ρ ≤ ρ := mul_le_of_le_one_left hρ'.le hρ1
    have hA1 : (ρ : ℝ) * (2 * (1 + M) * (1 + r) + 2) < (r - 1) * lam := by
      rw [lt_div_iff₀ (by positivity)] at hρr
      linarith
    have hA2 : (ρ : ℝ) * (2 * (1 + M)) < lam := by
      rw [lt_div_iff₀ (by positivity)] at hρM
      linarith
    have hc : 1 < 1 + (ρ : ℝ) := by linarith
    have hc1 : (1 + (ρ : ℝ)) - 1 = ρ := add_sub_cancel_left 1 (ρ : ℝ)
    have hρlam : (ρ : ℝ) < lam / 2 := by linarith
    have hMρ : 0 ≤ M * ρ := by positivity
    have hrρρ : r * (ρ * ρ) ≤ r * ρ := mul_le_mul_of_nonneg_left hρρ hr0.le
    have hϑ : 2 * ((ρ : ℝ) + M) * ((1 + (ρ : ℝ)) - 1) < lam := by
      rw [hc1]
      linarith only [hA2, hρρ]
    have hϑ1 : 0 < 1 - 2 * ((ρ : ℝ) + M) * ((1 + (ρ : ℝ)) - 1) / lam := by
      rw [sub_pos, div_lt_one hlam]; exact hϑ
    have hM₁ : (1 + 2 * (ρ : ℝ) / lam) / (1 - 2 * ((ρ : ℝ) + M) * ((1 + (ρ : ℝ)) - 1) / lam) <
        r := by
      rw [div_lt_iff₀ hϑ1, hc1]
      have e : r * (1 - 2 * ((ρ : ℝ) + M) * ρ / lam) - (1 + 2 * (ρ : ℝ) / lam) =
          (r * lam - 2 * r * (ρ * ρ) - 2 * r * (M * ρ) - lam - 2 * ρ) / lam := by
        field_simp
        ring
      have : 0 < r * (1 - 2 * ((ρ : ℝ) + M) * ρ / lam) - (1 + 2 * (ρ : ℝ) / lam) := by
        rw [e]
        apply div_pos _ hlam
        linarith only [hA1, hrρρ, hMρ, hρ']
      linarith only [this]
    have hM₂ : (1 + 2 * ((ρ : ℝ) + M * ((1 + (ρ : ℝ)) - 1)) / lam) /
        (1 - 2 * ((ρ : ℝ) + M) * ((1 + (ρ : ℝ)) - 1) / lam) < r := by
      rw [div_lt_iff₀ hϑ1, hc1]
      have e : r * (1 - 2 * ((ρ : ℝ) + M) * ρ / lam) - (1 + 2 * ((ρ : ℝ) + M * ρ) / lam) =
          (r * lam - 2 * r * (ρ * ρ) - 2 * r * (M * ρ) - lam - 2 * ρ - 2 * (M * ρ)) / lam := by
        field_simp
        ring
      have : 0 < r * (1 - 2 * ((ρ : ℝ) + M) * ρ / lam) - (1 + 2 * ((ρ : ℝ) + M * ρ) / lam) := by
        rw [e]
        apply div_pos _ hlam
        linarith only [hA1, hrρρ, hρ']
      linarith only [this]
    obtain ⟨q₀, hq₀⟩ := claimA (1 + ρ) hc ρ hρ0' hρlam hϑ r r hM₁ hM₂
    have hη₁' := (ENNReal.tendsto_nhds_zero.1 hη₁) (ENNReal.ofReal (r - 1))
      (ENNReal.ofReal_pos.2 (by linarith))
    have hη₂' := (ENNReal.tendsto_nhds_zero.1 hη₂) (ENNReal.ofReal (r - 1))
      (ENNReal.ofReal_pos.2 (by linarith))
    obtain ⟨q, hq, hq1, hq2⟩ :=
      ((eventually_ge_atTop q₀).and (((tendsto_add_atTop_nat 1).eventually hη₁').and hη₂')).exists
    have e1 : (1 : ℝ≥0∞) + ENNReal.ofReal (r - 1) = ENNReal.ofReal r := by
      rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_add zero_le_one (by linarith)]
      congr 1
      ring
    have h1 : 1 + η₁ (q + 1) ≤ ENNReal.ofReal r := by rw [← e1]; exact add_le_add le_rfl hq1
    have h2 : 1 + η₂ q ≤ ENNReal.ofReal r := by rw [← e1]; exact add_le_add le_rfl hq2
    calc (staticPointDimensions P A x).1
        ≤ 1 + (ENNReal.ofReal r * ((1 + η₁ (q + 1)) * d₁) +
            ENNReal.ofReal r * ((1 + η₂ q) * D₂)) :=
          hq₀ q hq
      _ ≤ 1 + (ENNReal.ofReal r * (ENNReal.ofReal r * d₁) +
          ENNReal.ofReal r * (ENNReal.ofReal r * D₂)) := by
          gcongr
      _ = 1 + ENNReal.ofReal (r * r) * (d₁ + D₂) := by
          rw [ENNReal.ofReal_mul hr0.le]
          ring
      _ = 1 + ENNReal.ofReal κ * (d₁ + D₂) := by rw [hrr]
  /- Claim C: let `κ → 1`. -/
  by_cases htop : d₁ + D₂ = ⊤
  · rw [htop, add_top]; exact le_top
  · have h1 : Tendsto (fun κ : ℝ ↦ ENNReal.ofReal κ) (𝓝[>] (1 : ℝ)) (𝓝 1) := by
      have := ENNReal.tendsto_ofReal (tendsto_id (x := 𝓝 (1 : ℝ)))
      rw [ENNReal.ofReal_one] at this
      exact this.mono_left nhdsWithin_le_nhds
    have hlim : Tendsto (fun κ : ℝ ↦ 1 + ENNReal.ofReal κ * (d₁ + D₂)) (𝓝[>] (1 : ℝ))
        (𝓝 (1 + (d₁ + D₂))) := by
      have := ENNReal.Tendsto.mul_const h1 (Or.inl one_ne_zero) (b := d₁ + D₂)
      rw [one_mul] at this
      exact tendsto_const_nhds.add this
    exact ge_of_tendsto hlim (eventually_nhdsWithin_of_forall fun κ hκ ↦ claimB κ hκ)

/-- Lower dimension, mixed bound (Hausdorff side, with the flow coordinate restored):
`dim^A(x) ≤ 1 + min (dim^A_BS(x,f,u⁺) + Dim^A_BS(x,f⁻¹,u⁻), Dim^A_BS(x,f,u⁺) + dim^A_BS(x,f⁻¹,u⁻))`.
Proof for the first term (`mixed_core`): for each parameter the interface gives a shifted
section point `z = φ t₀ x` with `dim x ≤ 1 + dim z` (`flow_coordinate`); choose `n_k` realizing
the forward `liminf`, set `p_k = ⌊S_{n_k} u⁺(x) - ρ n_k⌋`, take the forward return in
`[n_k / c, n_k + c]` by controlled returns and pad the orbit description by the constant `⌈c⌉₊`
steps (`orbit_extension`, Chapter A), `Tm_k` from the backward stopping time; use
`liminf_nhdsWithin_le_liminf_seq`, `liminf ≤ limsup`, the denominator swap, and let `q → ∞`,
`ρ → 0`, `c → 1`. Requires `A` to represent `f` (for the padding search), hence the hypotheses
`hP`, `hf`. Blueprint nodes `geo:section-point-mixed`, `geo:flow-coordinate`. -/
theorem sectionPoint_mixed {B : Set ℕ} (E : EffectiveGeodesicData G P B)
    (hBA : charOracle B ≤ᵀ charOracle A) (hA : OrbitToLocationEstimate G P A)
    (hP : ComputablePresentationIn P A)
    (hf : IsRepresentedMapIn P P A G.f) (hfinv : IsRepresentedMapIn P P A G.finv) {x : X}
    (hx : G.ControlledReturns x) (hpos : G.PositiveRates x) :
    (staticPointDimensions P A x).1 ≤
      1 + min ((pointwiseBSDimension P G.f G.uPlus A x).1 +
          (pointwiseBSDimension P G.finv G.uMinus A x).2)
        ((pointwiseBSDimension P G.f G.uPlus A x).2 +
          (pointwiseBSDimension P G.finv G.uMinus A x).1) := by
  have hest := hA x hx.mem_Reg
  obtain ⟨cpair, hpair⟩ := oraclePairComplexity_le_log A
  obtain ⟨hu, hu0, huM⟩ := G.uPlus_props
  obtain ⟨hv, hv0, hvM⟩ := G.uMinus_props
  have hx' : ∀ c : ℝ, 1 < c → ∃ Pp Pm : Set X, IsCompact Pp ∧ Pp ⊆ G.Reg ∧ IsCompact Pm ∧
      Pm ⊆ G.Reg ∧ ∃ K : ℕ, ∀ n : ℕ, K < n →
        (∃ T : ℕ, n ≤ T ∧ (T : ℝ) ≤ c * n ∧ G.φ ((fun t : ℝ ↦ t) T) x ∈ Pp) ∧
        (∃ T : ℕ, n ≤ T ∧ (T : ℝ) ≤ c * n ∧ G.φ ((fun t : ℝ ↦ -t) T) x ∈ Pm) := hx
  rw [← min_add_add_left]
  refine le_min ?_ ?_
  · refine mixed_core P G.continuous_f G.continuous_finv hu hv hu0 hv0 huM hvM hP hf hpos.1
      hpos.2 (σ₁ := fun t : ℝ ↦ t) (σ₂ := fun t : ℝ ↦ -t) hx' ?_
    intro P₁ P₂ h1 h2 h3 h4 ρ hρ
    obtain ⟨t₀, ht₀, ε, hε, C, hC, c₀, hch⟩ := hest P₁ P₂ h1 h2 h3 h4 ρ hρ
    refine ⟨G.φ t₀ x, (E.flow_coordinate P hBA ht₀).2, ε, hε, C, hC, c₀ + cpair,
      fun n₁ n₂ hn₁ hn₂ ↦ ?_⟩
    have h := hch n₁ n₂ hn₁ hn₂
    rw [G.combinedScale_eq] at h
    have h' : ((precisionComplexityNat P A (G.φ t₀ x) (C * (2 : ℝ) ^
        (-min (birkhoffSum G.f G.uPlus n₁ x - ρ * n₁)
          (birkhoffSum G.finv G.uMinus n₂ x - ρ * n₂))) : ℕ) : ℝ) ≤
        (orbitComplexityNat P G.f A x (n₁ + 1) ε : ℝ) +
          orbitComplexityNat P G.finv A x (n₂ + 1) ε + oraclePairComplexity A n₁ n₂ + c₀ := by
      exact_mod_cast h
    linarith [hpair n₁ n₂]
  · rw [add_comm (pointwiseBSDimension P G.f G.uPlus A x).2]
    refine mixed_core (G := G) P G.continuous_finv G.continuous_f hv hu hv0 hu0 hvM huM hP hfinv
      hpos.2 hpos.1 (σ₁ := fun t : ℝ ↦ -t) (σ₂ := fun t : ℝ ↦ t) ?_ ?_
    · intro c hc
      obtain ⟨Pp, Pm, h1, h2, h3, h4, K, hK⟩ := hx' c hc
      exact ⟨Pm, Pp, h3, h4, h1, h2, K, fun n hn ↦ ⟨(hK n hn).2, (hK n hn).1⟩⟩
    · intro P₁ P₂ h1 h2 h3 h4 ρ hρ
      obtain ⟨t₀, ht₀, ε, hε, C, hC, c₀, hch⟩ := hest P₂ P₁ h3 h4 h1 h2 ρ hρ
      refine ⟨G.φ t₀ x, (E.flow_coordinate P hBA ht₀).2, ε, hε, C, hC, c₀ + cpair,
        fun n₁ n₂ hn₁ hn₂ ↦ ?_⟩
      have h := hch n₂ n₁ hn₂ hn₁
      rw [G.combinedScale_eq, min_comm] at h
      have h' : ((precisionComplexityNat P A (G.φ t₀ x) (C * (2 : ℝ) ^
          (-min (birkhoffSum G.finv G.uMinus n₁ x - ρ * n₁)
            (birkhoffSum G.f G.uPlus n₂ x - ρ * n₂))) : ℕ) : ℝ) ≤
          (orbitComplexityNat P G.f A x (n₂ + 1) ε : ℝ) +
            orbitComplexityNat P G.finv A x (n₁ + 1) ε + oraclePairComplexity A n₂ n₁ + c₀ := by
        exact_mod_cast h
      linarith [hpair n₂ n₁]

end limits

end Kolmogorov.PointToSet
