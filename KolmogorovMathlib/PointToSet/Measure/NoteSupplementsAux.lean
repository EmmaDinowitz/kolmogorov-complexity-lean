/-
Copyright (c) 2026 Emma Dinowitz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emma Dinowitz
-/
import KolmogorovMathlib.PointToSet.Measure.ProbabilityRate
import KolmogorovMathlib.PointToSet.Measure.ShiftProduct

/-!
# Supplements to the note: rates in probability of two-component product mixtures

Auxiliary material for the §6.2 sentence on Example 6.8 of E. Dinowitz, *Entropy of non-invariant
measures and orbit complexity of random points* (stated in `NoteSupplementsLate.lean`). It does
not import `ShiftBernoulli.lean`.

* `noteSupp_Tracks g A x`: `g n x` is eventually finite and `(g n x).toReal - A n → 0`.
* `noteSupp_lowerProbRate_eq_of_tracks`, `noteSupp_upperProbRate_eq_of_tracks`: for a mixture
  `μ = w₁ ν₁ + w₂ ν₂` whose components are tracked `ν_i`-a.s. by sequences `A_i`, the rates in
  probability `sup {α : μ{g_n < α} → 0}` and `inf {β : μ{g_n > β} → 0}` are the common lower
  (upper) limit `c` of the `A_i`, as soon as a component of positive weight approaches `c`
  infinitely often. Almost sure convergence gives convergence in probability on each component,
  and a subsequence along which a component of positive weight sits at the wrong side keeps
  `μ{g_n < α}` (resp. `μ{g_n > β}`) away from `0`.
* `noteSupp_tracks_productMixture`: for `μ = t μ_{β₁} + s μ_{β₂}` (`t > 0`, `t + s ≤ 1`, product
  Bernoulli measures with biases in `[δ, 1 - δ]`), `μ_{β₁}`-a.s. at every scale `2^{-q}`,
  `-(1/n) log₂ μ(B_n(x, σ, 2^{-q}))` tracks `(1/(n+q)) ∑_{i<n+q} H(β₁ i)`. The upper bound uses
  `μ ≥ t μ_{β₁}`, the lower bound Lemma 7.1 (`ae_eventually_measure_bowenBall_le`) in the form
  `μ_{β₂}[x↾n] ≤ (n²/δ) μ_{β₁}[x↾n]`, and the strong law `ae_tendsto_symbolInfo_sub`; no
  singularity `μ_{β₁} ⊥ μ_{β₂}` is used.

Blueprint node `meas:probability-rate`.
-/

namespace Kolmogorov.PointToSet

open Filter Set MeasureTheory
open scoped Topology ENNReal unitInterval

/-! ### Rates in probability from almost sure tracking -/

section probRate

variable {X : Type*}

/-- `g n x` tracks the real sequence `A`: `g n x` is eventually finite and
`(g n x).toReal - A n → 0`. -/
def noteSupp_Tracks (g : ℕ → X → ℝ≥0∞) (A : ℕ → ℝ) (x : X) : Prop :=
  Tendsto (fun n ↦ (g n x).toReal - A n) atTop (𝓝 0) ∧ ∀ᶠ n in atTop, g n x ≠ ⊤

/-- Tracking gives two-sided bounds: eventually `ofReal (A n - ε) ≤ g n x ≤ ofReal (A n + ε)`. -/
lemma noteSupp_Tracks.eventually_bounds {g : ℕ → X → ℝ≥0∞} {A : ℕ → ℝ} {x : X}
    (h : noteSupp_Tracks g A x) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ENNReal.ofReal (A n - ε) ≤ g n x ∧ g n x ≤ ENNReal.ofReal (A n + ε) := by
  filter_upwards [h.1.eventually (Metric.ball_mem_nhds 0 hε), h.2] with n hn hne
  rw [Real.dist_eq, sub_zero, abs_lt] at hn
  rw [← ENNReal.ofReal_toReal hne]
  exact ⟨ENNReal.ofReal_le_ofReal (by linarith), ENNReal.ofReal_le_ofReal (by linarith)⟩

variable [MeasurableSpace X]

/-- If almost every point eventually leaves the measurable sets `s n`, then their measures tend
to `0` (finite measure). -/
lemma noteSupp_tendsto_measure_zero {μ : Measure X} [IsFiniteMeasure μ] {s : ℕ → Set X}
    (hs : ∀ n, MeasurableSet (s n)) (h : ∀ᵐ x ∂μ, ∀ᶠ n in atTop, x ∉ s n) :
    Tendsto (fun n ↦ μ (s n)) atTop (𝓝 0) :=
  tendsto_measure_zero_of_ae_eventually hs h

/-- If a component `w ν ≤ μ` with `w ≠ 0` has almost every point eventually inside the sets
`s (φ k)` along a subsequence, the measures `μ (s n)` do not tend to `0`. -/
lemma noteSupp_not_tendsto_measure_zero {μ ν : Measure X} [IsProbabilityMeasure ν] {w : ℝ≥0∞}
    (hw : w ≠ 0) (hle : ∀ s, w * ν s ≤ μ s) {s : ℕ → Set X} (hs : ∀ n, MeasurableSet (s n))
    {φ : ℕ → ℕ} (hφ : StrictMono φ) (h : ∀ᵐ x ∂ν, ∀ᶠ k in atTop, x ∈ s (φ k)) :
    ¬ Tendsto (fun n ↦ μ (s n)) atTop (𝓝 0) := by
  intro ht
  have h0 : Tendsto (fun k ↦ ν (s (φ k))ᶜ) atTop (𝓝 0) :=
    noteSupp_tendsto_measure_zero (fun k ↦ (hs (φ k)).compl)
      (h.mono fun x hx ↦ hx.mono fun k hk hk' ↦ hk' hk)
  have h1 : Tendsto (fun k ↦ ν (s (φ k))) atTop (𝓝 1) := by
    have : ∀ k, ν (s (φ k)) = 1 - ν (s (φ k))ᶜ := fun k ↦ by
      rw [prob_compl_eq_one_sub (hs (φ k)), ENNReal.sub_sub_cancel ENNReal.one_ne_top prob_le_one]
    simp_rw [this]
    simpa using ENNReal.Tendsto.sub tendsto_const_nhds h0 (Or.inl ENNReal.one_ne_top)
  have h2 : Tendsto (fun k ↦ w * ν (s (φ k))) atTop (𝓝 (w * 1)) :=
    ENNReal.Tendsto.const_mul h1 (Or.inl one_ne_zero)
  have h3 : Tendsto (fun k ↦ μ (s (φ k))) atTop (𝓝 0) := ht.comp hφ.tendsto_atTop
  have h4 : w * 1 ≤ 0 := le_of_tendsto_of_tendsto' h2 h3 fun k ↦ hle _
  rw [mul_one, nonpos_iff_eq_zero] at h4
  exact hw h4

/-- Almost sure statements for both components hold for the mixture. -/
lemma noteSupp_ae_mixture {ν₁ ν₂ : Measure X} {w₁ w₂ : ℝ≥0∞} {p : X → Prop}
    (h₁ : ∀ᵐ x ∂ν₁, p x) (h₂ : ∀ᵐ x ∂ν₂, p x) : ∀ᵐ x ∂(w₁ • ν₁ + w₂ • ν₂), p x :=
  ae_add_measure_iff.2 ⟨Measure.smul_absolutelyContinuous.ae_le h₁,
    Measure.smul_absolutelyContinuous.ae_le h₂⟩

/-- The first component of a mixture is dominated by it. -/
lemma noteSupp_le_mixture_left (ν₁ ν₂ : Measure X) (w₁ w₂ : ℝ≥0∞) (s : Set X) :
    w₁ * ν₁ s ≤ (w₁ • ν₁ + w₂ • ν₂) s := by
  simp only [Measure.add_apply, Measure.smul_apply, smul_eq_mul]
  exact le_self_add

/-- The second component of a mixture is dominated by it. -/
lemma noteSupp_le_mixture_right (ν₁ ν₂ : Measure X) (w₁ w₂ : ℝ≥0∞) (s : Set X) :
    w₂ * ν₂ s ≤ (w₁ • ν₁ + w₂ • ν₂) s := by
  simp only [Measure.add_apply, Measure.smul_apply, smul_eq_mul]
  exact le_add_self

/-- A real number strictly between `c` and a level `α > ofReal c`. -/
lemma noteSupp_exists_real_btwn {c : ℝ} {α : ℝ≥0∞} (h : ENNReal.ofReal c < α) :
    ∃ r : ℝ, c < r ∧ ENNReal.ofReal r < α := by
  rcases eq_or_ne α ⊤ with rfl | hαt
  · exact ⟨c + 1, by linarith, ENNReal.ofReal_lt_top⟩
  · obtain ⟨a, rfl⟩ : ∃ a : ℝ, α = ENNReal.ofReal a := ⟨α.toReal, (ENNReal.ofReal_toReal hαt).symm⟩
    rw [ENNReal.ofReal_lt_ofReal_iff'] at h
    refine ⟨(c + a) / 2, by linarith [h.1], ?_⟩
    rw [ENNReal.ofReal_lt_ofReal_iff']
    exact ⟨by linarith [h.1], h.2⟩

/-- Lower rate, upper bound: a tracked component of positive weight whose target is
infinitely often below `c + ε` makes `μ{g_n < α}` not tend to `0` for every `α > c`. -/
lemma noteSupp_not_tendsto_lt {μ ν : Measure X} [IsProbabilityMeasure ν] {w : ℝ≥0∞}
    (hw : w ≠ 0) (hle : ∀ s, w * ν s ≤ μ s) {g : ℕ → X → ℝ≥0∞} (hg : ∀ n, Measurable (g n))
    {A : ℕ → ℝ} (h : ∀ᵐ x ∂ν, noteSupp_Tracks g A x) {c : ℝ}
    (hf : ∀ ε > 0, ∃ᶠ n in atTop, A n < c + ε) {α : ℝ≥0∞} (hα : ENNReal.ofReal c < α) :
    ¬ Tendsto (fun n ↦ μ {x | g n x < α}) atTop (𝓝 0) := by
  obtain ⟨r, hcr, hrα⟩ := noteSupp_exists_real_btwn hα
  have hε : 0 < (r - c) / 2 := by linarith
  obtain ⟨φ, hφ, hφA⟩ := Filter.extraction_of_frequently_atTop (hf _ hε)
  refine noteSupp_not_tendsto_measure_zero hw hle (fun n ↦ measurableSet_lt (hg n)
    measurable_const) hφ (h.mono fun x hx ↦ ?_)
  filter_upwards [hφ.tendsto_atTop.eventually (hx.eventually_bounds hε)] with k hk
  refine lt_of_le_of_lt hk.2 (lt_of_le_of_lt (ENNReal.ofReal_le_ofReal ?_) hrα)
  linarith [hφA k]

/-- Upper rate, lower bound: a tracked component of positive weight whose target is
infinitely often above `C - ε` makes `μ{β < g_n}` not tend to `0` for every `β < C`. -/
lemma noteSupp_not_tendsto_gt {μ ν : Measure X} [IsProbabilityMeasure ν] {w : ℝ≥0∞}
    (hw : w ≠ 0) (hle : ∀ s, w * ν s ≤ μ s) {g : ℕ → X → ℝ≥0∞} (hg : ∀ n, Measurable (g n))
    {A : ℕ → ℝ} (h : ∀ᵐ x ∂ν, noteSupp_Tracks g A x) {C : ℝ}
    (hf : ∀ ε > 0, ∃ᶠ n in atTop, C - ε < A n) {β : ℝ≥0∞} (hβ : β < ENNReal.ofReal C) :
    ¬ Tendsto (fun n ↦ μ {x | β < g n x}) atTop (𝓝 0) := by
  have hβt : β ≠ ⊤ := ne_top_of_lt hβ
  have hb : β.toReal < C := ENNReal.toReal_lt_of_lt_ofReal hβ
  have hε : 0 < (C - β.toReal) / 3 := by linarith
  obtain ⟨φ, hφ, hφA⟩ := Filter.extraction_of_frequently_atTop (hf _ hε)
  refine noteSupp_not_tendsto_measure_zero hw hle (fun n ↦ measurableSet_lt measurable_const
    (hg n)) hφ (h.mono fun x hx ↦ ?_)
  filter_upwards [hφ.tendsto_atTop.eventually (hx.eventually_bounds hε)] with k hk
  have := hφA k
  have h0 := ENNReal.toReal_nonneg (a := β)
  exact ((ENNReal.ofReal_toReal hβt).symm.trans_lt
    (ENNReal.ofReal_lt_ofReal_iff'.2 ⟨by linarith, by linarith⟩)).trans_le hk.1

/-- **Lower rate in probability of a tracked mixture.** Let `μ = w₁ ν₁ + w₂ ν₂` and suppose
that `g n` tracks `A_i` `ν_i`-almost surely. If eventually `A_1 n, A_2 n > c - ε` for every
`ε > 0`, and some component of positive weight has `A_i n < c + ε` infinitely often, then the
lower rate in probability `sup {α : μ{g_n < α} → 0}` is `c`. -/
theorem noteSupp_lowerProbRate_eq_of_tracks [MetricSpace X] [BorelSpace X] {ν₁ ν₂ : Measure X}
    [IsProbabilityMeasure ν₁] [IsProbabilityMeasure ν₂] {w₁ w₂ : ℝ≥0∞}
    [IsFiniteMeasure (w₁ • ν₁ + w₂ • ν₂)]
    {g : ℕ → X → ℝ≥0∞} (hg : ∀ n, Measurable (g n)) {A₁ A₂ : ℕ → ℝ}
    (h₁ : ∀ᵐ x ∂ν₁, noteSupp_Tracks g A₁ x) (h₂ : ∀ᵐ x ∂ν₂, noteSupp_Tracks g A₂ x) {c : ℝ}
    (hlow : ∀ ε > 0, ∀ᶠ n in atTop, c - ε < A₁ n ∧ c - ε < A₂ n)
    (hfreq : (w₁ ≠ 0 ∧ ∀ ε > 0, ∃ᶠ n in atTop, A₁ n < c + ε) ∨
      (w₂ ≠ 0 ∧ ∀ ε > 0, ∃ᶠ n in atTop, A₂ n < c + ε)) :
    lowerProbRate (w₁ • ν₁ + w₂ • ν₂) g = ENNReal.ofReal c := by
  refine le_antisymm (sSup_le fun α hα ↦ ?_)
    (le_of_forall_lt_imp_le_of_dense fun α hα ↦ le_sSup ?_)
  · by_contra hlt
    rw [not_le] at hlt
    rcases hfreq with ⟨hw, hf⟩ | ⟨hw, hf⟩
    · exact noteSupp_not_tendsto_lt hw (noteSupp_le_mixture_left ν₁ ν₂ w₁ w₂) hg h₁ hf hlt hα
    · exact noteSupp_not_tendsto_lt hw (noteSupp_le_mixture_right ν₁ ν₂ w₁ w₂) hg h₂ hf hlt hα
  · have hαt : α ≠ ⊤ := ne_top_of_lt hα
    have ha : α.toReal < c := ENNReal.toReal_lt_of_lt_ofReal hα
    have hε : 0 < (c - α.toReal) / 2 := by linarith
    have key : ∀ (A : ℕ → ℝ) (x : X), noteSupp_Tracks g A x →
        (∀ᶠ n in atTop, c - (c - α.toReal) / 2 < A n) →
          ∀ᶠ n in atTop, x ∉ {x | g n x < α} := by
      intro A x hx hA
      filter_upwards [hx.eventually_bounds hε, hA] with n hn hAn
      simp only [not_lt]
      exact ((ENNReal.ofReal_toReal hαt).symm.trans_le
        (ENNReal.ofReal_le_ofReal (by linarith))).trans hn.1
    refine noteSupp_tendsto_measure_zero (fun n ↦ measurableSet_lt (hg n) measurable_const) ?_
    have hl := hlow _ hε
    exact noteSupp_ae_mixture (h₁.mono fun x hx ↦ key A₁ x hx (hl.mono fun n hn ↦ hn.1))
      (h₂.mono fun x hx ↦ key A₂ x hx (hl.mono fun n hn ↦ hn.2))

/-- **Upper rate in probability of a tracked mixture.** Let `μ = w₁ ν₁ + w₂ ν₂` and suppose
that `g n` tracks `A_i` `ν_i`-almost surely. If eventually `A_1 n, A_2 n < C + ε` for every
`ε > 0`, and some component of positive weight has `A_i n > C - ε` infinitely often, then the
upper rate in probability `inf {β : μ{g_n > β} → 0}` is `C`. -/
theorem noteSupp_upperProbRate_eq_of_tracks [MetricSpace X] [BorelSpace X] {ν₁ ν₂ : Measure X}
    [IsProbabilityMeasure ν₁] [IsProbabilityMeasure ν₂] {w₁ w₂ : ℝ≥0∞}
    [IsFiniteMeasure (w₁ • ν₁ + w₂ • ν₂)]
    {g : ℕ → X → ℝ≥0∞} (hg : ∀ n, Measurable (g n)) {A₁ A₂ : ℕ → ℝ}
    (h₁ : ∀ᵐ x ∂ν₁, noteSupp_Tracks g A₁ x) (h₂ : ∀ᵐ x ∂ν₂, noteSupp_Tracks g A₂ x) {C : ℝ}
    (hup : ∀ ε > 0, ∀ᶠ n in atTop, A₁ n < C + ε ∧ A₂ n < C + ε)
    (hfreq : (w₁ ≠ 0 ∧ ∀ ε > 0, ∃ᶠ n in atTop, C - ε < A₁ n) ∨
      (w₂ ≠ 0 ∧ ∀ ε > 0, ∃ᶠ n in atTop, C - ε < A₂ n)) :
    upperProbRate (w₁ • ν₁ + w₂ • ν₂) g = ENNReal.ofReal C := by
  refine le_antisymm (le_of_forall_gt_imp_ge_of_dense fun β hβ ↦ sInf_le ?_)
    (le_sInf fun β hβ ↦ ?_)
  · obtain ⟨r, hCr, hrβ⟩ := noteSupp_exists_real_btwn hβ
    have hε : 0 < (r - C) / 2 := by linarith
    have key : ∀ (A : ℕ → ℝ) (x : X), noteSupp_Tracks g A x →
        (∀ᶠ n in atTop, A n < C + (r - C) / 2) →
          ∀ᶠ n in atTop, x ∉ {x | β < g n x} := by
      intro A x hx hA
      filter_upwards [hx.eventually_bounds hε, hA] with n hn hAn
      simp only [not_lt]
      exact hn.2.trans ((ENNReal.ofReal_le_ofReal (by linarith)).trans hrβ.le)
    refine noteSupp_tendsto_measure_zero (fun n ↦ measurableSet_lt measurable_const (hg n)) ?_
    have hu := hup _ hε
    exact noteSupp_ae_mixture (h₁.mono fun x hx ↦ key A₁ x hx (hu.mono fun n hn ↦ hn.1))
      (h₂.mono fun x hx ↦ key A₂ x hx (hu.mono fun n hn ↦ hn.2))
  · by_contra hlt
    rw [not_le] at hlt
    rcases hfreq with ⟨hw, hf⟩ | ⟨hw, hf⟩
    · exact noteSupp_not_tendsto_gt hw (noteSupp_le_mixture_left ν₁ ν₂ w₁ w₂) hg h₁ hf hlt hβ
    · exact noteSupp_not_tendsto_gt hw (noteSupp_le_mixture_right ν₁ ν₂ w₁ w₂) hg h₂ hf hlt hβ

end probRate

/-! ### Almost sure tracking for mixtures of two product measures on the shift -/

section productMixture

attribute [local instance] cantorMetricSpace

/-- The mass `∏_{i<m} μ_β{x_i}` of the cylinder `[x↾m]` under `μ_β = ⨂_i Bernoulli(β_i)`. -/
noncomputable def noteSupp_cylMass (β : ℕ → I) (m : ℕ) (x : ℕ → Bool) : ℝ :=
  ∏ i ∈ Finset.range m, bitMass (β i) (x i)

variable {β β₁ β₂ : ℕ → I} {δ : ℝ}

/-- Symbol masses are at least `δ` for biases in `[δ, 1 - δ]`. -/
lemma noteSupp_le_bitMass (hβ : ∀ i, δ ≤ (β i : ℝ) ∧ (β i : ℝ) ≤ 1 - δ) (i : ℕ) (b : Bool) :
    δ ≤ bitMass (β i) b := by
  unfold bitMass
  split_ifs
  · exact (hβ i).1
  · linarith [(hβ i).2]

/-- Cylinder masses are positive for biases in `[δ, 1 - δ]`, `δ > 0`. -/
lemma noteSupp_cylMass_pos (hδ : 0 < δ) (hβ : ∀ i, δ ≤ (β i : ℝ) ∧ (β i : ℝ) ≤ 1 - δ) (m : ℕ)
    (x : ℕ → Bool) : 0 < noteSupp_cylMass β m x :=
  Finset.prod_pos fun i _ ↦ hδ.trans_le (noteSupp_le_bitMass hβ i _)

/-- Cylinder masses are at most `1`. -/
lemma noteSupp_cylMass_le_one (m : ℕ) (x : ℕ → Bool) : noteSupp_cylMass β m x ≤ 1 :=
  Finset.prod_le_one₀ (fun _ _ ↦ bitMass_nonneg _ _) fun _ _ ↦ bitMass_le_one _ _

/-- `-log₂ μ_β[x↾m] = ∑_{i<m} Y_i(x)`. -/
lemma noteSupp_neg_logb_cylMass (hδ : 0 < δ) (hβ : ∀ i, δ ≤ (β i : ℝ) ∧ (β i : ℝ) ≤ 1 - δ)
    (m : ℕ) (x : ℕ → Bool) :
    -Real.logb 2 (noteSupp_cylMass β m x) = ∑ i ∈ Finset.range m, symbolInfo β i x := by
  rw [noteSupp_cylMass, Real.logb_prod _ _ fun i _ ↦
    (hδ.trans_le (noteSupp_le_bitMass hβ i _)).ne', ← Finset.sum_neg_distrib]
  rfl

/-- The mass of a cylinder under the mixture `t μ_{β₁} + s μ_{β₂}`. -/
lemma noteSupp_mixture_cylinder {t s : ℝ} (ht : 0 ≤ t) (hs : 0 ≤ s) (x : ℕ → Bool) (m : ℕ) :
    (ENNReal.ofReal t • productBernoulli β₁ + ENNReal.ofReal s • productBernoulli β₂)
        (PiNat.cylinder x m) =
      ENNReal.ofReal (t * noteSupp_cylMass β₁ m x + s * noteSupp_cylMass β₂ m x) := by
  have h₁ : 0 ≤ noteSupp_cylMass β₁ m x := Finset.prod_nonneg fun i _ ↦ bitMass_nonneg _ _
  have h₂ : 0 ≤ noteSupp_cylMass β₂ m x := Finset.prod_nonneg fun i _ ↦ bitMass_nonneg _ _
  simp only [Measure.add_apply, Measure.smul_apply, smul_eq_mul, productBernoulli_cylinder]
  simp only [noteSupp_cylMass] at h₁ h₂ ⊢
  rw [← ENNReal.ofReal_mul ht, ← ENNReal.ofReal_mul hs,
    ← ENNReal.ofReal_add (mul_nonneg ht h₁) (mul_nonneg hs h₂)]

/-- The dyadic radius `2^{-q}` as a power of `1/2`. -/
lemma noteSupp_dyadicRadius_eq (q : ℕ) : dyadicRadius q = (1 / 2 : ℝ) ^ q := by
  simp [dyadicRadius]

/-- Lemma 7.1 on the shift, at equal lengths: `μ_{β₁}`-almost surely, eventually
`μ_{β₂}[x↾n] ≤ (n² / δ) μ_{β₁}[x↾n]`. -/
lemma noteSupp_ae_cylMass_le (hδ : 0 < δ) (hβ₂ : ∀ i, δ ≤ (β₂ i : ℝ) ∧ (β₂ i : ℝ) ≤ 1 - δ) :
    ∀ᵐ x ∂productBernoulli β₁, ∀ᶠ n in atTop,
      noteSupp_cylMass β₂ n x ≤ (n : ℝ) ^ 2 / δ * noteSupp_cylMass β₁ n x := by
  have hd : ∀ x y : ℕ → Bool, x ≠ y → dist x y = (1 / 2 : ℝ) ^ PiNat.firstDiff x y :=
    fun _ _ ↦ cantorMetricSpace_dist_eq
  filter_upwards [ae_eventually_measure_bowenBall_le continuous_shiftMap_cantor
    (productBernoulli β₂) (productBernoulli β₁) (ε := (1 / 2 : ℝ) ^ 1) (by norm_num)] with x hx
  filter_upwards [hx, eventually_ge_atTop 1] with n hn h1
  have e1 := bowenBall_shiftMap_eq_cylinder (by norm_num) (by norm_num) hd x h1 1
  have e2 : bowenBall shiftMap n x (2 * (1 / 2 : ℝ) ^ 1) = PiNat.cylinder x n := by
    rw [show (2 : ℝ) * (1 / 2) ^ 1 = (1 / 2) ^ 0 by norm_num,
      bowenBall_shiftMap_eq_cylinder (by norm_num) (by norm_num) hd x h1 0, add_zero]
  rw [e1, e2, productBernoulli_cylinder, productBernoulli_cylinder,
    show ((n : ℝ≥0∞)) ^ 2 = ENNReal.ofReal ((n : ℝ) ^ 2) by simp,
    ← ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_le_ofReal_iff
      (mul_nonneg (by positivity) (Finset.prod_nonneg fun i _ ↦ bitMass_nonneg _ _))] at hn
  have hsucc : noteSupp_cylMass β₂ (n + 1) x = noteSupp_cylMass β₂ n x * bitMass (β₂ n) (x n) :=
    Finset.prod_range_succ _ _
  have hge : noteSupp_cylMass β₂ n x * δ ≤ noteSupp_cylMass β₂ (n + 1) x := by
    rw [hsucc]
    exact mul_le_mul_of_nonneg_left (noteSupp_le_bitMass hβ₂ n _)
      (Finset.prod_nonneg fun i _ ↦ bitMass_nonneg _ _)
  have := hge.trans hn
  rw [div_mul_eq_mul_div, le_div_iff₀ hδ]
  exact this

/-- `log₂ (1 + m²/δ) / m → 0`. -/
lemma noteSupp_tendsto_logb_poly_div (hδ : 0 < δ) :
    Tendsto (fun m : ℕ ↦ Real.logb 2 (1 + (m : ℝ) ^ 2 / δ) / m) atTop (𝓝 0) := by
  set C := Real.logb 2 (1 + 1 / δ)
  have hlog : Tendsto (fun m : ℕ ↦ Real.logb 2 m / m) atTop (𝓝 0) := by
    have h := (Real.tendsto_pow_logb_div_mul_add_atTop (b := 2) 1 0 1 one_ne_zero).comp
      tendsto_natCast_atTop_atTop
    simpa [Function.comp_def] using h
  have hup : Tendsto (fun m : ℕ ↦ C / m + 2 * (Real.logb 2 m / m)) atTop (𝓝 0) := by
    simpa using (tendsto_const_div_atTop_nhds_zero_nat C).add (hlog.const_mul 2)
  refine squeeze_zero' (Eventually.of_forall fun m ↦ div_nonneg (Real.logb_nonneg one_lt_two
    (by have : 0 ≤ (m : ℝ) ^ 2 / δ := by positivity
        linarith)) (Nat.cast_nonneg m)) ?_ hup
  filter_upwards [eventually_ge_atTop 1] with m hm
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hle : 1 + (m : ℝ) ^ 2 / δ ≤ (1 + 1 / δ) * (m : ℝ) ^ 2 := by
    have : (1 : ℝ) ≤ (m : ℝ) ^ 2 := by nlinarith
    rw [add_mul, one_mul, one_div, inv_mul_eq_div]
    linarith
  have hpos : (0 : ℝ) < 1 + (m : ℝ) ^ 2 / δ := by positivity
  calc Real.logb 2 (1 + (m : ℝ) ^ 2 / δ) / m ≤ Real.logb 2 ((1 + 1 / δ) * (m : ℝ) ^ 2) / m :=
        div_le_div_of_nonneg_right (Real.logb_le_logb_of_le one_lt_two hpos hle)
          (Nat.cast_nonneg m)
    _ = C / m + 2 * (Real.logb 2 m / m) := by
        rw [Real.logb_mul (by positivity) (by positivity), Real.logb_pow]
        push_cast
        ring

/-- **Tracking on a component.** Let `μ = t μ_{β₁} + s μ_{β₂}` with `t > 0`, `s ≥ 0`,
`t + s ≤ 1` and biases in `[δ, 1 - δ]`. Then `μ_{β₁}`-almost surely, at every scale `2^{-q}`,
`-(1/n) log₂ μ(B_n(x, σ, 2^{-q}))` tracks the Cesàro averages `(1/(n+q)) ∑_{i<n+q} H(β₁ i)`:
on one side `μ ≥ t μ_{β₁}`; on the other Lemma 7.1 gives `μ_{β₂}[x↾n] ≤ (n²/δ) μ_{β₁}[x↾n]`
eventually, and the strong law `ae_tendsto_symbolInfo_sub` applies to `μ_{β₁}`. -/
theorem noteSupp_tracks_productMixture (hδ : 0 < δ)
    (hβ₁ : ∀ i, δ ≤ (β₁ i : ℝ) ∧ (β₁ i : ℝ) ≤ 1 - δ)
    (hβ₂ : ∀ i, δ ≤ (β₂ i : ℝ) ∧ (β₂ i : ℝ) ≤ 1 - δ) {t s : ℝ} (ht : 0 < t) (hs : 0 ≤ s)
    (hts : t + s ≤ 1) (q : ℕ) :
    ∀ᵐ x ∂productBernoulli β₁, noteSupp_Tracks
      (fun n x ↦ localEntropyRate (ENNReal.ofReal t • productBernoulli β₁ +
        ENNReal.ofReal s • productBernoulli β₂) shiftMap x n (dyadicRadius q))
      (fun n ↦ entropyAverage β₁ (n + q)) x := by
  have hd : ∀ x y : ℕ → Bool, x ≠ y → dist x y = (1 / 2 : ℝ) ^ PiNat.firstDiff x y :=
    fun _ _ ↦ cantorMetricSpace_dist_eq
  filter_upwards [ae_tendsto_symbolInfo_sub hδ hβ₁, noteSupp_ae_cylMass_le (β₁ := β₁) hδ hβ₂]
    with x hS hdom
  set P₁ : ℕ → ℝ := fun m ↦ noteSupp_cylMass β₁ m x with hP₁
  set P₂ : ℕ → ℝ := fun m ↦ noteSupp_cylMass β₂ m x with hP₂
  set V : ℕ → ℝ := fun m ↦ -Real.logb 2 (t * P₁ m + s * P₂ m) with hV
  set S : ℕ → ℝ := fun m ↦ ∑ i ∈ Finset.range m, symbolInfo β₁ i x with hSdef
  have hP₁pos : ∀ m, 0 < P₁ m := fun m ↦ noteSupp_cylMass_pos hδ hβ₁ m x
  have hP₂nn : ∀ m, 0 ≤ P₂ m := fun m ↦ (noteSupp_cylMass_pos hδ hβ₂ m x).le
  have hQpos : ∀ m, 0 < t * P₁ m + s * P₂ m := fun m ↦
    add_pos_of_pos_of_nonneg (mul_pos ht (hP₁pos m)) (mul_nonneg hs (hP₂nn m))
  have hSP : ∀ m, S m = -Real.logb 2 (P₁ m) := fun m ↦
    (noteSupp_neg_logb_cylMass hδ hβ₁ m x).symm
  -- `V ≥ 0`
  have hVnn : ∀ m, 0 ≤ V m := fun m ↦ by
    have h1 : t * P₁ m + s * P₂ m ≤ 1 := by
      have := noteSupp_cylMass_le_one (β := β₁) m x
      have := noteSupp_cylMass_le_one (β := β₂) m x
      nlinarith [hP₁pos m, hP₂nn m]
    simp only [hV, neg_nonneg]
    exact Real.logb_nonpos one_lt_two (hQpos m).le h1
  -- upper bound `V ≤ S - log₂ t`
  have hVle : ∀ m, V m - S m ≤ -Real.logb 2 t := fun m ↦ by
    have h1 : Real.logb 2 (t * P₁ m) ≤ Real.logb 2 (t * P₁ m + s * P₂ m) :=
      Real.logb_le_logb_of_le one_lt_two (mul_pos ht (hP₁pos m))
        (le_add_of_nonneg_right (mul_nonneg hs (hP₂nn m)))
    rw [Real.logb_mul ht.ne' (hP₁pos m).ne'] at h1
    simp only [hV, hSP]
    linarith
  -- lower bound `V ≥ S - log₂ (1 + m²/δ)`, eventually
  have hVge : ∀ᶠ m : ℕ in atTop, -(Real.logb 2 (1 + (m : ℝ) ^ 2 / δ)) ≤ V m - S m := by
    filter_upwards [hdom] with m hm
    have hδm : 0 ≤ (m : ℝ) ^ 2 / δ := by positivity
    have h1 : t * P₁ m + s * P₂ m ≤ (1 + (m : ℝ) ^ 2 / δ) * P₁ m := by
      have := hm
      have ht1 : t ≤ 1 := by linarith
      have hs1 : s ≤ 1 := by linarith
      nlinarith [hP₁pos m, hP₂nn m, mul_le_mul_of_nonneg_left hs1 (hP₂nn m)]
    have h2 := Real.logb_le_logb_of_le one_lt_two (hQpos m) h1
    rw [Real.logb_mul (by positivity) (hP₁pos m).ne'] at h2
    simp only [hV, hSP]
    linarith
  -- `V m / m - A m → 0`
  have hu : Tendsto (fun m : ℕ ↦ V m / m - entropyAverage β₁ m) atTop (𝓝 0) := by
    have hlow := (noteSupp_tendsto_logb_poly_div hδ).neg
    have hhigh := tendsto_const_div_atTop_nhds_zero_nat (-Real.logb 2 t)
    have hE : Tendsto (fun m : ℕ ↦ (V m - S m) / m) atTop (𝓝 0) := by
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le' (by simpa using hlow) hhigh ?_
        (Eventually.of_forall fun m : ℕ ↦ div_le_div_of_nonneg_right (hVle m)
          (Nat.cast_nonneg m))
      filter_upwards [hVge] with m hm
      rw [← neg_div]
      exact div_le_div_of_nonneg_right hm (Nat.cast_nonneg m)
    have := hS.add hE
    rw [add_zero] at this
    refine this.congr fun m ↦ ?_
    simp only [hSdef]
    ring
  -- transfer to the scale `2^{-q}` and the shifted index
  have hA : ∀ m, |entropyAverage β₁ m| ≤ 1 := fun m ↦ by
    rw [abs_le]
    unfold entropyAverage
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp
    have hm' : (0 : ℝ) < m := by exact_mod_cast hm
    have hsum : ∑ i ∈ Finset.range m, bitEntropy (β₁ i) ≤ m := by
      have := Finset.sum_le_sum fun i (_ : i ∈ Finset.range m) ↦ bitEntropy_le_one (β₁ i)
      simpa using this
    have hsum0 : 0 ≤ ∑ i ∈ Finset.range m, bitEntropy (β₁ i) :=
      Finset.sum_nonneg fun i _ ↦ bitEntropy_nonneg _
    constructor
    · have := div_nonneg hsum0 hm'.le
      linarith
    · rw [div_le_one hm']
      exact hsum
  have hrate : ∀ n, 1 ≤ n → localEntropyRate (ENNReal.ofReal t • productBernoulli β₁ +
      ENNReal.ofReal s • productBernoulli β₂) shiftMap x n (dyadicRadius q) =
        ENNReal.ofReal (V (n + q)) / n := fun n hn ↦ by
    rw [localEntropyRate, noteSupp_dyadicRadius_eq,
      bowenBall_shiftMap_eq_cylinder (by norm_num) (by norm_num) hd x hn q,
      noteSupp_mixture_cylinder ht.le hs, infoBits_ofReal (hQpos _)]
  refine ⟨?_, (eventually_ge_atTop 1).mono fun n hn ↦ ?_⟩
  · have hu' := hu.comp (tendsto_add_atTop_nat q)
    have hq := tendsto_const_div_atTop_nhds_zero_nat (q : ℝ)
    have hB : Tendsto (fun n : ℕ ↦ entropyAverage β₁ (n + q) * ((q : ℝ) / n)) atTop (𝓝 0) := by
      refine squeeze_zero_norm (fun n ↦ ?_) hq
      rw [Real.norm_eq_abs, abs_mul]
      calc |entropyAverage β₁ (n + q)| * |(q : ℝ) / n| ≤ 1 * |(q : ℝ) / n| :=
            mul_le_mul_of_nonneg_right (hA _) (abs_nonneg _)
        _ = (q : ℝ) / n := by rw [one_mul, abs_of_nonneg (by positivity)]
    have hsum := (hu'.add (hu'.mul hq)).add hB
    simp only [Function.comp_def, mul_zero, add_zero] at hsum
    refine hsum.congr' ((eventually_ge_atTop 1).mono fun n hn ↦ ?_)
    dsimp only
    rw [hrate n hn, ENNReal.toReal_div, ENNReal.toReal_ofReal (hVnn _), ENNReal.toReal_natCast]
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.one_le_iff_ne_zero.1 hn)
    have hnq : ((n + q : ℕ) : ℝ) ≠ 0 := by positivity
    push_cast at hnq ⊢
    field_simp
    ring
  · dsimp only
    rw [hrate n hn]
    exact ENNReal.div_ne_top ENNReal.ofReal_ne_top (by exact_mod_cast
      (Nat.one_le_iff_ne_zero.1 hn))

end productMixture

end Kolmogorov.PointToSet
