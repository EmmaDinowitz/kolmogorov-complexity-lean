/-
Copyright (c) 2026 Emma Dinowitz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emma Dinowitz
-/
import KolmogorovMathlib.PointToSet.Measure.InformationRate
import KolmogorovMathlib.PointToSet.Measure.Ergodic.FengHuangLowerAux
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real

/-!
# The Feng–Huang variational principle, Lower half

D.-J. Feng and W. Huang, *Variational principles for topological entropies of subsets*,
J. Funct. Anal. 263 (2012) (arXiv:1012.1103): for a continuous map `T` of a compact metric space
and a nonempty compact `K`, the lower (Bowen) half: `lowerEntropy T K ≤ sup_{μ(K)=1} h̲_μ(T)`.

Proof (Feng–Huang §§2–3, with a simplified comparison):

* a weighted Bowen content `W s N ε` (an infimum of `∑ c_i 2^{-s n_i}` over families with
  `∑ c_i 1_{B_{n_i}(x_i, ε)} ≥ 1_K`) is sublinear and dominates the Bowen content
  (maximal `(n, 2ε)`-separated nets); this is `FengHuangLowerAux.lean`;
* the dynamical Frostman lemma `fhLower_frostman` (Hahn–Banach
  `exists_extension_of_le_sublinear`, Riesz–Markov–Kakutani `RealRMK.rieszMeasure`, Urysohn)
  gives a probability `μ` on `K` with `μ(B_n(x, ε/2)) ≤ 2^{-ns}/c` for `n ≥ N`;
* hence `h̲_μ(T, x) ≥ s` everywhere, and `h̲_μ(T) ≥ s` (`lowerEntropy_le_iSup_measureEntropy'`).

Blueprint node `meas:variational`.
-/

namespace Kolmogorov.PointToSet

open Filter Set MeasureTheory
open scoped Topology ENNReal Computability CompactlySupported

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

/-! ### The dynamical Frostman lemma -/

section Frostman

variable [CompactSpace X]

omit [MeasurableSpace X] [BorelSpace X] in
/-- A continuous function on a compact space, as a compactly supported one. -/
private noncomputable def fhLowerCc (φ : C(X, ℝ)) : C_c(X, ℝ) :=
  ⟨φ, HasCompactSupport.of_compactSpace _⟩

omit [MeasurableSpace X] [BorelSpace X] in
/-- The compactly supported version of a continuous function has the same values. -/
private theorem fhLowerCc_apply (φ : C(X, ℝ)) (x : X) : fhLowerCc φ x = φ x := rfl

omit [MeasurableSpace X] [BorelSpace X] in
/-- The constant function one is nonzero on a nonempty space. -/
private theorem fhLowerCc_one_ne_zero [Nonempty X] : fhLowerCc (1 : C(X, ℝ)) ≠ 0 := by
  intro h
  obtain ⟨x⟩ := ‹Nonempty X›
  have := congrArg (fun f : C_c(X, ℝ) ↦ f x) h
  simp [fhLowerCc_apply] at this

omit [MeasurableSpace X] [BorelSpace X] in
/-- **Hahn–Banach for a normalized sublinear functional**: a positively homogeneous,
subadditive `p` on `C_c(X, ℝ)` with `p f = 0` for `f ≤ 0` and `p 1 = 1` dominates a positive
linear functional `Λ` with `Λ 1 = 1`. -/
private theorem fhLower_exists_positive_le [Nonempty X] (p : C_c(X, ℝ) → ℝ)
    (hhom : ∀ c : ℝ, 0 < c → ∀ f, p (c • f) = c * p f) (hadd : ∀ f g, p (f + g) ≤ p f + p g)
    (hneg : ∀ f : C_c(X, ℝ), (∀ x, f x ≤ 0) → p f = 0) (hone : p (fhLowerCc 1) = 1) :
    ∃ Λ : C_c(X, ℝ) →ₚ[ℝ] ℝ, Λ (fhLowerCc 1) = 1 ∧ ∀ f, Λ f ≤ p f := by
  have hH : ∀ c : ℝ, c • fhLowerCc (1 : C(X, ℝ)) = 0 → (RingHom.id ℝ) c • (1 : ℝ) = 0 := by
    intro c hc
    rcases eq_or_ne c 0 with rfl | h0
    · simp
    · exact absurd ((smul_eq_zero.1 hc).resolve_left h0) fhLowerCc_one_ne_zero
  let f₀ := LinearPMap.mkSpanSingleton' (fhLowerCc (1 : C(X, ℝ))) (1 : ℝ) hH
  obtain ⟨g, hg, hgp⟩ := exists_extension_of_le_sublinear f₀ p hhom hadd (by
    rintro ⟨x, hx⟩
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hx
    rw [LinearPMap.mkSpanSingleton'_apply]
    simp only [RingHom.id_apply, smul_eq_mul, mul_one]
    rcases lt_or_ge 0 c with hc | hc
    · rw [hhom c hc, hone, mul_one]
    · rw [hneg _ (fun x ↦ by simpa [fhLowerCc_apply] using hc)]
      exact hc)
  have hg1 : g (fhLowerCc 1) = 1 := by
    have h := hg ⟨(1 : ℝ) • fhLowerCc 1,
      Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)⟩
    rw [LinearPMap.mkSpanSingleton'_apply] at h
    simpa using h
  have hpos : ∀ f : C_c(X, ℝ), 0 ≤ f → 0 ≤ g f := by
    intro f hf
    have h1 := hgp (-f)
    rw [hneg _ (fun x ↦ by simpa using hf x), map_neg] at h1
    linarith
  exact ⟨PositiveLinearMap.mk₀ g hpos, hg1, hgp⟩

/-- **Dynamical Frostman lemma** (Feng–Huang, Lemma 3.4): if the weighted content
`c = W^s_{N,ε}(1_K)` of a nonempty compact `K` is positive, there is a Borel probability `μ`
with `μ K = 1` and `μ (B_n(x, ε/2)) ≤ 2^{-s n} / c` for all `x` and `n ≥ N`. -/
theorem fhLower_frostman {T : X → X} (hT : Continuous T) {K : Set X} (hK : IsCompact K)
    (hne : K.Nonempty) (s : ℝ) {ε : ℝ} (hε : 0 < ε) (N : ℕ)
    (hc0 : fhLowerWeightedContent T s ε N (K.indicator 1) ≠ 0) :
    ∃ μ : Measure X, IsProbabilityMeasure μ ∧ μ K = 1 ∧ ∀ x n, N ≤ n →
      μ (bowenBall T n x (ε / 2)) ≤
        (2 : ℝ≥0∞) ^ (-s * (n : ℝ)) / fhLowerWeightedContent T s ε N (K.indicator 1) := by
  classical
  have : Nonempty X := hne.to_subtype.map Subtype.val
  set W := fhLowerWeightedContent T s ε N with hW
  set c := W (K.indicator 1) with hc
  have hcT : c ≠ ⊤ := by
    refine ne_top_of_le_ne_top
      (fhLower_weightedContent_const_lt_top hT s hε N ENNReal.one_ne_top).ne ?_
    exact fhLower_weightedContent_mono T s ε N (indicator_le fun _ _ ↦ le_rfl)
  have hcR : 0 < c.toReal := ENNReal.toReal_pos hc0 hcT
  -- the sublinear functional
  let G : C_c(X, ℝ) → X → ℝ≥0∞ := fun f ↦ K.indicator fun z ↦ ENNReal.ofReal (f z)
  have hGT : ∀ f, W (G f) ≠ ⊤ := by
    intro f
    obtain ⟨M, hM⟩ := (isCompact_range f.continuous).bddAbove
    refine ne_top_of_le_ne_top
      (fhLower_weightedContent_const_lt_top hT s hε N (b := ENNReal.ofReal M)
        ENNReal.ofReal_ne_top).ne ?_
    refine fhLower_weightedContent_mono T s ε N (indicator_le fun z _ ↦ ?_)
    exact ENNReal.ofReal_le_ofReal (hM ⟨z, rfl⟩)
  let p : C_c(X, ℝ) → ℝ := fun f ↦ (W (G f)).toReal / c.toReal
  have hzero : ∀ f : C_c(X, ℝ), (∀ x ∈ K, f x ≤ 0) → p f = 0 := by
    intro f hf
    have : G f = fun _ ↦ 0 := by
      funext z
      by_cases hz : z ∈ K
      · simp [G, indicator_of_mem hz, ENNReal.ofReal_eq_zero.2 (hf z hz)]
      · simp [G, indicator_of_notMem hz]
    simp [p, this, hW, fhLower_weightedContent_zero]
  have hhom : ∀ a : ℝ, 0 < a → ∀ f, p (a • f) = a * p f := by
    intro a ha f
    have hG : G (a • f) = fun z ↦ ENNReal.ofReal a * G f z := by
      funext z
      by_cases hz : z ∈ K
      · simp [G, indicator_of_mem hz, ENNReal.ofReal_mul ha.le]
      · simp [G, indicator_of_notMem hz]
    simp only [p, hG]
    rw [hW, fhLower_weightedContent_mul T s ε N _ (ENNReal.ofReal_pos.2 ha).ne'
      ENNReal.ofReal_ne_top, ENNReal.toReal_mul, ENNReal.toReal_ofReal ha.le, mul_div_assoc]
  have hadd : ∀ f g, p (f + g) ≤ p f + p g := by
    intro f g
    have hG : G (f + g) ≤ G f + G g := by
      intro z
      by_cases hz : z ∈ K
      · simpa [G, indicator_of_mem hz] using ENNReal.ofReal_add_le
      · simp [G, indicator_of_notMem hz]
    have h1 : W (G (f + g)) ≤ W (G f) + W (G g) :=
      (fhLower_weightedContent_mono T s ε N hG).trans
        (fhLower_weightedContent_add_le T s ε N _ _)
    simp only [p]
    rw [← add_div, ← ENNReal.toReal_add (hGT f) (hGT g)]
    exact div_le_div_of_nonneg_right
      (ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hGT f, hGT g⟩) h1) hcR.le
  have hone : p (fhLowerCc 1) = 1 := by
    have : G (fhLowerCc 1) = K.indicator 1 := by
      funext z
      by_cases hz : z ∈ K
      · simp [G, indicator_of_mem hz, fhLowerCc_apply]
      · simp [G, indicator_of_notMem hz]
    simp only [p, this]
    exact div_self hcR.ne'
  obtain ⟨Λ, hΛ1, hΛp⟩ := fhLower_exists_positive_le p hhom hadd
    (fun f hf ↦ hzero f fun x _ ↦ hf x) hone
  -- the measure
  let μ := RealRMK.rieszMeasure Λ
  have hμ1 : μ univ = 1 := by
    apply le_antisymm
    · have := RealRMK.rieszMeasure_le_of_eq_one Λ (f := fhLowerCc 1)
        (fun x ↦ by simp [fhLowerCc_apply]) isCompact_univ (fun x _ ↦ rfl)
      simpa [hΛ1] using this
    · have := RealRMK.le_rieszMeasure_tsupport_subset Λ (f := fhLowerCc 1)
        (fun x ↦ by simp [fhLowerCc_apply]) (subset_univ _)
      simpa [hΛ1] using this
  have hprob : IsProbabilityMeasure μ := ⟨hμ1⟩
  -- the measure of a closed set under an Urysohn function
  have hbound : ∀ (F : Set X) (φ : C(X, ℝ)), IsClosed F → (∀ x, φ x ∈ Icc (0 : ℝ) 1) →
      EqOn φ 1 F → μ F ≤ ENNReal.ofReal (p (fhLowerCc φ)) := by
    intro F φ hF hφ hφF
    refine (RealRMK.rieszMeasure_le_of_eq_one Λ (f := fhLowerCc φ) (fun x ↦ (hφ x).1)
      hF.isCompact fun x hx ↦ hφF hx).trans (ENNReal.ofReal_le_ofReal (hΛp _))
  refine ⟨μ, hprob, ?_, fun x n hn ↦ ?_⟩
  · -- `μ` is carried by `K`
    obtain ⟨F, hFc, hFsub, hFU, -⟩ := hK.isClosed.isOpen_compl.exists_iUnion_isClosed
    refine (prob_compl_eq_zero_iff hK.measurableSet).1 ?_
    rw [← hFU]
    refine measure_iUnion_null fun m ↦ ?_
    obtain ⟨φ, hφK, hφF, hφ⟩ := exists_continuous_zero_one_of_isClosed hK.isClosed (hFc m)
      (disjoint_compl_right.mono_right (hFsub m))
    refine le_antisymm ((hbound _ φ (hFc m) hφ hφF).trans ?_) bot_le
    rw [hzero _ fun z hz ↦ by rw [fhLowerCc_apply, hφK hz, Pi.zero_apply], ENNReal.ofReal_zero]
  · -- the Frostman bound on Bowen balls
    have hB := bowen_ball_dense_open T hT n x ε
    obtain ⟨φ, hφB, hφF, hφ⟩ := exists_continuous_zero_one_of_isClosed hB.isClosed_compl
      (isClosed_closedBowenBall hT n x (ε / 2))
      (disjoint_compl_left_iff_subset.2
        (closedBowenBall_subset_bowenBall T n x (by linarith : ε / 2 < ε)))
    have hGφ : G (fhLowerCc φ) ≤ (bowenBall T n x ε).indicator 1 := by
      intro z
      by_cases hz : z ∈ bowenBall T n x ε
      · rw [indicator_of_mem hz]
        refine (indicator_le_self' (fun _ _ ↦ zero_le) z).trans ?_
        simpa [fhLowerCc_apply] using (hφ z).2
      · rw [indicator_of_notMem hz]
        have : φ z = 0 := hφB hz
        simp [G, fhLowerCc_apply, this]
    have hW2 : W (G (fhLowerCc φ)) ≤ (2 : ℝ≥0∞) ^ (-s * (n : ℝ)) :=
      (fhLower_weightedContent_mono T s ε N hGφ).trans
        (fhLower_weightedContent_bowenBall_le T s ε hn x)
    have h2T : (2 : ℝ≥0∞) ^ (-s * (n : ℝ)) ≠ ⊤ :=
      ENNReal.rpow_ne_top_of_ne_zero (by norm_num) (by norm_num)
    calc μ (bowenBall T n x (ε / 2)) ≤ μ (closedBowenBall T n x (ε / 2)) :=
          measure_mono (bowenBall_subset_closedBowenBall T n x _)
      _ ≤ ENNReal.ofReal (p (fhLowerCc φ)) :=
          hbound _ φ (isClosed_closedBowenBall hT n x _) hφ hφF
      _ ≤ ENNReal.ofReal (((2 : ℝ≥0∞) ^ (-s * (n : ℝ))).toReal / c.toReal) :=
          ENNReal.ofReal_le_ofReal
            (div_le_div_of_nonneg_right (ENNReal.toReal_mono h2T hW2) hcR.le)
      _ = (2 : ℝ≥0∞) ^ (-s * (n : ℝ)) / c := by
          rw [ENNReal.ofReal_div_of_pos hcR, ENNReal.ofReal_toReal h2T,
            ENNReal.ofReal_toReal hcT]

end Frostman

/-- The Feng–Huang variational principle, Lower half (the statement of the leaf in
`Variational.lean`). Blueprint node `meas:variational`. -/
theorem lowerEntropy_le_iSup_measureEntropy' [CompactSpace X] {T : X → X} (hT : Continuous T)
    {K : Set X} (hK : IsCompact K) (hne : K.Nonempty) :
    lowerEntropy T K ≤
      ⨆ (μ : Measure X) (_ : IsProbabilityMeasure μ) (_ : μ K = 1), (measureEntropy μ T).1 := by
  refine iSup_le fun p ↦ le_of_forall_lt_imp_le_of_dense fun b hb ↦ ?_
  obtain ⟨s', hs'0, hbs', hs'p⟩ := ENNReal.lt_iff_exists_real_btwn.1 hb
  obtain ⟨β, hβ0, hbβ, hβs'⟩ := ENNReal.lt_iff_exists_real_btwn.1 hbs'
  refine hbβ.le.trans ?_
  have hβs : β < s' := (ENNReal.ofReal_lt_ofReal_iff_of_nonneg hβ0).1 hβs'
  -- the Bowen content at the exponent `s'` is positive at some cutoff `N`
  have hlim : lowerContentLimit T (fun _ ↦ 0) .centered K s' (dyadicRadius p) ≠ 0 := fun h ↦
    absurd (iInf_le_of_le s' (iInf_le_of_le hs'0 (iInf_le_of_le h le_rfl))) (not_le.2 hs'p)
  obtain ⟨N, hN1, hN⟩ : ∃ N, 1 ≤ N ∧
      lowerContent T (fun _ ↦ 0) .centered K s' (dyadicRadius p) N ≠ 0 := by
    by_contra h
    push Not at h
    exact hlim (ENNReal.iSup_eq_zero.2 fun N ↦ ENNReal.iSup_eq_zero.2 fun hN ↦ h N hN)
  set δ := (s' - β) / 2 with hδ
  have hδ0 : 0 < δ := by rw [hδ]; linarith
  set s := s' - δ with hs
  -- the geometric weights `2^{-δ k}` and a cutoff `N' ≥ N` with tail sum `< 1`
  set f : ℕ → ℝ≥0∞ := fun k ↦ (2 : ℝ≥0∞) ^ (-δ * (k : ℝ)) with hf
  have hfsum : ∑' k, f k ≠ ⊤ := by
    have : ∀ k : ℕ, f k = ((2 : ℝ≥0∞) ^ (-δ)) ^ k := fun k ↦ by
      rw [hf, ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
    simp_rw [this, ENNReal.tsum_geometric]
    exact ENNReal.inv_ne_top.2 (tsub_pos_iff_lt.2
      (ENNReal.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith))).ne'
  obtain ⟨N', hN', hN'N⟩ : ∃ N', ∑' k, f (k + N') < 1 ∧ N ≤ N' :=
    (((tendsto_order.1 (ENNReal.tendsto_sum_nat_add f hfsum)).2 1 one_pos).and
      (eventually_ge_atTop N)).exists
  have hN'1 : 1 ≤ N' := hN1.trans hN'N
  -- comparison with the weighted content at the radius `r_{p+1}`
  have hr : 2 * dyadicRadius (p + 1) = dyadicRadius p := by
    simp only [dyadicRadius, pow_succ]
    ring
  have hcmp := fhLower_lowerContent_le_weightedContent T K (s := s) hN'1
    (dyadicRadius_pos (p + 1)) hN'
  rw [hr, hs, sub_add_cancel] at hcmp
  set c := fhLowerWeightedContent T s (dyadicRadius (p + 1)) N' (K.indicator 1) with hc
  have hc0 : c ≠ 0 := fun h ↦ hN (le_antisymm
    ((fhLower_lowerContent_mono_cutoff _ _ _ _ _ _ hN'N).trans (hcmp.trans h.le)) bot_le)
  -- the Frostman measure
  obtain ⟨μ, hμ, hμK, hμB⟩ := fhLower_frostman hT hK hne s (dyadicRadius_pos (p + 1)) N' hc0
  refine le_iSup_of_le μ (le_iSup_of_le hμ (le_iSup_of_le hμK ?_))
  have hr2 : dyadicRadius (p + 1) / 2 = dyadicRadius (p + 2) := by
    simp only [dyadicRadius, pow_succ]
    ring
  have hloc : ∀ x, ENNReal.ofReal β ≤ (localEntropy μ T x).1 := by
    intro x
    simp only [localEntropy, localEntropyAt]
    refine le_iSup_of_le (p + 2) (le_liminf_of_le (by isBoundedDefault) ?_)
    have hev : ∀ᶠ n : ℕ in atTop, f n < c :=
      (tendsto_order.1 (ENNReal.tendsto_atTop_zero_of_tsum_ne_top hfsum)).2 c
        (pos_iff_ne_zero.2 hc0)
    filter_upwards [hev, eventually_ge_atTop N', eventually_ge_atTop 1] with n hn hnN hn1
    have hμn := hμB x n hnN
    rw [hr2] at hμn
    have hkey : μ (bowenBall T n x (dyadicRadius (p + 2))) ≤
        ENNReal.ofReal ((2 : ℝ) ^ (-(β * n))) := by
      refine hμn.trans ?_
      have hsplit : (2 : ℝ≥0∞) ^ (-s * (n : ℝ)) = (2 : ℝ≥0∞) ^ (-(β * n)) * f n := by
        rw [hf, ← ENNReal.rpow_add _ _ (by norm_num) (by norm_num)]
        congr 1
        rw [hs, hδ]
        ring
      rw [hsplit, mul_div_assoc, ← ENNReal.ofReal_rpow_of_pos two_pos, ENNReal.ofReal_ofNat]
      exact mul_le_of_le_one_right' (ENNReal.div_le_of_le_mul (by rw [one_mul]; exact hn.le))
    have hinfo := le_infoBits_of_le_rpow hkey
    unfold localEntropyRate
    rw [ENNReal.le_div_iff_mul_le (Or.inl (by exact_mod_cast (by omega : n ≠ 0)))
      (Or.inl (ENNReal.natCast_ne_top n)), ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul hβ0]
    exact hinfo
  calc ENNReal.ofReal β = ∫⁻ _, ENNReal.ofReal β ∂μ := by simp
    _ ≤ ∫⁻ x, (localEntropy μ T x).1 ∂μ := lintegral_mono hloc

end Kolmogorov.PointToSet
