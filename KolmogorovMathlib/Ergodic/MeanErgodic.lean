/-
Copyright (c) 2026 Emma Dinowitz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emma Dinowitz
-/
import KolmogorovMathlib.Ergodic.MaximalInequality
import Mathlib.Analysis.InnerProductSpace.MeanErgodic
import Mathlib.Dynamics.Ergodic.Function
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Birkhoff averages of an ergodic map

For an ergodic measure-preserving map `T` of a probability space and a bounded measurable
function `g`:

* `ae_tendsto_birkhoffAverage` (Birkhoff's pointwise ergodic theorem, ergodic case, bounded
  functions): `A_n g(x) → ∫ g dμ` for `μ`-a.e. `x`. Proof: for `a > ∫ g`, the set `G_a` of points
  where `A_n g > q` frequently for some rational `q > a` is exactly `T`-invariant, because
  `A_n g ∘ T - A_n g → 0` for bounded `g` (`tendsto_birkhoffAverage_apply_sub_birkhoffAverage'`).
  By ergodicity `G_a` is null or conull. It lies in the maximal set
  `{x | ∃ n ≥ 1, ∑_{k<n} (g - a)(T^k x) > 0}`, so if it were conull the maximal ergodic lemma
  (`setIntegral_nonneg_of_maximal`) would give `∫ g ≥ a`. Hence `limsup A_n g ≤ ∫ g` a.e.;
  applying this to `-g` gives the lower bound.
* `tendsto_integral_abs_birkhoffAverage_sub` (mean ergodic theorem in `L¹`):
  `∫ |A_n g - ∫ g dμ| dμ → 0`, from the pointwise theorem by dominated convergence
  (`|A_n g - ∫ g| ≤ 2 C`).

The non-ergodic version for bounded functions is in `BirkhoffNonErgodic.lean`
(`ae_exists_tendsto_birkhoffAverage`, `ae_tendsto_birkhoffAverage_condExp`); the general `L¹`
pointwise ergodic theorem is not formalized.
Blueprint node `erg:birkhoff`.
-/

noncomputable section

open MeasureTheory Filter Topology

namespace Kolmogorov.Ergodic

variable {X : Type*} [MeasurableSpace X]

omit [MeasurableSpace X] in
/-- Birkhoff averages of a function bounded by `C` are bounded by `C`. -/
lemma abs_birkhoffAverage_le {T : X → X} {g : X → ℝ} {C : ℝ} (hC : ∀ x, |g x| ≤ C)
    (n : ℕ) (x : X) : |birkhoffAverage ℝ T g n x| ≤ C := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simpa using (abs_nonneg _).trans (hC x)
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hsum : |birkhoffSum T g n x| ≤ n * C := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    simpa using Finset.sum_le_sum fun k (_ : k ∈ Finset.range n) ↦ hC (T^[k] x)
  rw [birkhoffAverage, smul_eq_mul, abs_mul, abs_inv, Nat.abs_cast, inv_mul_le_iff₀ hn']
  exact hsum

/-- Birkhoff averages of a measurable function under a measurable map are measurable. -/
lemma measurable_birkhoffAverage_of {T : X → X} (hT : Measurable T) {g : X → ℝ}
    (hg : Measurable g) (n : ℕ) : Measurable (birkhoffAverage ℝ T g n) :=
  (Finset.measurable_sum (Finset.range n) fun k _ ↦ hg.comp (hT.iterate k)).const_smul
    ((n : ℝ)⁻¹)

/-- The set of points along which a sequence of measurable functions is frequently above `q` is
measurable. -/
lemma measurableSet_frequently_lt {f : ℕ → X → ℝ} (hf : ∀ n, Measurable (f n)) (q : ℝ) :
    MeasurableSet {x | ∃ᶠ n in atTop, q < f n x} := by
  have : {x | ∃ᶠ n in atTop, q < f n x} = ⋂ N, ⋃ n, ⋃ (_ : N ≤ n), {x | q < f n x} := by
    ext x
    simp [Filter.frequently_atTop]
  rw [this]
  exact MeasurableSet.iInter fun N ↦ MeasurableSet.iUnion fun n ↦ MeasurableSet.iUnion fun _ ↦
    measurableSet_lt measurable_const (hf n)

/-- If `u n - v n → 0` and `u n > q` frequently, then `v n > q'` frequently for every `q' < q`. -/
lemma frequently_lt_of_tendsto_sub {u v : ℕ → ℝ}
    (h : Tendsto (fun n ↦ u n - v n) atTop (𝓝 0)) {q q' : ℝ} (hq : q' < q)
    (hu : ∃ᶠ n in atTop, q < u n) : ∃ᶠ n in atTop, q' < v n := by
  have hev : ∀ᶠ n in atTop, u n - v n < q - q' := (tendsto_order.1 h).2 _ (by linarith)
  exact hu.mp (hev.mono fun n h1 h2 ↦ by linarith)

/-- Upper half of Birkhoff's theorem for an ergodic map and a bounded measurable function: for
`μ`-a.e. `x`, eventually `A_n g(x) < b` for every `b > ∫ g`. The set of points where `A_n g > q`
frequently for some rational `q > a` is exactly `T`-invariant (`A_n g ∘ T - A_n g → 0`), so it is
null or conull; it lies in the maximal set of `g - a`, so conull would give `∫ g ≥ a`. -/
private lemma ae_eventually_birkhoffAverage_lt {μ : Measure X} [IsProbabilityMeasure μ]
    {T : X → X} (hT : Ergodic T μ) {g : X → ℝ} (hg : Measurable g) {C : ℝ}
    (hC : ∀ x, |g x| ≤ C) :
    ∀ᵐ x ∂μ, ∀ b, ∫ y, g y ∂μ < b → ∀ᶠ n in atTop, birkhoffAverage ℝ T g n x < b := by
  have hTm : MeasurePreserving T μ μ := hT.toMeasurePreserving
  have hgi : Integrable g μ := Integrable.of_bound hg.aestronglyMeasurable C
    (ae_of_all _ fun x ↦ (Real.norm_eq_abs _).trans_le (hC x))
  have hAm := measurable_birkhoffAverage_of hTm.measurable hg
  have hbdd : Bornology.IsBounded (Set.range g) := isBounded_iff_forall_norm_le.2
    ⟨C, by rintro _ ⟨x, rfl⟩; exact (Real.norm_eq_abs _).trans_le (hC x)⟩
  have hshift : ∀ x, Tendsto (fun n ↦ birkhoffAverage ℝ T g n (T x)
      - birkhoffAverage ℝ T g n x) atTop (𝓝 0) :=
    tendsto_birkhoffAverage_apply_sub_birkhoffAverage' ℝ hbdd T
  let G : ℝ → Set X := fun a ↦
    ⋃ q : ℚ, ⋃ (_ : a < q), {x | ∃ᶠ n in atTop, (q : ℝ) < birkhoffAverage ℝ T g n x}
  have hGm : ∀ a, MeasurableSet (G a) := fun a ↦
    MeasurableSet.iUnion fun q ↦ MeasurableSet.iUnion fun _ ↦ measurableSet_frequently_lt hAm q
  have hGinv : ∀ a, T ⁻¹' G a = G a := by
    intro a
    ext x
    simp only [G, Set.mem_preimage, Set.mem_iUnion, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨q, hq, hfr⟩
      obtain ⟨q', hq'a, hq'q⟩ := exists_rat_btwn hq
      exact ⟨q', hq'a, frequently_lt_of_tendsto_sub (hshift x) hq'q hfr⟩
    · rintro ⟨q, hq, hfr⟩
      obtain ⟨q', hq'a, hq'q⟩ := exists_rat_btwn hq
      refine ⟨q', hq'a, frequently_lt_of_tendsto_sub ?_ hq'q hfr⟩
      simpa using (hshift x).neg
  have hsub : ∀ a, G a ⊆ {x | ∃ n, 1 ≤ n ∧ 0 < birkhoffSum T (fun y ↦ g y - a) n x} := by
    intro a x hx
    simp only [G, Set.mem_iUnion, Set.mem_ofPred_eq] at hx ⊢
    obtain ⟨q, hq, hfr⟩ := hx
    obtain ⟨n, hn, hqn⟩ := Filter.frequently_atTop.1 hfr 1
    refine ⟨n, hn, ?_⟩
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    have hS : birkhoffSum T (fun y ↦ g y - a) n x = birkhoffSum T g n x - n * a := by
      simp [birkhoffSum, Finset.sum_sub_distrib]
    have hA : birkhoffAverage ℝ T g n x = birkhoffSum T g n x / n := by
      simp [birkhoffAverage, div_eq_inv_mul]
    rw [hA, lt_div_iff₀ hn'] at hqn
    have := mul_lt_mul_of_pos_right hq hn'
    rw [hS]
    linarith
  have hnull : ∀ a, ∫ y, g y ∂μ < a → μ (G a) = 0 := by
    intro a ha
    rcases hT.toPreErgodic.measure_self_or_compl_eq_zero (hGm a).nullMeasurableSet
      (by rw [hGinv a]) with h | h
    · exact h
    · exfalso
      have h' : ∀ᵐ x ∂μ, x ∈ G a := mem_ae_iff.2 h
      have hae : ∀ᵐ x ∂μ, x ∈ {x | ∃ n, 1 ≤ n ∧ 0 < birkhoffSum T (fun y ↦ g y - a) n x} :=
        h'.mono fun x hx ↦ hsub a hx
      have key := setIntegral_nonneg_of_maximal (g := fun y ↦ g y - a) hTm
        (hgi.sub (integrable_const a))
      rw [Measure.restrict_eq_self_of_ae_mem hae, integral_sub hgi (integrable_const a),
        integral_const, probReal_univ, one_smul] at key
      linarith
  have hall : ∀ᵐ x ∂μ, ∀ a : ℚ, ∫ y, g y ∂μ < a → x ∉ G a := by
    rw [ae_all_iff]
    intro a
    by_cases ha : ∫ y, g y ∂μ < a
    · exact (measure_eq_zero_iff_ae_notMem.1 (hnull a ha)).mono fun x hx _ ↦ hx
    · exact ae_of_all _ fun x h ↦ absurd h ha
  filter_upwards [hall] with x hx b hb
  obtain ⟨a, ha1, ha2⟩ := exists_rat_btwn hb
  obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn ha2
  have hnot : ¬ ∃ᶠ n in atTop, (q : ℝ) < birkhoffAverage ℝ T g n x := fun hfr ↦
    hx a ha1 (by simp only [G, Set.mem_iUnion, Set.mem_ofPred_eq]; exact ⟨q, hq1, hfr⟩)
  exact (not_frequently.1 hnot).mono fun n hn ↦ (not_lt.1 hn).trans_lt hq2

/-- Birkhoff's pointwise ergodic theorem for an ergodic map and a bounded measurable function:
`A_n g(x) → ∫ g dμ` for `μ`-almost every `x`. Blueprint node `erg:birkhoff`. -/
theorem ae_tendsto_birkhoffAverage {μ : Measure X} [IsProbabilityMeasure μ] {T : X → X}
    (hT : Ergodic T μ) {g : X → ℝ} (hg : Measurable g) {C : ℝ} (hC : ∀ x, |g x| ≤ C) :
    ∀ᵐ x ∂μ, Tendsto (fun n : ℕ ↦ birkhoffAverage ℝ T g n x) atTop (𝓝 (∫ y, g y ∂μ)) := by
  have hneg := ae_eventually_birkhoffAverage_lt hT hg.neg (C := C) fun x ↦ by
    simpa using hC x
  filter_upwards [ae_eventually_birkhoffAverage_lt hT hg hC, hneg] with x h1 h2
  refine tendsto_order.2 ⟨fun b hb ↦ ?_, h1⟩
  have := h2 (-b) (by simp only [Pi.neg_apply, integral_neg]; linarith)
  exact this.mono fun n hn ↦ by
    rw [birkhoffAverage_neg_apply] at hn
    linarith

/-- The mean ergodic theorem in `L¹` for a bounded measurable function and an ergodic map of a
probability space: `∫ |A_n g - ∫ g dμ| dμ → 0`. Blueprint node `erg:birkhoff`. -/
theorem tendsto_integral_abs_birkhoffAverage_sub {μ : Measure X} [IsProbabilityMeasure μ]
    {T : X → X} (hT : Ergodic T μ) {g : X → ℝ} (hg : Measurable g) {C : ℝ}
    (hC : ∀ x, |g x| ≤ C) :
    Tendsto (fun n : ℕ ↦ ∫ x, |birkhoffAverage ℝ T g n x - ∫ y, g y ∂μ| ∂μ) atTop (𝓝 0) := by
  have hAm := measurable_birkhoffAverage_of hT.toMeasurePreserving.measurable hg
  have hint : |∫ y, g y ∂μ| ≤ C := by
    have := norm_integral_le_of_norm_le_const (μ := μ) (f := g) (C := C)
      (ae_of_all _ fun x ↦ (Real.norm_eq_abs _).trans_le (hC x))
    simpa using this
  have := tendsto_integral_of_dominated_convergence (μ := μ) (fun _ ↦ C + C)
    (F := fun n x ↦ |birkhoffAverage ℝ T g n x - ∫ y, g y ∂μ|) (f := fun _ ↦ 0)
    (fun n ↦
      (continuous_abs.measurable.comp ((hAm n).sub measurable_const)).aestronglyMeasurable)
    (integrable_const _)
    (fun n ↦ ae_of_all _ fun x ↦ by
      rw [Real.norm_eq_abs, abs_abs]
      exact (abs_sub _ _).trans (add_le_add (abs_birkhoffAverage_le hC n x) hint))
    (by
      filter_upwards [ae_tendsto_birkhoffAverage hT hg hC] with x hx
      simpa using (hx.sub_const (∫ y, g y ∂μ)).abs)
  simpa using this

end Kolmogorov.Ergodic
