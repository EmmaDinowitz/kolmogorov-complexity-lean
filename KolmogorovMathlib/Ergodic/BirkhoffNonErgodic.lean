/-
Copyright (c) 2026 Emma Dinowitz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emma Dinowitz
-/
import KolmogorovMathlib.Ergodic.MeanErgodic
import Mathlib.MeasureTheory.MeasurableSpace.Invariants
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic

/-!
# Birkhoff's pointwise ergodic theorem without ergodicity (bounded functions)

For a measure-preserving map `T` of a probability space and a bounded measurable `g`:

* `ae_exists_tendsto_birkhoffAverage`: the Birkhoff averages `A_n g(x)` converge for `μ`-a.e. `x`.
  Proof: for rationals `a < b` let `E` be the set of points where `A_n g > q` frequently for some
  rational `q > b` and `A_n g < p` frequently for some rational `p < a` (private `upSet`). It is
  measurable and exactly `T`-invariant (`A_n g ∘ T - A_n g → 0` for bounded `g`), so `T`
  preserves `μ.restrict E`; the maximal ergodic lemma (`setIntegral_nonneg_of_maximal`) for
  `μ.restrict E` applied to `g - b` and `a - g` gives `b μ(E) ≤ ∫_E g ≤ a μ(E)`, so `μ(E) = 0`.
  Convergence off these null sets is `tendsto_of_no_upcrossings`.
* `ae_tendsto_birkhoffAverage_condExp`: the limit is the conditional expectation of `g` given the
  σ-algebra of invariant sets (`MeasurableSpace.invariants T`). The version
  `L = 1_D · limsup A_n g` of the limit (`D` the convergence set) satisfies `L ∘ T = L`, so it is
  `invariants T`-measurable; `∫_E A_n g = ∫_E g` for invariant `E` and `n ≥ 1` passes to the
  limit by dominated convergence, and `ae_eq_condExp_of_forall_setIntegral_eq` concludes.

Blueprint node `erg:birkhoff`.
-/

noncomputable section

open MeasureTheory Filter Topology

namespace Kolmogorov.Ergodic

variable {X : Type*} [MeasurableSpace X]

/-- The set of points where the Birkhoff averages of `g` are frequently above some rational
`q > c`. It is `T`-invariant for bounded `g` (`preimage_upSet`). -/
private def upSet (T : X → X) (g : X → ℝ) (c : ℝ) : Set X :=
  ⋃ q : ℚ, ⋃ (_ : c < q), {x | ∃ᶠ n in atTop, (q : ℝ) < birkhoffAverage ℝ T g n x}

/-- `upSet T g c` is measurable. -/
private lemma measurableSet_upSet {T : X → X} (hT : Measurable T) {g : X → ℝ}
    (hg : Measurable g) (c : ℝ) : MeasurableSet (upSet T g c) :=
  MeasurableSet.iUnion fun _ ↦ MeasurableSet.iUnion fun _ ↦
    measurableSet_frequently_lt (measurable_birkhoffAverage_of hT hg) _

omit [MeasurableSpace X] in
/-- `upSet T g c` is exactly `T`-invariant for bounded `g`, since `A_n g ∘ T - A_n g → 0`. -/
private lemma preimage_upSet {T : X → X} {g : X → ℝ} (hg : Bornology.IsBounded (Set.range g))
    (c : ℝ) : T ⁻¹' upSet T g c = upSet T g c := by
  have hshift : ∀ x, Tendsto (fun n ↦ birkhoffAverage ℝ T g n (T x)
      - birkhoffAverage ℝ T g n x) atTop (𝓝 0) :=
    tendsto_birkhoffAverage_apply_sub_birkhoffAverage' ℝ hg T
  ext x
  simp only [upSet, Set.mem_preimage, Set.mem_iUnion, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨q, hq, hfr⟩
    obtain ⟨q', hq'a, hq'q⟩ := exists_rat_btwn hq
    exact ⟨q', hq'a, frequently_lt_of_tendsto_sub (hshift x) hq'q hfr⟩
  · rintro ⟨q, hq, hfr⟩
    obtain ⟨q', hq'a, hq'q⟩ := exists_rat_btwn hq
    refine ⟨q', hq'a, frequently_lt_of_tendsto_sub ?_ hq'q hfr⟩
    simpa using (hshift x).neg

omit [MeasurableSpace X] in
/-- Points of `upSet T g c` lie in the maximal set of `g - c`. -/
private lemma upSet_subset {T : X → X} {g : X → ℝ} (c : ℝ) :
    upSet T g c ⊆ {x | ∃ n, 1 ≤ n ∧ 0 < birkhoffSum T (fun y ↦ g y - c) n x} := by
  intro x hx
  simp only [upSet, Set.mem_iUnion, Set.mem_ofPred_eq] at hx ⊢
  obtain ⟨q, hq, hfr⟩ := hx
  obtain ⟨n, hn, hqn⟩ := Filter.frequently_atTop.1 hfr 1
  refine ⟨n, hn, ?_⟩
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hS : birkhoffSum T (fun y ↦ g y - c) n x = birkhoffSum T g n x - n * c := by
    simp [birkhoffSum, Finset.sum_sub_distrib]
  have hA : birkhoffAverage ℝ T g n x = birkhoffSum T g n x / n := by
    simp [birkhoffAverage, div_eq_inv_mul]
  rw [hA, lt_div_iff₀ hn'] at hqn
  have := mul_lt_mul_of_pos_right hq hn'
  rw [hS]
  linarith

/-- Maximal ergodic lemma on an invariant set: if a measurable `T`-invariant set `E` lies in
`upSet T g c`, then `c μ(E) ≤ ∫_E g`. Proof: `T` preserves `μ.restrict E`, and `E` lies in the
maximal set of `g - c`. -/
private lemma mul_measureReal_le_setIntegral {μ : Measure X} [IsFiniteMeasure μ] {T : X → X}
    (hT : MeasurePreserving T μ μ) {g : X → ℝ} (hg : Integrable g μ) {E : Set X}
    (hEm : MeasurableSet E) (hEinv : T ⁻¹' E = E) (c : ℝ) (hE : E ⊆ upSet T g c) :
    c * μ.real E ≤ ∫ x in E, g x ∂μ := by
  have hTE : MeasurePreserving T (μ.restrict E) (μ.restrict E) := by
    have := hT.restrict_preimage hEm
    rwa [hEinv] at this
  have key := setIntegral_nonneg_of_maximal (g := fun y ↦ g y - c) hTE
    (hg.integrableOn.sub (integrable_const c))
  have hae : ∀ᵐ x ∂μ.restrict E,
      x ∈ {x | ∃ n, 1 ≤ n ∧ 0 < birkhoffSum T (fun y ↦ g y - c) n x} :=
    (ae_restrict_mem hEm).mono fun x hx ↦ upSet_subset c (hE hx)
  rw [Measure.restrict_eq_self_of_ae_mem hae, integral_sub hg.integrableOn (integrable_const c),
    integral_const, measureReal_restrict_apply_univ, smul_eq_mul] at key
  linarith

/-- Birkhoff averages of a bounded measurable function converge almost everywhere for a
measure-preserving map. Blueprint node `erg:birkhoff`. -/
theorem ae_exists_tendsto_birkhoffAverage {μ : Measure X} [IsProbabilityMeasure μ] {T : X → X}
    (hT : MeasurePreserving T μ μ) {g : X → ℝ} (hg : Measurable g) {C : ℝ}
    (hC : ∀ x, |g x| ≤ C) :
    ∀ᵐ x ∂μ, ∃ l, Tendsto (fun n : ℕ ↦ birkhoffAverage ℝ T g n x) atTop (𝓝 l) := by
  have hbdd : ∀ {f : X → ℝ}, (∀ x, |f x| ≤ C) → Bornology.IsBounded (Set.range f) :=
    fun hf ↦ isBounded_iff_forall_norm_le.2
      ⟨C, by rintro _ ⟨x, rfl⟩; exact (Real.norm_eq_abs _).trans_le (hf x)⟩
  have hgi : Integrable g μ := Integrable.of_bound hg.aestronglyMeasurable C
    (ae_of_all _ fun x ↦ (Real.norm_eq_abs _).trans_le (hC x))
  have hC' : ∀ x, |(-g) x| ≤ C := fun x ↦ by simpa using hC x
  let E : ℚ → ℚ → Set X := fun a b ↦ upSet T g b ∩ upSet T (-g) (-a)
  have hnull : ∀ a b : ℚ, a < b → μ (E a b) = 0 := by
    intro a b hab
    have hEm : MeasurableSet (E a b) :=
      (measurableSet_upSet hT.measurable hg _).inter (measurableSet_upSet hT.measurable hg.neg _)
    have hEinv : T ⁻¹' E a b = E a b := by
      simp only [E, Set.preimage_inter, preimage_upSet (hbdd hC), preimage_upSet (hbdd hC')]
    have h1 := mul_measureReal_le_setIntegral hT hgi hEm hEinv (b : ℝ) Set.inter_subset_left
    have h2 := mul_measureReal_le_setIntegral hT hgi.neg hEm hEinv (-(a : ℝ))
      Set.inter_subset_right
    simp only [Pi.neg_apply, integral_neg] at h2
    have hab' : (a : ℝ) < b := by exact_mod_cast hab
    have hpos : 0 ≤ μ.real (E a b) := measureReal_nonneg
    have : μ.real (E a b) = 0 := le_antisymm (by nlinarith) hpos
    exact (measureReal_eq_zero_iff (measure_ne_top _ _)).1 this
  have hall : ∀ᵐ x ∂μ, ∀ a b : ℚ, a < b → x ∉ E a b := by
    rw [ae_all_iff]
    intro a
    rw [ae_all_iff]
    intro b
    by_cases hab : a < b
    · exact (measure_eq_zero_iff_ae_notMem.1 (hnull a b hab)).mono fun x hx _ ↦ hx
    · exact ae_of_all _ fun x h ↦ absurd h hab
  filter_upwards [hall] with x hx
  refine tendsto_of_no_upcrossings Rat.denseRange_cast ?_
    (isBoundedUnder_of ⟨C, fun n ↦ (le_abs_self _).trans (abs_birkhoffAverage_le hC n x)⟩)
    (isBoundedUnder_of ⟨-C, fun n ↦ (neg_le_of_abs_le (abs_birkhoffAverage_le hC n x))⟩)
  rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩ hab ⟨ha, hb⟩
  obtain ⟨a', ha'1, ha'2⟩ := exists_rat_btwn hab
  obtain ⟨b', hb'1, hb'2⟩ := exists_rat_btwn ha'2
  refine hx a' b' (by exact_mod_cast hb'1) ⟨?_, ?_⟩
  · simp only [upSet, Set.mem_iUnion, Set.mem_ofPred_eq]
    exact ⟨b, hb'2, hb⟩
  · simp only [upSet, Set.mem_iUnion, Set.mem_ofPred_eq]
    refine ⟨-a, by push_cast; linarith, ha.mono fun n hn ↦ ?_⟩
    rw [birkhoffAverage_neg_apply]
    push_cast
    linarith

/-- The limit of the Birkhoff averages is the conditional expectation given the invariant
σ-algebra. Blueprint node `erg:birkhoff`. -/
theorem ae_tendsto_birkhoffAverage_condExp {μ : Measure X} [IsProbabilityMeasure μ] {T : X → X}
    (hT : MeasurePreserving T μ μ) {g : X → ℝ} (hg : Measurable g) {C : ℝ}
    (hC : ∀ x, |g x| ≤ C) :
    ∀ᵐ x ∂μ, Tendsto (fun n : ℕ ↦ birkhoffAverage ℝ T g n x) atTop
      (𝓝 (μ[g | MeasurableSpace.invariants T] x)) := by
  have hAm := measurable_birkhoffAverage_of hT.measurable hg
  have hbdd : Bornology.IsBounded (Set.range g) := isBounded_iff_forall_norm_le.2
    ⟨C, by rintro _ ⟨x, rfl⟩; exact (Real.norm_eq_abs _).trans_le (hC x)⟩
  have hgi : Integrable g μ := Integrable.of_bound hg.aestronglyMeasurable C
    (ae_of_all _ fun x ↦ (Real.norm_eq_abs _).trans_le (hC x))
  have hshift := tendsto_birkhoffAverage_apply_sub_birkhoffAverage' ℝ hbdd T
  -- the convergence set `D` and the invariant version `L` of the limit
  let D : Set X := {x | ∃ c, Tendsto (fun n ↦ birkhoffAverage ℝ T g n x) atTop (𝓝 c)}
  have hDm : MeasurableSet D := measurableSet_exists_tendsto hAm
  have hshiftD : ∀ x c, Tendsto (fun n ↦ birkhoffAverage ℝ T g n x) atTop (𝓝 c) →
      Tendsto (fun n ↦ birkhoffAverage ℝ T g n (T x)) atTop (𝓝 c) := fun x c h ↦ by
    simpa using h.add (hshift x)
  have hshiftD' : ∀ x c, Tendsto (fun n ↦ birkhoffAverage ℝ T g n (T x)) atTop (𝓝 c) →
      Tendsto (fun n ↦ birkhoffAverage ℝ T g n x) atTop (𝓝 c) := fun x c h ↦ by
    simpa using h.sub (hshift x)
  have hDinv : ∀ x, T x ∈ D ↔ x ∈ D := fun x ↦
    ⟨fun ⟨c, hc⟩ ↦ ⟨c, hshiftD' x c hc⟩, fun ⟨c, hc⟩ ↦ ⟨c, hshiftD x c hc⟩⟩
  let L : X → ℝ := D.indicator fun x ↦ limsup (fun n ↦ birkhoffAverage ℝ T g n x) atTop
  have hLm : Measurable L := (Measurable.limsup hAm).indicator hDm
  have hlim : ∀ x ∈ D, Tendsto (fun n ↦ birkhoffAverage ℝ T g n x) atTop (𝓝 (L x)) := by
    rintro x ⟨c, hc⟩
    simp only [L, Set.indicator_of_mem (show x ∈ D from ⟨c, hc⟩), hc.limsup_eq]
    exact hc
  have hLT : ∀ x, L (T x) = L x := by
    intro x
    by_cases hx : x ∈ D
    · obtain ⟨c, hc⟩ := hx
      simp only [L, Set.indicator_of_mem ((hDinv x).2 ⟨c, hc⟩),
        Set.indicator_of_mem (show x ∈ D from ⟨c, hc⟩), hc.limsup_eq, (hshiftD x c hc).limsup_eq]
    · simp only [L, Set.indicator_of_notMem hx, Set.indicator_of_notMem (mt (hDinv x).1 hx)]
  have hae : ∀ᵐ x ∂μ, Tendsto (fun n ↦ birkhoffAverage ℝ T g n x) atTop (𝓝 (L x)) :=
    (ae_exists_tendsto_birkhoffAverage hT hg hC).mono fun x hx ↦ hlim x hx
  have hLbound : ∀ x, |L x| ≤ C := by
    intro x
    by_cases hx : x ∈ D
    · exact le_of_tendsto' ((continuous_abs.tendsto _).comp (hlim x hx))
        fun n ↦ abs_birkhoffAverage_le hC n x
    · simp only [L, Set.indicator_of_notMem hx, abs_zero]
      exact (abs_nonneg _).trans (hC x)
  have hLi : Integrable L μ := Integrable.of_bound hLm.aestronglyMeasurable C
    (ae_of_all _ fun x ↦ (Real.norm_eq_abs _).trans_le (hLbound x))
  have hLinv : Measurable[MeasurableSpace.invariants T] L := by
    rw [MeasurableSpace.measurable_invariants_dom]
    refine ⟨hLm, fun s _ ↦ ?_⟩
    rw [show L ∘ T = L from funext hLT]
  -- set integrals over invariant sets
  have hset : ∀ s, MeasurableSet[MeasurableSpace.invariants T] s →
      ∫ x in s, L x ∂μ = ∫ x in s, g x ∂μ := by
    intro s hs
    have hTs : MeasurePreserving T (μ.restrict s) (μ.restrict s) := by
      have := hT.restrict_preimage hs.1
      rwa [hs.2] at this
    have hcomp : ∀ k, ∫ x in s, g (T^[k] x) ∂μ = ∫ x in s, g x ∂μ := by
      intro k
      have hk := hTs.iterate k
      rw [← integral_map hk.measurable.aemeasurable hg.aestronglyMeasurable, hk.map_eq]
    have hAn : ∀ n, 1 ≤ n → ∫ x in s, birkhoffAverage ℝ T g n x ∂μ = ∫ x in s, g x ∂μ := by
      intro n hn
      have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.one_le_iff_ne_zero.1 hn)
      simp only [birkhoffAverage, birkhoffSum, smul_eq_mul]
      rw [integral_const_mul, integral_finsetSum (f := fun k x ↦ g (T^[k] x)) _ fun k _ ↦
        Integrable.of_bound (hg.comp (hT.measurable.iterate k)).aestronglyMeasurable C
          (ae_of_all _ fun x ↦ (Real.norm_eq_abs _).trans_le (hC _))]
      simp only [hcomp, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      field_simp
    have hlimInt : Tendsto (fun n ↦ ∫ x in s, birkhoffAverage ℝ T g n x ∂μ) atTop
        (𝓝 (∫ x in s, L x ∂μ)) :=
      tendsto_integral_of_dominated_convergence (fun _ ↦ C)
        (fun n ↦ (hAm n).aestronglyMeasurable) (integrable_const C)
        (fun n ↦ ae_of_all _ fun x ↦ (Real.norm_eq_abs _).trans_le
          (abs_birkhoffAverage_le hC n x))
        (ae_restrict_of_ae hae)
    have hconst : Tendsto (fun n ↦ ∫ x in s, birkhoffAverage ℝ T g n x ∂μ) atTop
        (𝓝 (∫ x in s, g x ∂μ)) :=
      tendsto_const_nhds.congr' ((eventually_ge_atTop 1).mono fun n hn ↦ (hAn n hn).symm)
    exact tendsto_nhds_unique hlimInt hconst
  have hLae : L =ᵐ[μ] μ[g | MeasurableSpace.invariants T] :=
    ae_eq_condExp_of_forall_setIntegral_eq (MeasurableSpace.invariants_le T) hgi
      (fun s _ _ ↦ hLi.integrableOn) (fun s hs _ ↦ hset s hs)
      hLinv.stronglyMeasurable.aestronglyMeasurable
  filter_upwards [hae, hLae] with x hx hx'
  rw [← hx']
  exact hx

end Kolmogorov.Ergodic
