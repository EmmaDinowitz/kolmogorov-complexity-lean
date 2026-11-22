/-
Copyright (c) 2026 Emma Dinowitz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emma Dinowitz
-/
import KolmogorovMathlib.Ergodic.BirkhoffNonErgodic
import Mathlib.MeasureTheory.SetAlgebra
import Mathlib.Probability.Kernel.Condexp

/-!
# Ergodic decomposition on a compact metric space

`exists_ergodicDecomposition`: for a continuous map `T` of a compact metric space and a
`T`-invariant Borel probability measure `μ` there is a Markov kernel `κ : X → Measure X` with
`μ.bind κ = μ` such that `κ x` is `T`-invariant and ergodic for `μ`-almost every `x`.
Mathlib has no ergodic decomposition.

Construction. Let `I = invariants T` be the σ-algebra of (measurable, exactly) `T`-invariant
sets and `κ = condExpKernel μ I` (`X` is compact metric, hence standard Borel), viewed as a kernel
on `X` with its Borel σ-algebra. Fix a countable algebra of sets `𝒜` generating the Borel
σ-algebra (`generateSetAlgebra` of `countableGeneratingSet X`). Then:
* `μ.bind κ = μ` (`condExpKernel_comp_trim`); hence a `μ`-a.e. property holds `κ x`-a.e. for
  `μ`-a.e. `x`;
* for an `I`-measurable `h : X → ℝ`, `h = h(x)` `κ x`-a.e. for `μ`-a.e. `x`: for an invariant
  set `S`, `κ x S = E[1_S | I](x) = 1_S(x)` a.e.; test with the sets `{h < q}`, `q ∈ ℚ`;
* `κ x` is invariant: `E[1_{T⁻¹A} | I] = E[1_A | I]` a.e. since the sets of `I` are invariant;
  this gives `κ x (T⁻¹ A) = κ x A` for all `A ∈ 𝒜` (countably many), hence `map T (κ x) = κ x`;
* `κ x` is ergodic: by `ae_tendsto_birkhoffAverage_condExp`, the averages `A_n 1_A` converge
  `μ`-a.e. to the `I`-measurable `E[1_A | I]`, hence, under `κ x`, a.e. to the constant
  `E[1_A | I](x) = κ x A`. For a `T`-invariant set `E`, `1_E · A_n 1_A = A_n 1_{A ∩ E}` and
  dominated convergence give `κ x (A ∩ E) = κ x A · κ x E` for `A ∈ 𝒜`; so
  `(κ x).restrict E = κ x E • κ x`, and evaluating at `E` gives `κ x E ∈ {0, 1}`.

Continuity of `T` is not used (only its measurability). The proof relies on the statement of
`ae_tendsto_birkhoffAverage_condExp` (`BirkhoffNonErgodic.lean`).

Blueprint node `erg:decomposition`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory MeasurableSpace

namespace Kolmogorov.Ergodic

section Aux

variable {X : Type*} [mX : MeasurableSpace X]

omit mX in
/-- If `T ⁻¹' E = E` then `T^[k] y ∈ E ↔ y ∈ E`. -/
private lemma iterate_mem_iff {T : X → X} {E : Set X} (hTE : T ⁻¹' E = E) (k : ℕ) (y : X) :
    T^[k] y ∈ E ↔ y ∈ E := by
  induction k generalizing y with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply, ih]
    exact Set.ext_iff.1 hTE y

omit mX in
/-- The Birkhoff average of an indicator function is bounded by `1` in absolute value. -/
private lemma abs_birkhoffAverage_indicator_le (T : X → X) (A : Set X) (n : ℕ) (y : X) :
    |birkhoffAverage ℝ T (A.indicator fun _ ↦ (1 : ℝ)) n y| ≤ 1 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have h0 : ∀ k ∈ Finset.range n, 0 ≤ A.indicator (fun _ ↦ (1 : ℝ)) (T^[k] y) :=
    fun k _ ↦ Set.indicator_nonneg (fun _ _ ↦ zero_le_one) _
  have h1 : ∀ k ∈ Finset.range n, A.indicator (fun _ ↦ (1 : ℝ)) (T^[k] y) ≤ 1 := fun k _ ↦ by
    by_cases hk : T^[k] y ∈ A <;> simp [hk]
  have hS0 := Finset.sum_nonneg h0
  have hS1 := Finset.sum_le_card_nsmul _ _ _ h1
  simp only [Finset.card_range, nsmul_eq_mul, mul_one] at hS1
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  rw [birkhoffAverage, birkhoffSum, smul_eq_mul, abs_of_nonneg (by positivity),
    inv_mul_le_iff₀ hnpos, mul_one]
  exact hS1

/-- The integral of a Birkhoff average of an indicator function for an invariant measure. -/
private lemma integral_birkhoffAverage_indicator {ν : Measure X} [IsProbabilityMeasure ν]
    {T : X → X} (hν : MeasurePreserving T ν ν) {B : Set X} (hB : MeasurableSet B) {n : ℕ}
    (hn : 1 ≤ n) :
    ∫ y, birkhoffAverage ℝ T (B.indicator fun _ ↦ (1 : ℝ)) n y ∂ν = ν.real B := by
  have hpt : birkhoffAverage ℝ T (B.indicator fun _ ↦ (1 : ℝ)) n = fun y ↦
      (n : ℝ)⁻¹ * ∑ k ∈ Finset.range n, (T^[k] ⁻¹' B).indicator (fun _ ↦ (1 : ℝ)) y := rfl
  have hmeas : ∀ k, MeasurableSet (T^[k] ⁻¹' B) := fun k ↦ (hν.iterate k).measurable hB
  rw [hpt, integral_const_mul,
    integral_finsetSum _ fun k _ ↦ (integrable_const (1 : ℝ)).indicator (hmeas k)]
  simp_rw [integral_indicator_const _ (hmeas _), (hν.iterate _).measureReal_preimage
    hB.nullMeasurableSet]
  have hnpos : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.one_le_iff_ne_zero.1 hn)
  simp [hnpos]

omit mX in
/-- On an invariant set `E`, the Birkhoff averages of `1_A` are those of `1_{A ∩ E}`. -/
private lemma indicator_birkhoffAverage {T : X → X} {E : Set X} (hTE : T ⁻¹' E = E)
    (A : Set X) (n : ℕ) (y : X) :
    E.indicator (birkhoffAverage ℝ T (A.indicator fun _ ↦ (1 : ℝ)) n) y =
      birkhoffAverage ℝ T ((A ∩ E).indicator fun _ ↦ (1 : ℝ)) n y := by
  by_cases hy : y ∈ E
  · rw [Set.indicator_of_mem hy, birkhoffAverage, birkhoffAverage, birkhoffSum, birkhoffSum]
    congr 1
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    have hk : T^[k] y ∈ E := (iterate_mem_iff hTE k y).2 hy
    by_cases hA : T^[k] y ∈ A
    · simp [hA, hk]
    · simp [hA]
  · rw [Set.indicator_of_notMem hy, birkhoffAverage, birkhoffSum]
    have : ∀ k ∈ Finset.range n, ((A ∩ E).indicator fun _ ↦ (1 : ℝ)) (T^[k] y) = 0 :=
      fun k _ ↦ Set.indicator_of_notMem (fun h ↦ hy ((iterate_mem_iff hTE k y).1 h.2)) _
    rw [Finset.sum_eq_zero this, smul_zero]

/-- For a `T`-invariant measurable set `E` and a measurable set `A` whose Birkhoff averages
converge a.e. to the constant `ν.real A`, the events `A` and `E` are independent. -/
private lemma measureReal_inter_eq_mul {ν : Measure X} [IsProbabilityMeasure ν] {T : X → X}
    (hν : MeasurePreserving T ν ν) {E : Set X} (hE : MeasurableSet E) (hTE : T ⁻¹' E = E)
    {A : Set X} (hA : MeasurableSet A)
    (h : ∀ᵐ y ∂ν, Tendsto (fun n ↦ birkhoffAverage ℝ T (A.indicator fun _ ↦ (1 : ℝ)) n y)
      atTop (𝓝 (ν.real A))) :
    ν.real (A ∩ E) = ν.real A * ν.real E := by
  set F : ℕ → X → ℝ := fun n ↦ E.indicator (birkhoffAverage ℝ T (A.indicator fun _ ↦ 1) n)
  have hF : ∀ n, F n = birkhoffAverage ℝ T ((A ∩ E).indicator fun _ ↦ (1 : ℝ)) n :=
    fun n ↦ funext (indicator_birkhoffAverage hTE A n)
  have hlim : Tendsto (fun n ↦ ∫ y, F n y ∂ν) atTop
      (𝓝 (∫ y, E.indicator (fun _ ↦ ν.real A) y ∂ν)) := by
    refine tendsto_integral_of_dominated_convergence (fun _ ↦ (1 : ℝ)) (fun n ↦ ?_)
      (integrable_const _) (fun n ↦ Eventually.of_forall fun y ↦ ?_) ?_
    · rw [hF]
      exact (measurable_birkhoffAverage_of hν.measurable
        (measurable_const.indicator (hA.inter hE)) n).aestronglyMeasurable
    · rw [hF, Real.norm_eq_abs]
      exact abs_birkhoffAverage_indicator_le T _ n y
    · filter_upwards [h] with y hy
      by_cases hyE : y ∈ E
      · simpa [F, Set.indicator_of_mem hyE] using hy
      · simp [F, Set.indicator_of_notMem hyE]
  have hconst : ∀ᶠ n in atTop, ∫ y, F n y ∂ν = ν.real (A ∩ E) := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    rw [hF]
    exact integral_birkhoffAverage_indicator hν (hA.inter hE) hn
  have := tendsto_nhds_unique (tendsto_const_nhds.congr' (EventuallyEq.symm hconst)) hlim
  rw [this, integral_indicator_const _ hE, smul_eq_mul, mul_comm]

/-- A measure-preserving map is ergodic as soon as, for every set `A` of a generating π-system,
the Birkhoff averages of `1_A` converge a.e. to the constant `ν.real A`. -/
private lemma ergodic_of_tendsto_birkhoffAverage {ν : Measure X} [IsProbabilityMeasure ν]
    {T : X → X} (hν : MeasurePreserving T ν ν) {C : Set (Set X)} (hgen : mX = generateFrom C)
    (hC : IsPiSystem C) (hCm : ∀ A ∈ C, MeasurableSet A)
    (h : ∀ A ∈ C, ∀ᵐ y ∂ν, Tendsto (fun n ↦ birkhoffAverage ℝ T (A.indicator fun _ ↦ (1 : ℝ))
      n y) atTop (𝓝 (ν.real A))) :
    Ergodic T ν := by
  refine Ergodic.of_preimage_eq hν fun E hE hTE ↦ ?_
  have key : ∀ A ∈ C, ν (A ∩ E) = ν A * ν E := fun A hA ↦ by
    have := measureReal_inter_eq_mul hν hE hTE (hCm A hA) (h A hA)
    simp only [measureReal_def] at this
    rw [← ENNReal.toReal_mul] at this
    exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _)
      (ENNReal.mul_ne_top (measure_ne_top _ _) (measure_ne_top _ _))).1 this
  have hres : ν.restrict E = ν E • ν := by
    refine ext_of_generate_finite C hgen hC (fun A hA ↦ ?_) ?_
    · rw [Measure.restrict_apply (hCm A hA), Measure.smul_apply, smul_eq_mul, key A hA,
        mul_comm]
    · simp
  have hEE : ν E = ν E * ν E := by
    have := congrArg (fun ρ : Measure X ↦ ρ E) hres
    simpa [Measure.restrict_apply hE] using this
  rw [Filter.eventuallyEmptyOrUniv_iff']
  rcases eq_or_ne (ν E) 0 with h0 | h0
  · exact Or.inl (ae_eq_empty.2 h0)
  · refine Or.inr (ae_eq_univ.2 ((prob_compl_eq_zero_iff hE).2 ?_))
    exact ((ENNReal.mul_right_inj h0 (measure_ne_top _ _)).1 (by rw [mul_one]; exact hEE)).symm

end Aux

section CondKernel

variable {X : Type*} {m : MeasurableSpace X} [mX : MeasurableSpace X] [StandardBorelSpace X]

/-- The conditional expectation kernel of `μ` given a sub-σ-algebra `m ≤ mX`, viewed as a kernel
from `X` with its own σ-algebra `mX`. -/
private def condKernel (μ : Measure X) [IsFiniteMeasure μ]
    (hm : m ≤ mX) : Kernel X X :=
  (condExpKernel μ m).comap id (measurable_id'' hm)

/-- `condKernel` is a Markov kernel. -/
private lemma isMarkovKernel_condKernel (μ : Measure X) [IsFiniteMeasure μ]
    (hm : m ≤ mX) : IsMarkovKernel (condKernel μ hm) := by
  unfold condKernel
  infer_instance

/-- Disintegration: `μ.bind (condKernel μ hm) = μ`. -/
private lemma bind_condKernel (μ : Measure X) [IsFiniteMeasure μ]
    (hm : m ≤ mX) : μ.bind (condKernel μ hm) = μ := by
  ext s hs
  rw [Measure.bind_apply hs (Kernel.measurable _).aemeasurable]
  have h1 : ∀ x, condKernel μ hm x s = condExpKernel μ m x s := fun _ ↦ rfl
  simp_rw [h1]
  rw [← lintegral_trim hm (measurable_condExpKernel hs)]
  conv_rhs => rw [← condExpKernel_comp_trim (μ := μ) hm]
  rw [Measure.bind_apply hs (Kernel.measurable _).aemeasurable]

/-- A `μ`-a.e. property holds `condKernel μ hm x`-a.e. for `μ`-a.e. `x`. -/
private lemma ae_ae_condKernel_of_ae {μ : Measure X} [IsFiniteMeasure μ]
    (hm : m ≤ mX) {p : X → Prop} (h : ∀ᵐ y ∂μ, p y) :
    ∀ᵐ x ∂μ, ∀ᵐ y ∂condKernel μ hm x, p y :=
  Measure.ae_ae_of_ae_comp (by rwa [bind_condKernel μ hm])

/-- The kernel computes conditional probabilities. -/
private lemma condKernel_real_ae_eq {μ : Measure X} [IsFiniteMeasure μ]
    (hm : m ≤ mX) {s : Set X} (hs : MeasurableSet s) :
    (fun x ↦ (condKernel μ hm x).real s) =ᵐ[μ] μ⟦s | m⟧ :=
  condExpKernel_ae_eq_condExp hm hs

/-- For an `m`-measurable set `S`, `condKernel μ hm x` is concentrated on `S` or on `Sᶜ`
according to whether `x ∈ S`, for `μ`-a.e. `x`. -/
private lemma ae_ae_mem_iff {μ : Measure X} [IsFiniteMeasure μ]
    (hm : m ≤ mX) {S : Set X} (hS : MeasurableSet[m] S) :
    ∀ᵐ x ∂μ, ∀ᵐ y ∂condKernel μ hm x, (y ∈ S ↔ x ∈ S) := by
  have hSm : MeasurableSet S := hm _ hS
  have h1 : μ⟦S | m⟧ = S.indicator (fun _ ↦ (1 : ℝ)) :=
    condExp_of_stronglyMeasurable hm (stronglyMeasurable_const.indicator hS)
      ((integrable_const (1 : ℝ)).indicator hSm)
  have := isMarkovKernel_condKernel μ hm
  filter_upwards [condKernel_real_ae_eq hm hSm] with x hx
  rw [h1] at hx
  by_cases hxS : x ∈ S
  · rw [Set.indicator_of_mem hxS, measureReal_def, ENNReal.toReal_eq_one_iff] at hx
    have h3 : condKernel μ hm x Sᶜ = 0 := (prob_compl_eq_zero_iff hSm).2 hx
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 h3] with y hy
    simp only [Set.mem_compl_iff, not_not] at hy
    simp [hy, hxS]
  · rw [Set.indicator_of_notMem hxS, measureReal_def, ENNReal.toReal_eq_zero_iff] at hx
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 (hx.resolve_right (measure_ne_top _ _))]
      with y hy
    simp [hy, hxS]

/-- An `m`-measurable real function is `condKernel μ hm x`-a.e. equal to its value at `x`, for
`μ`-a.e. `x`. -/
private lemma ae_ae_eq_of_measurable {μ : Measure X} [IsFiniteMeasure μ]
    (hm : m ≤ mX) {h : X → ℝ} (hh : Measurable[m] h) :
    ∀ᵐ x ∂μ, ∀ᵐ y ∂condKernel μ hm x, h y = h x := by
  have hq : ∀ q : ℚ, ∀ᵐ x ∂μ, ∀ᵐ y ∂condKernel μ hm x,
      (y ∈ h ⁻¹' Set.Iio (q : ℝ) ↔ x ∈ h ⁻¹' Set.Iio (q : ℝ)) :=
    fun q ↦ ae_ae_mem_iff hm (hh measurableSet_Iio)
  filter_upwards [ae_all_iff.2 hq] with x hx
  filter_upwards [ae_all_iff.2 hx] with y hy
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn hlt
    exact absurd ((hy q).1 hq1) (not_lt.2 hq2.le)
  · obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn hlt
    exact absurd ((hy q).2 hq1) (not_lt.2 hq2.le)

omit [StandardBorelSpace X] in
/-- Conditional probabilities given the invariant σ-algebra are invariant. -/
private lemma condExp_preimage_ae_eq {μ : Measure X} [IsFiniteMeasure μ] {T : X → X}
    (hμ : MeasurePreserving T μ μ) {A : Set X} (hA : MeasurableSet A) :
    μ⟦T ⁻¹' A | invariants T⟧ =ᵐ[μ] μ⟦A | invariants T⟧ := by
  have hm := invariants_le T
  have hTA : MeasurableSet (T ⁻¹' A) := hμ.measurable hA
  refine (ae_eq_condExp_of_forall_setIntegral_eq hm ((integrable_const (1 : ℝ)).indicator hTA)
    (fun s _ _ ↦ integrable_condExp.integrableOn) (fun s hs _ ↦ ?_)
    stronglyMeasurable_condExp.aestronglyMeasurable).symm
  obtain ⟨hsm, hsT⟩ := measurableSet_invariants.1 hs
  rw [setIntegral_condExp hm ((integrable_const (1 : ℝ)).indicator hA) hs,
    setIntegral_indicator hA, setIntegral_indicator hTA, setIntegral_const, setIntegral_const]
  have : s ∩ T ⁻¹' A = T ⁻¹' (s ∩ A) := by rw [Set.preimage_inter, hsT]
  rw [this, hμ.measureReal_preimage (hsm.inter hA).nullMeasurableSet]

/-- The conditional measures given the invariant σ-algebra are a.e. invariant on each set. -/
private lemma ae_condKernel_preimage {μ : Measure X} [IsFiniteMeasure μ] {T : X → X}
    (hμ : MeasurePreserving T μ μ) {A : Set X} (hA : MeasurableSet A) :
    ∀ᵐ x ∂μ, condKernel μ (invariants_le T) x (T ⁻¹' A) = condKernel μ (invariants_le T) x A := by
  have := isMarkovKernel_condKernel μ (invariants_le T)
  filter_upwards [condKernel_real_ae_eq (invariants_le T) (hμ.measurable hA),
    condKernel_real_ae_eq (invariants_le T) hA, condExp_preimage_ae_eq hμ hA] with x h1 h2 h3
  have h4 : (condKernel μ (invariants_le T) x).real (T ⁻¹' A) =
      (condKernel μ (invariants_le T) x).real A := by
    rw [h1, h3, ← h2]
  simp only [measureReal_def] at h4
  exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).1 h4

/-- Under the conditional measures given the invariant σ-algebra, the Birkhoff averages of an
indicator converge a.e. to a constant, the conditional measure of the set. -/
private lemma ae_ae_tendsto_condKernel {μ : Measure X} [IsProbabilityMeasure μ] {T : X → X}
    (hμ : MeasurePreserving T μ μ) {A : Set X} (hA : MeasurableSet A) :
    ∀ᵐ x ∂μ, ∀ᵐ y ∂condKernel μ (invariants_le T) x,
      Tendsto (fun n ↦ birkhoffAverage ℝ T (A.indicator fun _ ↦ (1 : ℝ)) n y) atTop
        (𝓝 ((condKernel μ (invariants_le T) x).real A)) := by
  have hm := invariants_le T
  have hB := ae_tendsto_birkhoffAverage_condExp hμ (g := A.indicator fun _ ↦ (1 : ℝ))
    (measurable_const.indicator hA) (C := 1) (fun y ↦ by by_cases hy : y ∈ A <;> simp [hy])
  filter_upwards [ae_ae_condKernel_of_ae hm hB,
    ae_ae_eq_of_measurable hm stronglyMeasurable_condExp.measurable,
    condKernel_real_ae_eq hm hA] with x hx1 hx2 hx3
  filter_upwards [hx1, hx2] with y hy1 hy2
  rw [hx3, ← hy2]
  exact hy1

end CondKernel

variable {X : Type*} [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]

/-- The ergodic decomposition of an invariant Borel probability measure of a continuous map of a
compact metric space. Blueprint node `erg:decomposition`. -/
theorem exists_ergodicDecomposition {T : X → X} (_hT : Continuous T) (μ : Measure X)
    [IsProbabilityMeasure μ] (hμ : MeasurePreserving T μ μ) :
    ∃ κ : Kernel X X, IsMarkovKernel κ ∧ μ.bind κ = μ ∧ ∀ᵐ x ∂μ, Ergodic T (κ x) := by
  set 𝒜 := generateSetAlgebra (countableGeneratingSet X) with h𝒜
  have h𝒜c : 𝒜.Countable := countable_generateSetAlgebra countable_countableGeneratingSet
  have hgen : ‹MeasurableSpace X› = generateFrom 𝒜 := by
    rw [h𝒜, generateFrom_generateSetAlgebra_eq, generateFrom_countableGeneratingSet]
  have hπ : IsPiSystem 𝒜 := isSetAlgebra_generateSetAlgebra.isSetRing.isSetSemiring.isPiSystem
  have h𝒜m : ∀ A ∈ 𝒜, MeasurableSet A := fun A hA ↦ by
    rw [hgen]
    exact measurableSet_generateFrom hA
  have : Countable 𝒜 := h𝒜c.to_subtype
  have hm := invariants_le T
  have := isMarkovKernel_condKernel μ hm
  refine ⟨condKernel μ hm, this, bind_condKernel μ hm, ?_⟩
  have h1 : ∀ᵐ x ∂μ, ∀ A : 𝒜, condKernel μ hm x (T ⁻¹' A) = condKernel μ hm x A :=
    ae_all_iff.2 fun A ↦ ae_condKernel_preimage hμ (h𝒜m A A.2)
  have h2 : ∀ᵐ x ∂μ, ∀ A : 𝒜, ∀ᵐ y ∂condKernel μ hm x,
      Tendsto (fun n ↦ birkhoffAverage ℝ T ((A : Set X).indicator fun _ ↦ (1 : ℝ)) n y) atTop
        (𝓝 ((condKernel μ hm x).real A)) :=
    ae_all_iff.2 fun A ↦ ae_ae_tendsto_condKernel hμ (h𝒜m A A.2)
  filter_upwards [h1, h2] with x hx1 hx2
  have hpres : MeasurePreserving T (condKernel μ hm x) (condKernel μ hm x) := by
    refine ⟨hμ.measurable, ext_of_generate_finite 𝒜 hgen hπ (fun A hA ↦ ?_) ?_⟩
    · rw [Measure.map_apply hμ.measurable (h𝒜m A hA)]
      exact hx1 ⟨A, hA⟩
    · rw [Measure.map_apply hμ.measurable MeasurableSet.univ, Set.preimage_univ]
  exact ergodic_of_tendsto_birkhoffAverage hpres hgen hπ h𝒜m fun A hA ↦ hx2 ⟨A, hA⟩

end Kolmogorov.Ergodic
