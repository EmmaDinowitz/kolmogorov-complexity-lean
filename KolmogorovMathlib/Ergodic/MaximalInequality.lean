/-
Copyright (c) 2026 Emma Dinowitz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emma Dinowitz
-/
import Mathlib.Dynamics.BirkhoffSum.QuasiMeasurePreserving
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# The maximal ergodic inequality

Mathlib has no maximal ergodic theorem. This module proves the maximal ergodic lemma (Garsia's
proof) and the weak-type maximal inequality for Birkhoff averages of an integrable function
under a measure-preserving map of a finite measure space:

* `setIntegral_nonneg_of_maximal` (maximal ergodic lemma): `∫_{E} g ≥ 0`, where
  `E = {x | ∃ n ≥ 1, ∑_{k<n} g(T^k x) > 0}`.
* `measure_maximal_birkhoffAverage_le` (maximal inequality):
  `λ μ{x | ∃ n ≥ 1, (1/n) ∑_{k<n} g(T^k x) > λ} ≤ ∫ |g| dμ` for `λ > 0`.

Proof of the lemma: with `S_k` the Birkhoff sums and `M_N = max (0, S_1, …, S_N)`, the identity
`S_{k+1} = g + S_k ∘ T` gives `M_N - M_N ∘ T ≤ g` on `E_N = {M_N > 0}`; integrating over `E_N` and
using `∫ M_N ∘ T = ∫ M_N` gives `∫_{E_N} g ≥ 0`, and `E_N ↑ E`. A general integrable `g` is
first replaced by a measurable representative. The maximal inequality is the lemma for `g - λ`.

They are the classical inputs of the effective Birkhoff theorem used for input (I2) of the note
*Orbit complexity of Martin-Löf random points equals entropy*. Blueprint node `erg:maximal`.
-/

noncomputable section

open MeasureTheory Filter Topology

namespace Kolmogorov.Ergodic

variable {X : Type*} [MeasurableSpace X]

/-- The running maximum `M_N = max (0, S_1, …, S_N)` of the Birkhoff sums `S_k` of `g`. -/
private def maxBirkhoffSum (T : X → X) (g : X → ℝ) : ℕ → X → ℝ
  | 0 => fun _ ↦ 0
  | N + 1 => fun x ↦ max (maxBirkhoffSum T g N x) (birkhoffSum T g (N + 1) x)

omit [MeasurableSpace X] in
/-- `M_N` is nonnegative. -/
private lemma maxBirkhoffSum_nonneg (T : X → X) (g : X → ℝ) (N : ℕ) (x : X) :
    0 ≤ maxBirkhoffSum T g N x := by
  induction N with
  | zero => exact le_rfl
  | succ N ih => exact ih.trans (le_max_left _ _)

omit [MeasurableSpace X] in
/-- `M_N` dominates every Birkhoff sum `S_k` with `k ≤ N`. -/
private lemma birkhoffSum_le_maxBirkhoffSum (T : X → X) (g : X → ℝ) {k N : ℕ} (hk : k ≤ N)
    (x : X) : birkhoffSum T g k x ≤ maxBirkhoffSum T g N x := by
  induction N with
  | zero =>
    obtain rfl : k = 0 := by omega
    simp [maxBirkhoffSum]
  | succ N ih =>
    rcases Nat.lt_or_ge k (N + 1) with h | h
    · exact (ih (by omega)).trans (le_max_left _ _)
    · obtain rfl : k = N + 1 := by omega
      exact le_max_right _ _

omit [MeasurableSpace X] in
/-- `M_N` is bounded by any nonnegative bound of all Birkhoff sums `S_k`, `1 ≤ k ≤ N`. -/
private lemma maxBirkhoffSum_le (T : X → X) (g : X → ℝ) {N : ℕ} {x : X} {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ k, 1 ≤ k → k ≤ N → birkhoffSum T g k x ≤ c) : maxBirkhoffSum T g N x ≤ c := by
  induction N with
  | zero => exact hc
  | succ N ih =>
    exact max_le (ih fun k hk hkN ↦ h k hk (by omega)) (h (N + 1) (by omega) le_rfl)

omit [MeasurableSpace X] in
/-- `M_N` is monotone in `N`. -/
private lemma maxBirkhoffSum_mono (T : X → X) (g : X → ℝ) (x : X) :
    Monotone fun N ↦ maxBirkhoffSum T g N x :=
  monotone_nat_of_le_succ fun _ ↦ le_max_left _ _

omit [MeasurableSpace X] in
/-- Garsia's pointwise bound `M_N ≤ max 0 (g + M_N ∘ T)`, from `S_{k+1} = g + S_k ∘ T`. -/
private lemma maxBirkhoffSum_le_max (T : X → X) (g : X → ℝ) (N : ℕ) (x : X) :
    maxBirkhoffSum T g N x ≤ max 0 (g x + maxBirkhoffSum T g N (T x)) := by
  refine maxBirkhoffSum_le T g (le_max_left _ _) fun k hk hkN ↦ ?_
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rw [birkhoffSum_succ_apply']
  exact (add_le_add_right (birkhoffSum_le_maxBirkhoffSum T g (by omega) (T x)) _).trans
    (le_max_right _ _)

/-- The maximal ergodic lemma for a measurable integrand. -/
private lemma setIntegral_nonneg_of_maximal_of_measurable {μ : Measure X} [IsFiniteMeasure μ]
    {T : X → X} (hT : MeasurePreserving T μ μ) {g : X → ℝ} (hgm : Measurable g)
    (hg : Integrable g μ) :
    0 ≤ ∫ x in {x | ∃ n, 1 ≤ n ∧ 0 < birkhoffSum T g n x}, g x ∂μ := by
  have hSm : ∀ n, Measurable (birkhoffSum T g n) := fun n ↦
    Finset.measurable_sum _ fun k _ ↦ hgm.comp (hT.measurable.iterate k)
  have hSi : ∀ n, Integrable (birkhoffSum T g n) μ := fun n ↦
    integrable_finsetSum _ fun k _ ↦ (hT.iterate k).integrable_comp_of_integrable hg
  have hMm : ∀ N, Measurable (maxBirkhoffSum T g N) := by
    intro N
    induction N with
    | zero => exact measurable_const
    | succ N ih => exact ih.max (hSm _)
  have hMi : ∀ N, Integrable (maxBirkhoffSum T g N) μ := by
    intro N
    induction N with
    | zero => exact integrable_const (0 : ℝ)
    | succ N ih => exact ih.sup (hSi _)
  set E : ℕ → Set X := fun N ↦ {x | 0 < maxBirkhoffSum T g N x} with hE_def
  have hEm : ∀ N, MeasurableSet (E N) := fun N ↦ measurableSet_lt measurable_const (hMm N)
  have step : ∀ N, 0 ≤ ∫ x in E N, g x ∂μ := by
    intro N
    have hMTi : Integrable (fun x ↦ maxBirkhoffSum T g N (T x)) μ :=
      hT.integrable_comp_of_integrable (hMi N)
    have hinv : ∫ x, maxBirkhoffSum T g N (T x) ∂μ = ∫ x, maxBirkhoffSum T g N x ∂μ := by
      have := integral_map hT.measurable.aemeasurable (hMm N).aestronglyMeasurable
        (μ := μ) (f := maxBirkhoffSum T g N)
      rw [hT.map_eq] at this
      exact this.symm
    have hset : ∫ x in E N, maxBirkhoffSum T g N x ∂μ = ∫ x, maxBirkhoffSum T g N x ∂μ :=
      setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx ↦
        le_antisymm (not_lt.1 hx) (maxBirkhoffSum_nonneg T g N x)
    calc (0 : ℝ) = ∫ x in E N, maxBirkhoffSum T g N x ∂μ
          - ∫ x, maxBirkhoffSum T g N (T x) ∂μ := by rw [hset, hinv, sub_self]
      _ ≤ ∫ x in E N, maxBirkhoffSum T g N x ∂μ
          - ∫ x in E N, maxBirkhoffSum T g N (T x) ∂μ :=
        sub_le_sub_left (setIntegral_le_integral hMTi
          (ae_of_all _ fun x ↦ maxBirkhoffSum_nonneg T g N (T x))) _
      _ = ∫ x in E N, (maxBirkhoffSum T g N x - maxBirkhoffSum T g N (T x)) ∂μ :=
        (integral_sub (hMi N).integrableOn hMTi.integrableOn).symm
      _ ≤ ∫ x in E N, g x ∂μ := by
        refine setIntegral_mono_on ((hMi N).sub hMTi).integrableOn hg.integrableOn (hEm N) ?_
        intro x hx
        have h1 := maxBirkhoffSum_le_max T g N x
        have h2 : (0 : ℝ) < maxBirkhoffSum T g N x := hx
        rcases le_max_iff.1 h1 with h | h
        · exact absurd h (not_le.2 h2)
        · linarith
  have hU : ⋃ N, E N = {x | ∃ n, 1 ≤ n ∧ 0 < birkhoffSum T g n x} := by
    ext x
    simp only [hE_def, Set.mem_iUnion, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨N, hN⟩
      by_contra h
      push Not at h
      exact hN.not_ge (maxBirkhoffSum_le T g le_rfl fun k hk _ ↦ h k hk)
    · rintro ⟨n, -, hpos⟩
      exact ⟨n, hpos.trans_le (birkhoffSum_le_maxBirkhoffSum T g le_rfl x)⟩
  have hmono : Monotone E := fun N N' h x hx ↦ lt_of_lt_of_le hx (maxBirkhoffSum_mono T g x h)
  have hlim := tendsto_setIntegral_of_monotone hEm hmono hg.integrableOn
  rw [hU] at hlim
  exact ge_of_tendsto' hlim step

/-- The maximal ergodic lemma (Garsia): for an integrable `g` and a measure-preserving `T` of a
finite measure, the integral of `g` over the set where some Birkhoff sum of `g` is positive is
nonnegative. Blueprint node `erg:maximal`. -/
theorem setIntegral_nonneg_of_maximal {μ : Measure X} [IsFiniteMeasure μ] {T : X → X}
    (hT : MeasurePreserving T μ μ) {g : X → ℝ} (hg : Integrable g μ) :
    0 ≤ ∫ x in {x | ∃ n, 1 ≤ n ∧ 0 < birkhoffSum T g n x}, g x ∂μ := by
  have hgg' : g =ᵐ[μ] hg.1.mk g := hg.1.ae_eq_mk
  have hS : ∀ᵐ x ∂μ, ∀ n, birkhoffSum T g n x = birkhoffSum T (hg.1.mk g) n x :=
    ae_all_iff.2 fun n ↦ hT.quasiMeasurePreserving.birkhoffSum_ae_eq_of_ae_eq hgg' n
  have hE : {x | ∃ n, 1 ≤ n ∧ 0 < birkhoffSum T g n x}
      =ᵐ[μ] {x | ∃ n, 1 ≤ n ∧ 0 < birkhoffSum T (hg.1.mk g) n x} :=
    eventuallyEqSet_iff.2 (hS.mono fun x hx ↦ by simp only [Set.mem_ofPred_eq, hx])
  rw [setIntegral_congr_set hE, integral_congr_ae (ae_restrict_of_ae hgg')]
  exact setIntegral_nonneg_of_maximal_of_measurable hT hg.1.stronglyMeasurable_mk.measurable
    (hg.congr hgg')

/-- The maximal inequality: `λ μ{x | ∃ n ≥ 1, A_n g(x) > λ} ≤ ∫ |g| dμ` for `λ > 0`, where `A_n g`
is the Birkhoff average. Blueprint node `erg:maximal`. -/
theorem measure_maximal_birkhoffAverage_le {μ : Measure X} [IsFiniteMeasure μ] {T : X → X}
    (hT : MeasurePreserving T μ μ) {g : X → ℝ} (hg : Integrable g μ) {lam : ℝ} (_hlam : 0 < lam) :
    lam * μ.real {x | ∃ n, 1 ≤ n ∧ lam < birkhoffAverage ℝ T g n x} ≤ ∫ x, |g x| ∂μ := by
  have key := setIntegral_nonneg_of_maximal hT (hg.sub (integrable_const lam))
  have hset : {x | ∃ n, 1 ≤ n ∧ 0 < birkhoffSum T (g - fun _ ↦ lam) n x}
      = {x | ∃ n, 1 ≤ n ∧ lam < birkhoffAverage ℝ T g n x} := by
    ext x
    simp only [Set.mem_ofPred_eq]
    refine exists_congr fun n ↦ and_congr_right fun hn ↦ ?_
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    have hS : birkhoffSum T (g - fun _ ↦ lam) n x = birkhoffSum T g n x - n * lam := by
      simp [birkhoffSum, Finset.sum_sub_distrib]
    have hA : birkhoffAverage ℝ T g n x = birkhoffSum T g n x / n := by
      simp [birkhoffAverage, div_eq_inv_mul]
    rw [hS, hA, lt_div_iff₀ hn']
    constructor <;> intro h <;> linarith
  rw [hset] at key
  set F := {x | ∃ n, 1 ≤ n ∧ lam < birkhoffAverage ℝ T g n x}
  have h1 : ∫ x in F, ((g - fun _ ↦ lam : X → ℝ)) x ∂μ = ∫ x in F, g x ∂μ - μ.real F * lam := by
    simp only [Pi.sub_apply]
    rw [integral_sub hg.integrableOn (integrable_const lam), setIntegral_const, smul_eq_mul]
  have h2 : ∫ x in F, g x ∂μ ≤ ∫ x in F, |g x| ∂μ :=
    integral_mono hg.integrableOn hg.abs.integrableOn fun x ↦ le_abs_self _
  have h3 : ∫ x in F, |g x| ∂μ ≤ ∫ x, |g x| ∂μ :=
    setIntegral_le_integral hg.abs (ae_of_all _ fun x ↦ abs_nonneg _)
  linarith

end Kolmogorov.Ergodic
