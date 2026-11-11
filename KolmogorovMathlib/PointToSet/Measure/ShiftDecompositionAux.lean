/-
Copyright (c) 2026 Emma Dinowitz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emma Dinowitz
-/
import KolmogorovMathlib.PointToSet.Measure.Shift
import KolmogorovMathlib.PointToSet.Measure.Decomposition
import Mathlib.Probability.Martingale.Convergence
import Mathlib.MeasureTheory.Measure.Decomposition.IntegralRNDeriv
import Mathlib.Probability.BorelCantelli
import Mathlib.Probability.Distributions.Bernoulli
import Mathlib.Probability.ProductMeasure

/-!
# Cylinders on a shift: helper material for `ShiftDecomposition`

On a sequence space `ℕ → α` with a first-difference metric `dist x y = β ^ firstDiff x y`
(`0 < β < 1`), the cylinders `[x↾n]` are Borel, the cylinder masses `μ[x↾n]` and
`μ_ω[x↾n]` are Borel functions of `x` and of `(ω, x)`, and the packing argument of the
domination lemma (Lemma 7.1 of E. Dinowitz, *Entropy of non-invariant measures and orbit
complexity of random points*) works with the partition into cylinders, with no change of scale:

* `measurableSet_cylinder`, `measurableSet_mem_cylinder`, `measurable_measure_cylinder`,
  `measurable_kernel_cylinder`: measurability;
* `measure_setOf_mul_lt_measure_cylinder_le`: the cylinders `C` of length `n` with
  `c ν(C) < μ(C)` have total `ν`-mass at most `μ(X) / c`;
* `ae_measure_cylinder_ne_zero`: `ν[x↾n] > 0` for all `n`, `ν`-almost everywhere.

On Cantor space with `cantorMetricSpace`: `infoBits_two_inv_pow`, `cantor_hd`,
`measurableSet_cantor_cylinder`, and `tendsto_natCast_add_div_natCast`.

Martingale convergence along cylinders (for Proposition 7.6(iii)): `prefixSigma` (the
σ-algebra of `x↾n`), `setLIntegral_ratio_cylinder` and `ae_tendsto_logb_ratio_cylinder`
(`log₂ (ν[x↾n] / μ[x↾n])` converges `ν`-almost everywhere when `ν ≪ μ`, by Lévy's upward
theorem).

Example 7.8 (the revealed blocks `J_k = [2^k, 2^{k+1})`, revealed independently with
probability `1/k`): `revealProb`, `revealedSet`, `revealIndicatorMeasure`, `revealCount`;
the two Borel–Cantelli lemmas `ae_frequently_reveal` and `ae_eventually_sparse`; the
deterministic density computation `density_compl_revealedSet` (`ℕ \ S` has lower density `1/2`
and upper density `1`); and the mean bound `integral_revealCount_le`
(`E #([0, n) ∩ S) ≤ 12 n / log₂ n`).

Blueprint node `meas:examples`.
-/

namespace Kolmogorov.PointToSet

open Filter Set MeasureTheory ProbabilityTheory
open scoped Topology ENNReal NNReal

/-! ### Cylinders for a first-difference metric -/

section cylinders

variable {α : Type*} [MetricSpace (ℕ → α)] {β : ℝ}

/-- For a first-difference metric the coordinates are locally constant: `{x | x i = a}` is
open. -/
theorem isOpen_setOf_apply_eq (hβ : 0 < β) (hβ₁ : β < 1)
    (hd : ∀ x y : ℕ → α, x ≠ y → dist x y = β ^ PiNat.firstDiff x y) (i : ℕ) (a : α) :
    IsOpen {x : ℕ → α | x i = a} := by
  refine Metric.isOpen_iff.2 fun x hx ↦ ⟨β ^ i, pow_pos hβ i, fun y hy ↦ ?_⟩
  simp only [mem_ofPred_eq] at hx ⊢
  rw [← hx]
  by_cases hxy : y = x
  · rw [hxy]
  rw [Metric.mem_ball, hd y x hxy] at hy
  exact PiNat.apply_eq_of_lt_firstDiff ((pow_lt_pow_iff_right_of_lt_one₀ hβ hβ₁).1 hy)

variable [MeasurableSpace (ℕ → α)] [BorelSpace (ℕ → α)]

/-- Cylinders are Borel for a first-difference metric. -/
theorem measurableSet_cylinder (hβ : 0 < β) (hβ₁ : β < 1)
    (hd : ∀ x y : ℕ → α, x ≠ y → dist x y = β ^ PiNat.firstDiff x y) (x : ℕ → α) (n : ℕ) :
    MeasurableSet (PiNat.cylinder x n) := by
  have h : PiNat.cylinder x n = ⋂ i ∈ Iio n, {y : ℕ → α | y i = x i} := by
    ext y
    simp [PiNat.mem_cylinder_iff]
  rw [h]
  exact MeasurableSet.biInter (to_countable _) fun i _ ↦
    (isOpen_setOf_apply_eq hβ hβ₁ hd i (x i)).measurableSet

/-- The relation `y ∈ [x↾n]` is jointly Borel on a countable alphabet. -/
theorem measurableSet_mem_cylinder [Countable α] (hβ : 0 < β) (hβ₁ : β < 1)
    (hd : ∀ x y : ℕ → α, x ≠ y → dist x y = β ^ PiNat.firstDiff x y) (n : ℕ) :
    MeasurableSet {q : (ℕ → α) × (ℕ → α) | q.2 ∈ PiNat.cylinder q.1 n} := by
  have h : {q : (ℕ → α) × (ℕ → α) | q.2 ∈ PiNat.cylinder q.1 n} =
      ⋂ i ∈ Iio n, ⋃ a : α,
        (Prod.fst ⁻¹' {y : ℕ → α | y i = a}) ∩ (Prod.snd ⁻¹' {y : ℕ → α | y i = a}) := by
    ext q
    simp [PiNat.mem_cylinder_iff]
  rw [h]
  refine MeasurableSet.biInter (to_countable _) fun i _ ↦ MeasurableSet.iUnion fun a ↦ ?_
  have ho := (isOpen_setOf_apply_eq hβ hβ₁ hd i a).measurableSet
  exact (measurable_fst ho).inter (measurable_snd ho)

/-- The mass `μ[x↾n]` of the cylinder about `x` is a Borel function of `x`. -/
theorem measurable_measure_cylinder [Countable α] (hβ : 0 < β) (hβ₁ : β < 1)
    (hd : ∀ x y : ℕ → α, x ≠ y → dist x y = β ^ PiNat.firstDiff x y) (μ : Measure (ℕ → α))
    [SFinite μ] (n : ℕ) : Measurable fun x ↦ μ (PiNat.cylinder x n) :=
  measurable_measure_prodMk_left (measurableSet_mem_cylinder hβ hβ₁ hd n)

/-- The mass `μ_ω[x↾n]` is a Borel function of the label and the point. -/
theorem measurable_kernel_cylinder [Countable α] (hβ : 0 < β) (hβ₁ : β < 1)
    (hd : ∀ x y : ℕ → α, x ≠ y → dist x y = β ^ PiNat.firstDiff x y) {Ω : Type*}
    [MeasurableSpace Ω] (κ : Kernel Ω (ℕ → α)) [IsSFiniteKernel κ] (n : ℕ) :
    Measurable fun p : Ω × (ℕ → α) ↦ κ p.1 (PiNat.cylinder p.2 n) := by
  have hD : MeasurableSet {q : (Ω × (ℕ → α)) × (ℕ → α) | q.2 ∈ PiNat.cylinder q.1.2 n} :=
    (measurableSet_mem_cylinder hβ hβ₁ hd n).preimage
      ((measurable_snd.comp measurable_fst).prodMk measurable_snd)
  exact Kernel.measurable_kernel_prodMk_left (κ := Kernel.prodMkRight (ℕ → α) κ) hD

/-- The first `n` symbols of a sequence. -/
def prefixMap (n : ℕ) (x : ℕ → α) : Fin n → α := fun i ↦ x i

omit [MetricSpace (ℕ → α)] [MeasurableSpace (ℕ → α)] [BorelSpace (ℕ → α)] in
/-- The fibre of the prefix map through `x` is the cylinder `[x↾n]`. -/
theorem prefixMap_preimage (x : ℕ → α) (n : ℕ) :
    prefixMap n ⁻¹' {prefixMap n x} = PiNat.cylinder x n := by
  ext y
  simp only [mem_preimage, mem_singleton_iff, prefixMap, funext_iff, PiNat.mem_cylinder_iff]
  exact ⟨fun h i hi ↦ h ⟨i, hi⟩, fun h i ↦ h i i.2⟩

/-- The fibres of the prefix map are Borel. -/
theorem measurableSet_prefixMap_fibre (hβ : 0 < β) (hβ₁ : β < 1)
    (hd : ∀ x y : ℕ → α, x ≠ y → dist x y = β ^ PiNat.firstDiff x y) {n : ℕ} (w : Fin n → α) :
    MeasurableSet (prefixMap n ⁻¹' {w}) := by
  by_cases hw : ∃ x, prefixMap n x = w
  · obtain ⟨x, rfl⟩ := hw
    rw [prefixMap_preimage]
    exact measurableSet_cylinder hβ hβ₁ hd x n
  · simp only [not_exists] at hw
    have : prefixMap n ⁻¹' {w} = ∅ := eq_empty_of_forall_notMem fun x hx ↦ hw x hx
    rw [this]
    exact MeasurableSet.empty

/-- Every union of cylinders of length `n` is Borel. -/
theorem measurableSet_preimage_prefixMap [Countable α] (hβ : 0 < β) (hβ₁ : β < 1)
    (hd : ∀ x y : ℕ → α, x ≠ y → dist x y = β ^ PiNat.firstDiff x y) (n : ℕ)
    (t : Set (Fin n → α)) : MeasurableSet (prefixMap n ⁻¹' t) := by
  rw [← Set.biUnion_preimage_singleton]
  exact MeasurableSet.biUnion t.to_countable fun w _ ↦ measurableSet_prefixMap_fibre hβ hβ₁ hd w

/-- A union of cylinders of length `n` has the mass of the sum of its cylinders. -/
theorem measure_preimage_prefixMap [Countable α] (hβ : 0 < β) (hβ₁ : β < 1)
    (hd : ∀ x y : ℕ → α, x ≠ y → dist x y = β ^ PiNat.firstDiff x y) (ν : Measure (ℕ → α))
    (n : ℕ) (s : Set (Fin n → α)) :
    ν (prefixMap n ⁻¹' s) = ∑' w : s, ν (prefixMap n ⁻¹' {(w : Fin n → α)}) :=
  (tsum_measure_preimage_singleton s.to_countable fun w _ ↦
    measurableSet_prefixMap_fibre hβ hβ₁ hd w).symm

/-- The packing estimate on cylinders (the cylinder form of Lemma 7.1, where no change of
scale is needed): the cylinders `C` of length `n` on which `c ν(C) < μ(C)` have total
`ν`-mass at most `μ(X) / c`. -/
theorem measure_setOf_mul_lt_measure_cylinder_le [Countable α] (hβ : 0 < β) (hβ₁ : β < 1)
    (hd : ∀ x y : ℕ → α, x ≠ y → dist x y = β ^ PiNat.firstDiff x y) (μ ν : Measure (ℕ → α))
    (n : ℕ) {c : ℝ≥0∞} (hc0 : c ≠ 0) (hc : c ≠ ⊤) :
    ν {x | c * ν (PiNat.cylinder x n) < μ (PiNat.cylinder x n)} ≤ μ univ / c := by
  set E := {x | c * ν (PiNat.cylinder x n) < μ (PiNat.cylinder x n)}
  set s := prefixMap n '' E
  have hE : E = prefixMap n ⁻¹' s := by
    ext y
    refine ⟨fun hy ↦ ⟨y, hy, rfl⟩, ?_⟩
    rintro ⟨e, he, hey⟩
    have h : PiNat.cylinder y n = PiNat.cylinder e n := by
      rw [← prefixMap_preimage, ← prefixMap_preimage, hey]
    change c * ν (PiNat.cylinder y n) < μ (PiNat.cylinder y n)
    rw [h]
    exact he
  calc ν E = ∑' w : s, ν (prefixMap n ⁻¹' {(w : Fin n → α)}) := by
        rw [hE, measure_preimage_prefixMap hβ hβ₁ hd]
    _ ≤ ∑' w : s, μ (prefixMap n ⁻¹' {(w : Fin n → α)}) / c := by
        refine ENNReal.tsum_le_tsum fun w ↦ ?_
        obtain ⟨e, he, hw⟩ := w.2
        rw [← hw, prefixMap_preimage, ENNReal.le_div_iff_mul_le (Or.inl hc0) (Or.inl hc),
          mul_comm]
        exact he.le
    _ = μ (prefixMap n ⁻¹' s) / c := by
        simp only [div_eq_mul_inv]
        rw [ENNReal.tsum_mul_right, measure_preimage_prefixMap hβ hβ₁ hd]
    _ ≤ μ univ / c := by gcongr; exact subset_univ _

/-- Almost every point has cylinders of positive mass: `ν[x↾n] > 0` for all `n`, for
`ν`-almost every `x`. -/
theorem ae_measure_cylinder_ne_zero [Countable α] (hβ : 0 < β) (hβ₁ : β < 1)
    (hd : ∀ x y : ℕ → α, x ≠ y → dist x y = β ^ PiNat.firstDiff x y) (ν : Measure (ℕ → α)) :
    ∀ᵐ x ∂ν, ∀ n, ν (PiNat.cylinder x n) ≠ 0 := by
  refine ae_all_iff.2 fun n ↦ ?_
  set s := prefixMap n '' {x | ν (PiNat.cylinder x n) = 0}
  refine measure_mono_null (t := prefixMap n ⁻¹' s)
    (fun x hx ↦ (⟨x, not_not.1 hx, rfl⟩ : prefixMap n x ∈ s)) ?_
  rw [measure_preimage_prefixMap hβ hβ₁ hd]
  refine ENNReal.tsum_eq_zero.2 fun w ↦ ?_
  obtain ⟨e, he, hw⟩ := w.2
  rw [← hw, prefixMap_preimage]
  exact he

end cylinders

/-! ### Cantor space: common computations -/

section cantor

attribute [local instance] cantorMetricSpace

/-- The information of the mass `2^{-m}` is `m` bits. -/
theorem infoBits_two_inv_pow (m : ℕ) : infoBits ((2 : ℝ≥0∞)⁻¹ ^ m) = m := by
  rw [infoBits_of_ne (by simp), ENNReal.toReal_pow, ENNReal.toReal_inv, ENNReal.toReal_ofNat,
    Real.logb_pow, Real.logb_inv, Real.logb_self_eq_one one_lt_two]
  simp only [mul_neg, mul_one, neg_neg, ENNReal.ofReal_natCast]

/-- `(n + k) / n → 1` in `ℝ≥0∞`. -/
theorem tendsto_natCast_add_div_natCast (k : ℕ) :
    Tendsto (fun n : ℕ ↦ ((n + k : ℕ) : ℝ≥0∞) / n) atTop (𝓝 1) := by
  have h : Tendsto (fun n : ℕ ↦ 1 + (k : ℝ≥0∞) * (n : ℝ≥0∞)⁻¹) atTop (𝓝 (1 + k * 0)) :=
    tendsto_const_nhds.add (ENNReal.Tendsto.const_mul ENNReal.tendsto_inv_nat_nhds_zero
      (Or.inr (ENNReal.natCast_ne_top k)))
  rw [mul_zero, add_zero] at h
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn0 : (n : ℝ≥0∞) ≠ 0 := by exact_mod_cast (Nat.one_le_iff_ne_zero.1 hn)
  push_cast
  rw [ENNReal.add_div, ENNReal.div_self hn0 (ENNReal.natCast_ne_top n), div_eq_mul_inv]

/-- The Cantor metric as a first-difference metric with ratio `1/2`. -/
theorem cantor_hd : ∀ x y : ℕ → Bool, x ≠ y → dist x y = (1 / 2 : ℝ) ^ PiNat.firstDiff x y :=
  fun _ _ ↦ cantorMetricSpace_dist_eq

/-- Cylinders of Cantor space are measurable. -/
theorem measurableSet_cantor_cylinder (x : ℕ → Bool) (n : ℕ) :
    MeasurableSet (PiNat.cylinder x n) :=
  measurableSet_cylinder (by norm_num) (by norm_num) cantor_hd x n

end cantor

/-! ### The cylinder filtration and martingale convergence -/

section martingale

variable {α : Type*} [MetricSpace (ℕ → α)] [MeasurableSpace (ℕ → α)] [BorelSpace (ℕ → α)]
  {β : ℝ}

/-- The σ-algebra `σ(x↾n)` generated by the first `n` symbols. -/
@[instance_reducible]
def prefixSigma (n : ℕ) : MeasurableSpace (ℕ → α) :=
  MeasurableSpace.comap (prefixMap n) ⊤

omit [MetricSpace (ℕ → α)] [MeasurableSpace (ℕ → α)] [BorelSpace (ℕ → α)] in
/-- The σ-algebras `σ(x↾n)` increase with `n`. -/
theorem prefixSigma_mono : Monotone (prefixSigma (α := α)) := by
  intro n m hnm
  have h : prefixMap n =
      (fun v : Fin m → α ↦ fun i : Fin n ↦ v (Fin.castLE hnm i)) ∘ prefixMap m := rfl
  rw [prefixSigma, prefixSigma, h, ← MeasurableSpace.comap_comp]
  exact MeasurableSpace.comap_mono le_top

/-- `σ(x↾n)` is contained in the Borel σ-algebra. -/
theorem prefixSigma_le [Countable α] (hβ : 0 < β) (hβ₁ : β < 1)
    (hd : ∀ x y : ℕ → α, x ≠ y → dist x y = β ^ PiNat.firstDiff x y) (n : ℕ) :
    prefixSigma n ≤ ‹MeasurableSpace (ℕ → α)› := by
  rw [prefixSigma, MeasurableSpace.comap_le_iff_le_map]
  intro t _
  exact measurableSet_preimage_prefixMap hβ hβ₁ hd n t

/-- The cylinder σ-algebras generate the Borel σ-algebra. -/
theorem le_iSup_prefixSigma (hβ : 0 < β) (hβ₁ : β < 1)
    (hd : ∀ x y : ℕ → α, x ≠ y → dist x y = β ^ PiNat.firstDiff x y) :
    ‹MeasurableSpace (ℕ → α)› ≤ ⨆ n, prefixSigma (α := α) n := by
  rw [BorelSpace.measurable_eq (α := ℕ → α), borel]
  refine MeasurableSpace.generateFrom_le fun U hU ↦ ?_
  have hU' : U = ⋃ n, prefixMap n ⁻¹' {w | prefixMap n ⁻¹' {w} ⊆ U} := by
    ext x
    simp only [mem_iUnion, mem_preimage, mem_ofPred_eq]
    constructor
    · intro hx
      obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hU x hx
      obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one hε hβ₁
      refine ⟨k + 1, ?_⟩
      rw [prefixMap_preimage]
      intro y hy
      apply hball
      rw [Metric.mem_ball]
      by_cases hyx : y = x
      · rw [hyx, dist_self]
        exact hε
      rw [hd y x hyx]
      have hk1 : k + 1 ≤ PiNat.firstDiff y x := by
        by_contra hlt
        exact PiNat.apply_firstDiff_ne hyx (hy _ (by omega))
      calc β ^ PiNat.firstDiff y x ≤ β ^ (k + 1) := pow_le_pow_of_le_one hβ.le hβ₁.le hk1
        _ ≤ β ^ k := pow_le_pow_of_le_one hβ.le hβ₁.le (Nat.le_succ k)
        _ < ε := hk
    · rintro ⟨n, hn⟩
      exact hn rfl
  rw [hU']
  exact MeasurableSet.iUnion fun n ↦ le_iSup (fun n ↦ prefixSigma (α := α) n) n _
    ⟨_, MeasurableSpace.measurableSet_top, rfl⟩

/-- The ratio `ν[x↾n] / μ[x↾n]` integrates over every union `s` of cylinders of length `n` to
`ν(s)`, when `ν ≪ μ`. -/
theorem setLIntegral_ratio_cylinder [Countable α] (hβ : 0 < β) (hβ₁ : β < 1)
    (hd : ∀ x y : ℕ → α, x ≠ y → dist x y = β ^ PiNat.firstDiff x y) {μ ν : Measure (ℕ → α)}
    [IsFiniteMeasure μ] (hac : ν ≪ μ) (n : ℕ) (t : Set (Fin n → α)) :
    ∫⁻ x in prefixMap n ⁻¹' t, ν (PiNat.cylinder x n) / μ (PiNat.cylinder x n) ∂μ =
      ν (prefixMap n ⁻¹' t) := by
  have hU : prefixMap n ⁻¹' t = ⋃ w : t, prefixMap n ⁻¹' {(w : Fin n → α)} := by
    ext x
    simp
  have hdisj : Pairwise (Function.onFun Disjoint
      fun w : t ↦ prefixMap n ⁻¹' {(w : Fin n → α)}) := fun w w' hne ↦
    (Set.disjoint_singleton.2 (Subtype.coe_injective.ne hne)).preimage _
  rw [hU, lintegral_iUnion (fun w ↦ measurableSet_prefixMap_fibre hβ hβ₁ hd _) hdisj,
    ← hU, measure_preimage_prefixMap hβ hβ₁ hd]
  refine tsum_congr fun w ↦ ?_
  set F := prefixMap n ⁻¹' {(w : Fin n → α)}
  have hc : ∀ x ∈ F, ν (PiNat.cylinder x n) / μ (PiNat.cylinder x n) = ν F / μ F := by
    intro x hx
    have hx' : prefixMap n x = w := hx
    rw [← prefixMap_preimage, hx']
  rw [setLIntegral_congr_fun (measurableSet_prefixMap_fibre hβ hβ₁ hd _) hc, setLIntegral_const]
  rcases eq_or_ne (μ F) 0 with h0 | h0
  · rw [h0, mul_zero, hac h0]
  · exact ENNReal.div_mul_cancel h0 (measure_ne_top _ _)

/-- Martingale convergence along cylinders: if `ν ≪ μ` (finite measures), then for
`ν`-almost every `x` the information density `log₂ (ν[x↾n] / μ[x↾n])` converges to a finite
limit, `log₂ (dν/dμ)(x)`. The ratios are the conditional expectations of `dν/dμ` given `x↾n`
under `μ`, so they converge `μ`-almost everywhere by Lévy's upward theorem
(`Integrable.tendsto_ae_condExp`), and `dν/dμ` is positive and finite `ν`-almost everywhere. -/
theorem ae_tendsto_logb_ratio_cylinder [Countable α] (hβ : 0 < β) (hβ₁ : β < 1)
    (hd : ∀ x y : ℕ → α, x ≠ y → dist x y = β ^ PiNat.firstDiff x y) {μ ν : Measure (ℕ → α)}
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (hac : ν ≪ μ) :
    ∀ᵐ x ∂ν, ∃ c : ℝ, Tendsto (fun n : ℕ ↦
      Real.logb 2 ((ν (PiNat.cylinder x n)).toReal / (μ (PiNat.cylinder x n)).toReal)) atTop
        (𝓝 c) := by
  let ℱ : Filtration ℕ ‹MeasurableSpace (ℕ → α)› :=
    ⟨prefixSigma, prefixSigma_mono, prefixSigma_le hβ hβ₁ hd⟩
  set g : (ℕ → α) → ℝ := fun x ↦ (ν.rnDeriv μ x).toReal
  set H : ℕ → (ℕ → α) → ℝ≥0∞ := fun n x ↦ ν (PiNat.cylinder x n) / μ (PiNat.cylinder x n)
  have hHmeas : ∀ n, Measurable[prefixSigma n] (H n) := by
    intro n
    have h : H n = (fun w ↦ ν (prefixMap n ⁻¹' {w}) / μ (prefixMap n ⁻¹' {w})) ∘ prefixMap n := by
      funext x
      simp only [H, Function.comp_apply, prefixMap_preimage]
    rw [h, measurable_iff_comap_le, prefixSigma, ← MeasurableSpace.comap_comp]
    exact MeasurableSpace.comap_mono le_top
  have hHm : ∀ n, Measurable (H n) := fun n ↦ (hHmeas n).mono (prefixSigma_le hβ hβ₁ hd n) le_rfl
  have hint : ∀ n, ∫⁻ x, H n x ∂μ = ν univ := fun n ↦ by
    have := setLIntegral_ratio_cylinder hβ hβ₁ hd hac n univ
    rwa [preimage_univ, Measure.restrict_univ] at this
  have hHfin : ∀ n, ∀ᵐ x ∂μ, H n x < ⊤ := fun n ↦
    ae_lt_top (hHm n) (by rw [hint]; exact measure_ne_top _ _)
  have hcond : ∀ n, (fun x ↦ (H n x).toReal) =ᵐ[μ] μ[g | ℱ n] := by
    intro n
    refine ae_eq_condExp_of_forall_setIntegral_eq (ℱ.le n) Measure.integrable_toReal_rnDeriv
      (fun s _ _ ↦ (integrable_toReal_of_lintegral_ne_top (hHm n).aemeasurable
        (by rw [hint]; exact measure_ne_top _ _)).integrableOn) ?_
      ((hHmeas n).ennreal_toReal.aestronglyMeasurable)
    intro s hs _
    obtain ⟨t, -, rfl⟩ := hs
    rw [integral_toReal (hHm n).aemeasurable (ae_restrict_of_ae (hHfin n)),
      setLIntegral_ratio_cylinder hβ hβ₁ hd hac n t, Measure.setIntegral_toReal_rnDeriv hac]
    rfl
  have hg : StronglyMeasurable[⨆ n, ℱ n] g :=
    ((Measure.measurable_rnDeriv ν μ).ennreal_toReal.mono (le_iSup_prefixSigma hβ hβ₁ hd)
      le_rfl).stronglyMeasurable
  have hlim := (Measure.integrable_toReal_rnDeriv (μ := ν) (ν := μ)).tendsto_ae_condExp hg
  have hμae : ∀ᵐ x ∂μ, Tendsto (fun n ↦ (H n x).toReal) atTop (𝓝 (g x)) := by
    filter_upwards [hlim, ae_all_iff.2 hcond] with x hx hx'
    exact hx.congr fun n ↦ (hx' n).symm
  filter_upwards [hac.ae_le hμae, Measure.rnDeriv_pos hac,
    hac.ae_le (Measure.rnDeriv_lt_top ν μ)] with x hx hpos hfin
  have hg0 : 0 < g x := ENNReal.toReal_pos hpos.ne' hfin.ne
  refine ⟨Real.log (g x) / Real.log 2, ?_⟩
  refine (((Real.continuousAt_log hg0.ne').tendsto.comp hx).div_const (Real.log 2)).congr
    fun n ↦ ?_
  simp only [Function.comp_apply, H, ENNReal.toReal_div, Real.logb]

end martingale

/-! ### Example 7.8: the revealed blocks -/

section revealed

/-- The probability `1/k` of revealing the block `J_k = [2^k, 2^{k+1})` (Example 7.8; only the
blocks with `k ≥ 2` are used). -/
noncomputable def revealProb (k : ℕ) : unitInterval :=
  ⟨(k : ℝ)⁻¹, inv_nonneg.2 (Nat.cast_nonneg k), Nat.cast_inv_le_one k⟩

/-- The set `⋃ {J_k : k ≥ 2, e_k = 1}` of revealed coordinates, `J_k = [2^k, 2^{k+1})`. -/
def revealedSet (e : ℕ → Bool) : Set ℕ :=
  {i | ∃ k, 2 ≤ k ∧ e k = true ∧ 2 ^ k ≤ i ∧ i < 2 ^ (k + 1)}

/-- The law of the revealing indicators `(e_k)_k`: independent Bernoulli(`1/k`) variables. -/
noncomputable def revealIndicatorMeasure : Measure (ℕ → Bool) :=
  Measure.infinitePi fun k ↦ ProbabilityTheory.bernoulliMeasure true false (revealProb k)

instance : IsProbabilityMeasure revealIndicatorMeasure := by
  unfold revealIndicatorMeasure; infer_instance

/-- The number `#([0, n) ∩ revealedSet e)` of revealed coordinates below `n`. -/
noncomputable def revealCount (e : ℕ → Bool) (n : ℕ) : ℕ :=
  (Iio n ∩ revealedSet e).ncard

/-! #### Counting revealed coordinates -/

/-- The block containing a revealed coordinate is determined by the coordinate. -/
lemma log_eq_of_mem_block {i k : ℕ} (h1 : 2 ^ k ≤ i) (h2 : i < 2 ^ (k + 1)) :
    Nat.log 2 i = k :=
  Nat.log_eq_of_pow_le_of_lt_pow h1 h2

/-- At most `n` coordinates below `n` are revealed. -/
lemma revealCount_le (e : ℕ → Bool) (n : ℕ) : revealCount e n ≤ n := by
  calc revealCount e n ≤ (Iio n).ncard :=
        Set.ncard_le_ncard inter_subset_left (finite_Iio n)
    _ = n := by rw [← Finset.coe_range, Set.ncard_coe_finset, Finset.card_range]

/-- If the block `J_k` is revealed, at least `2^k` of the coordinates below `2^{k+1}` are. -/
lemma pow_le_revealCount {e : ℕ → Bool} {k : ℕ} (hk : 2 ≤ k) (he : e k = true) :
    2 ^ k ≤ revealCount e (2 ^ (k + 1)) := by
  have hsub : (↑(Finset.Ico (2 ^ k) (2 ^ (k + 1))) : Set ℕ) ⊆
      Iio (2 ^ (k + 1)) ∩ revealedSet e := by
    intro i hi
    simp only [Finset.coe_Ico, mem_Ico] at hi
    exact ⟨hi.2, k, hk, he, hi.1, hi.2⟩
  have h := Set.ncard_le_ncard hsub ((finite_Iio _).inter_of_left _)
  rw [Set.ncard_coe_finset, Nat.card_Ico] at h
  rw [revealCount]
  have : 2 ^ (k + 1) - 2 ^ k = 2 ^ k := by rw [pow_succ]; omega
  omega

/-- If no block `J_j` with `a ≤ j < b` is revealed, at most `2^a` coordinates below `2^b` are. -/
lemma revealCount_pow_le {e : ℕ → Bool} {a b : ℕ} (h : ∀ j, a ≤ j → j < b → e j = false) :
    revealCount e (2 ^ b) ≤ 2 ^ a := by
  have hsub : Iio (2 ^ b) ∩ revealedSet e ⊆ Iio (2 ^ a) := by
    rintro i ⟨hi, j, -, hj, h1, h2⟩
    simp only [mem_Iio] at hi ⊢
    have hjb : j < b := (Nat.pow_lt_pow_iff_right (by norm_num)).1 (lt_of_le_of_lt h1 hi)
    have hja : j < a := by
      by_contra hc
      rw [h j (not_lt.1 hc) hjb] at hj
      exact Bool.false_ne_true hj
    calc i < 2 ^ (j + 1) := h2
      _ ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) hja
  calc revealCount e (2 ^ b) ≤ (Iio (2 ^ a)).ncard := Set.ncard_le_ncard hsub (finite_Iio _)
    _ = 2 ^ a := by rw [← Finset.coe_range, Set.ncard_coe_finset, Finset.card_range]

/-- The deterministic upper bound: if, from the block `K` on, a revealed block `J_k` is never
preceded by a revealed block `J_j` with `k ≤ j + m`, then
`2^{m+1} #([0, n) ∩ S) ≤ (2^m + 2) n + 2^{m + K + 2}` for every `n`. -/
lemma revealCount_le_of_sparse {e : ℕ → Bool} {K m : ℕ}
    (h : ∀ k, K ≤ k → e k = true → ∀ j, k ≤ j + m → j < k → e j = false) (n : ℕ) :
    2 ^ (m + 1) * revealCount e n ≤ (2 ^ m + 2) * n + 2 ^ (m + K + 2) := by
  have hsmall : ∀ n, n ≤ 2 ^ (K + 1) →
      2 ^ (m + 1) * revealCount e n ≤ (2 ^ m + 2) * n + 2 ^ (m + K + 2) := by
    intro n hn
    have h1 := revealCount_le e n
    have h2 : 2 ^ (m + 1) * revealCount e n ≤ 2 ^ (m + 1) * 2 ^ (K + 1) :=
      Nat.mul_le_mul_left _ (h1.trans hn)
    rw [← pow_add, show m + 1 + (K + 1) = m + K + 2 by ring] at h2
    omega
  suffices H : ∀ k n, n ≤ 2 ^ (k + 1) →
      2 ^ (m + 1) * revealCount e n ≤ (2 ^ m + 2) * n + 2 ^ (m + K + 2) from
    H n n (Nat.lt_two_pow_self.le.trans (Nat.pow_le_pow_right (by norm_num) (Nat.le_succ n)))
  intro k
  induction k with
  | zero =>
    intro n hn
    exact hsmall n (hn.trans (Nat.pow_le_pow_right (by norm_num) (by omega)))
  | succ k ih =>
    intro n hn
    rcases le_or_gt n (2 ^ (k + 1)) with hle | hlt
    · exact ih n hle
    rcases le_or_gt (k + 1) K with hK | hK
    · exact hsmall n (hn.trans (Nat.pow_le_pow_right (by norm_num) (by omega)))
    cases hek : e (k + 1) with
    | false =>
      -- no coordinate of `[2^{k+1}, n)` is revealed
      have hsub : Iio n ∩ revealedSet e ⊆ Iio (2 ^ (k + 1)) ∩ revealedSet e := by
        rintro i ⟨hi, j, hj2, hj, h1, h2⟩
        refine ⟨?_, j, hj2, hj, h1, h2⟩
        simp only [mem_Iio] at hi ⊢
        by_contra hc
        have hjk : k + 1 ≤ j := by
          by_contra hc'
          have : 2 ^ (j + 1) ≤ 2 ^ (k + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
          omega
        have hjk' : j ≤ k + 1 := by
          by_contra hc'
          have : 2 ^ (k + 1 + 1) ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) (by omega)
          omega
        rw [show j = k + 1 by omega, hek] at hj
        exact Bool.false_ne_true hj
      have hmono : revealCount e n ≤ revealCount e (2 ^ (k + 1)) :=
        Set.ncard_le_ncard hsub ((finite_Iio _).inter_of_left _)
      have := ih (2 ^ (k + 1)) le_rfl
      have h3 : (2 ^ m + 2) * 2 ^ (k + 1) ≤ (2 ^ m + 2) * n := Nat.mul_le_mul_left _ hlt.le
      have h4 := Nat.mul_le_mul_left (2 ^ (m + 1)) hmono
      omega
    | true =>
      -- the revealed coordinates below `n` lie in `[0, 2^{k+1-m}) ∪ [2^{k+1}, n)`
      have hsub : Iio n ∩ revealedSet e ⊆
          ↑(Finset.range (2 ^ (k + 1 - m)) ∪ Finset.Ico (2 ^ (k + 1)) n) := by
        rintro i ⟨hi, j, hj2, hj, h1, h2⟩
        simp only [mem_Iio] at hi
        simp only [Finset.coe_union, Finset.coe_range, Finset.coe_Ico, mem_union, mem_Iio,
          mem_Ico]
        rcases lt_or_ge j (k + 1) with hjk | hjk
        · left
          have hjm : j + m < k + 1 := by
            by_contra hc
            rw [h (k + 1) hK.le hek j (by omega) hjk] at hj
            exact Bool.false_ne_true hj
          calc i < 2 ^ (j + 1) := h2
            _ ≤ 2 ^ (k + 1 - m) := Nat.pow_le_pow_right (by norm_num) (by omega)
        · right
          exact ⟨le_trans (Nat.pow_le_pow_right (by norm_num) hjk) h1, hi⟩
      have hcard : revealCount e n ≤ 2 ^ (k + 1 - m) + (n - 2 ^ (k + 1)) := by
        calc revealCount e n ≤
              (↑(Finset.range (2 ^ (k + 1 - m)) ∪ Finset.Ico (2 ^ (k + 1)) n) : Set ℕ).ncard :=
              Set.ncard_le_ncard hsub (Finset.finite_toSet _)
          _ ≤ 2 ^ (k + 1 - m) + (n - 2 ^ (k + 1)) := by
              rw [Set.ncard_coe_finset]
              refine (Finset.card_union_le _ _).trans ?_
              rw [Finset.card_range, Nat.card_Ico]
      have hc : 2 ^ m * 2 ^ (k + 1 - m) ≤ 2 ^ (k + 1) + 2 ^ m := by
        rcases le_or_gt m (k + 1) with hm | hm
        · rw [← pow_add, Nat.add_sub_cancel' hm]
          exact Nat.le_add_right _ _
        · rw [Nat.sub_eq_zero_of_le hm.le, pow_zero, mul_one]
          exact Nat.le_add_left _ _
      have hK2 : 2 * 2 ^ m ≤ 2 ^ (m + K + 2) := by
        rw [← pow_succ']
        exact Nat.pow_le_pow_right (by norm_num) (by omega)
      generalize 2 ^ (k + 1 - m) = c at hcard hc
      have ha : n ≤ 2 * 2 ^ (k + 1) := by rw [pow_succ] at hn ⊢; omega
      generalize 2 ^ (k + 1) = a at hcard hc ha hlt
      obtain ⟨d, rfl⟩ : ∃ d, n = a + d := ⟨n - a, by omega⟩
      have hd : d ≤ a := by omega
      have hsub' : a + d - a = d := by omega
      rw [hsub'] at hcard
      have h5 : 2 ^ m * d ≤ 2 ^ m * a := Nat.mul_le_mul_left _ hd
      have h6 := Nat.mul_le_mul_left (2 ^ (m + 1)) hcard
      rw [pow_succ] at h6 ⊢
      nlinarith

/-! #### The revealing indicators -/

/-- `1/k` as a probability. -/
lemma toNNReal_revealProb (k : ℕ) : unitInterval.toNNReal (revealProb k) = (k : ℝ≥0)⁻¹ := by
  ext
  change ((k : ℝ)⁻¹) = _
  rw [NNReal.coe_inv, NNReal.coe_natCast]

/-- `P(e_k = 1 for all k ∈ s) = ∏_{k ∈ s} 1/k`. -/
lemma revealIndicatorMeasure_pi (s : Finset ℕ) :
    revealIndicatorMeasure (Set.pi s fun _ ↦ {true}) = ∏ k ∈ s, (((k : ℝ≥0)⁻¹ : ℝ≥0) : ℝ≥0∞) := by
  rw [revealIndicatorMeasure, Measure.infinitePi_pi _ fun _ _ ↦ measurableSet_singleton _]
  refine Finset.prod_congr rfl fun k _ ↦ ?_
  rw [bernoulliMeasure_apply_of_mem_of_notMem _ (measurableSet_singleton _) rfl (by simp),
    toNNReal_revealProb]

/-- The event `e_k = 1`. -/
lemma revealEvent_eq_pi (k : ℕ) :
    {e : ℕ → Bool | e k = true} = Set.pi ({k} : Finset ℕ) fun _ ↦ {true} := by
  ext e
  simp

/-- `P(e_k = 1) = 1/k`. -/
lemma revealIndicatorMeasure_apply_eq_true (k : ℕ) :
    revealIndicatorMeasure {e | e k = true} = (((k : ℝ≥0)⁻¹ : ℝ≥0) : ℝ≥0∞) := by
  rw [revealEvent_eq_pi, revealIndicatorMeasure_pi, Finset.prod_singleton]

/-- Second Borel–Cantelli lemma: almost surely `e_k = 1` for infinitely many `k`. -/
theorem ae_frequently_reveal : ∀ᵐ e ∂revealIndicatorMeasure, ∃ᶠ k in atTop, e k = true := by
  have hm : ∀ k, MeasurableSet {e : ℕ → Bool | e k = true} := fun k ↦
    (measurable_pi_apply k) (measurableSet_singleton _)
  have hind : iIndepSet (fun k ↦ {e : ℕ → Bool | e k = true}) revealIndicatorMeasure := by
    rw [iIndepSet_iff_meas_biInter hm]
    intro s
    have h : (⋂ k ∈ s, {e : ℕ → Bool | e k = true}) = Set.pi s fun _ ↦ {true} := by
      ext e
      simp
    rw [h, revealIndicatorMeasure_pi]
    exact Finset.prod_congr rfl fun k _ ↦ (revealIndicatorMeasure_apply_eq_true k).symm
  have hsum : ∑' k, revealIndicatorMeasure {e : ℕ → Bool | e k = true} = ∞ := by
    simp only [revealIndicatorMeasure_apply_eq_true]
    by_contra h
    refine Real.not_summable_natCast_inv ?_
    have := ENNReal.tsum_coe_ne_top_iff_summable.1 h
    rw [← NNReal.summable_coe] at this
    simpa using this
  have h1 := measure_limsup_eq_one hm hind hsum
  have hmeas : MeasurableSet (limsup (fun k ↦ {e : ℕ → Bool | e k = true}) atTop) :=
    MeasurableSet.measurableSet_limsup hm
  rw [← prob_compl_eq_zero_iff hmeas] at h1
  rw [ae_iff]
  refine measure_mono_null (fun e he ↦ ?_) h1
  simp only [mem_compl_iff, mem_limsup_iff_frequently_mem, mem_ofPred_eq]
  exact he

/-- First Borel–Cantelli lemma: almost surely, from some block on, a revealed block `J_k` is
never preceded by a revealed block `J_j` with `k ≤ j + m`. -/
theorem ae_eventually_sparse (m : ℕ) : ∀ᵐ e ∂revealIndicatorMeasure, ∀ᶠ k in atTop,
    e k = true → ∀ j, k ≤ j + m → j < k → e j = false := by
  set s : ℕ → Set (ℕ → Bool) := fun k ↦
    ⋃ j ∈ Finset.Ico (k - m) k, Set.pi ({j, k} : Finset ℕ) fun _ ↦ {true}
  have hbound : ∀ k, revealIndicatorMeasure (s k) ≤
      ENNReal.ofReal (m * (m + 1) / (k : ℝ) ^ 2) := by
    intro k
    refine (measure_biUnion_finset_le _ _).trans ?_
    have hterm : ∀ j ∈ Finset.Ico (k - m) k,
        revealIndicatorMeasure (Set.pi ({j, k} : Finset ℕ) fun _ ↦ {true}) ≤
          ENNReal.ofReal ((m + 1) / (k : ℝ) ^ 2) := by
      intro j hj
      rw [Finset.mem_Ico] at hj
      rw [revealIndicatorMeasure_pi, Finset.prod_pair (by omega), ← ENNReal.coe_mul,
        ENNReal.ofReal, ENNReal.coe_le_coe, ← NNReal.coe_le_coe]
      rcases Nat.eq_zero_or_pos j with rfl | hj0
      · simp
      have hk : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
      have hj' : (0 : ℝ) < j := by exact_mod_cast hj0
      have hkj : (k : ℝ) ≤ (m + 1) * j := by
        have h2 : m ≤ m * j := Nat.le_mul_of_pos_right _ hj0
        have : k ≤ (m + 1) * j := by rw [add_mul, one_mul]; omega
        exact_mod_cast this
      push_cast
      rw [Real.coe_toNNReal _ (by positivity), ← mul_inv, inv_eq_one_div,
        div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    calc ∑ j ∈ Finset.Ico (k - m) k, revealIndicatorMeasure (Set.pi ({j, k} : Finset ℕ) _)
        ≤ ∑ _j ∈ Finset.Ico (k - m) k, ENNReal.ofReal ((m + 1) / (k : ℝ) ^ 2) :=
          Finset.sum_le_sum hterm
      _ ≤ m * ENNReal.ofReal ((m + 1) / (k : ℝ) ^ 2) := by
          rw [Finset.sum_const, nsmul_eq_mul]
          gcongr
          rw [Nat.card_Ico]
          exact_mod_cast (show k - (k - m) ≤ m by omega)
      _ = ENNReal.ofReal (m * (m + 1) / (k : ℝ) ^ 2) := by
          rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _), mul_div_assoc]
  have hsum : ∑' k, revealIndicatorMeasure (s k) ≠ ∞ := by
    refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hbound)
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun k ↦ by positivity)]
    · exact ENNReal.ofReal_ne_top
    · simp_rw [div_eq_mul_one_div ((m : ℝ) * (m + 1))]
      exact (Real.summable_one_div_nat_pow.2 one_lt_two).mul_left _
  filter_upwards [ae_eventually_notMem hsum] with e he
  filter_upwards [he] with k hk hek j hj1 hj2
  by_contra hc
  refine hk (mem_biUnion (x := j) (Finset.mem_Ico.2 ⟨by omega, hj2⟩) ?_)
  intro i hi
  simp only [Finset.coe_insert, Finset.coe_singleton, mem_insert_iff, mem_singleton_iff] at hi
  rcases hi with rfl | rfl
  · simpa using hc
  · simpa using hek

/-! #### Densities of the revealed set -/

/-- The revealed blocks give frequently `n ≤ 2 #([0, n) ∩ S)` (at `n = 2^{k+1}`, `e_k = 1`). -/
lemma frequently_le_two_mul_revealCount {e : ℕ → Bool} (h : ∃ᶠ k in atTop, e k = true) :
    ∃ᶠ n in atTop, n ≤ 2 * revealCount e n := by
  rw [frequently_atTop] at h ⊢
  intro N
  obtain ⟨k, hk, hek⟩ := h (max N 2)
  refine ⟨2 ^ (k + 1), ?_, ?_⟩
  · exact (le_max_left N 2).trans (hk.trans (Nat.lt_two_pow_self.le.trans
      (Nat.pow_le_pow_right (by norm_num) (Nat.le_succ k))))
  · have := pow_le_revealCount ((le_max_right N 2).trans hk) hek
    have h2 : 2 ^ (k + 1) = 2 * 2 ^ k := by ring
    omega

/-- After a revealed block `J_k` followed by `m` unrevealed ones, few coordinates are revealed:
frequently `2^m #([0, n) ∩ S) ≤ n`. -/
lemma frequently_pow_mul_revealCount_le {e : ℕ → Bool} {m : ℕ}
    (h : ∃ᶠ k in atTop, e k = true)
    (hs : ∀ᶠ k in atTop, e k = true → ∀ j, k ≤ j + m → j < k → e j = false) :
    ∃ᶠ n in atTop, 2 ^ m * revealCount e n ≤ n := by
  rw [frequently_atTop] at h ⊢
  obtain ⟨K, hK⟩ := eventually_atTop.1 hs
  intro N
  obtain ⟨k, hk, hek⟩ := h (max N K)
  refine ⟨2 ^ (k + 1 + m), ?_, ?_⟩
  · exact (le_max_left N K).trans (hk.trans (Nat.lt_two_pow_self.le.trans
      (Nat.pow_le_pow_right (by norm_num) (by omega))))
  · have hz : ∀ j, k + 1 ≤ j → j < k + 1 + m → e j = false := by
      intro j hj1 hj2
      by_contra hc
      have := hK j (by omega) (by simpa using hc) k (by omega) (by omega)
      rw [hek] at this
      simp at this
    calc 2 ^ m * revealCount e (2 ^ (k + 1 + m)) ≤ 2 ^ m * 2 ^ (k + 1) :=
          Nat.mul_le_mul_left _ (revealCount_pow_le hz)
      _ = 2 ^ (k + 1 + m) := by rw [← pow_add, add_comm]

/-- Sparse revealed blocks give eventually `2^{m+1} #([0, n) ∩ S) ≤ (2^m + 4) n`. -/
lemma eventually_revealCount_le {e : ℕ → Bool} {m : ℕ}
    (hs : ∀ᶠ k in atTop, e k = true → ∀ j, k ≤ j + m → j < k → e j = false) :
    ∀ᶠ n in atTop, 2 ^ (m + 1) * revealCount e n ≤ (2 ^ m + 4) * n := by
  obtain ⟨K, hK⟩ := eventually_atTop.1 hs
  filter_upwards [eventually_ge_atTop (2 ^ (m + K + 1))] with n hn
  have h := revealCount_le_of_sparse (fun k hk ↦ hK k hk) n
  have h2 : 2 ^ (m + K + 2) = 2 * 2 ^ (m + K + 1) := by rw [pow_succ]; ring
  rw [h2] at h
  nlinarith

/-- The unrevealed coordinates below `n` and the revealed ones add up to `n`. -/
lemma ncard_diff_revealedSet_add (e : ℕ → Bool) (n : ℕ) :
    (Iio n \ revealedSet e).ncard + revealCount e n = n := by
  rw [revealCount, add_comm, Set.ncard_inter_add_ncard_sdiff_eq_ncard _ _ (finite_Iio n),
    ← Finset.coe_range, Set.ncard_coe_finset, Finset.card_range]

/-- Example 7.8, the deterministic part: if infinitely many blocks are revealed and, for every
`m`, revealed blocks are eventually at distance more than `m` apart, then `ℕ \ S` has lower
density `1/2` and upper density `1`. -/
theorem density_compl_revealedSet {e : ℕ → Bool} (h : ∃ᶠ k in atTop, e k = true)
    (hs : ∀ m, ∀ᶠ k in atTop, e k = true → ∀ j, k ≤ j + m → j < k → e j = false) :
    (liminf (fun n : ℕ ↦ ((Iio n \ revealedSet e).ncard : ℝ≥0∞) / n) atTop,
      limsup (fun n : ℕ ↦ ((Iio n \ revealedSet e).ncard : ℝ≥0∞) / n) atTop) = (2⁻¹, 1) := by
  set g : ℕ → ℕ := fun n ↦ (Iio n \ revealedSet e).ncard
  have hg : ∀ n, (g n : ℝ) = n - revealCount e n := fun n ↦ by
    have := ncard_diff_revealedSet_add e n
    rw [eq_sub_iff_add_eq]
    exact_mod_cast this
  have H1 : ∀ (c : ℝ) (n : ℕ), 1 ≤ n → c * n ≤ g n → ENNReal.ofReal c ≤ (g n : ℝ≥0∞) / n := by
    intro c n hn hc
    have hn0 : (n : ℝ≥0∞) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
    rw [ENNReal.le_div_iff_mul_le (Or.inl hn0) (Or.inl (ENNReal.natCast_ne_top n)),
      ← ENNReal.ofReal_natCast n, ← ENNReal.ofReal_mul' (Nat.cast_nonneg _),
      ← ENNReal.ofReal_natCast (g n)]
    exact ENNReal.ofReal_le_ofReal hc
  have H2 : ∀ (c : ℝ) (n : ℕ), 1 ≤ n → (g n : ℝ) ≤ c * n → (g n : ℝ≥0∞) / n ≤ ENNReal.ofReal c := by
    intro c n hn hc
    have hn0 : (n : ℝ≥0∞) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
    rw [ENNReal.div_le_iff_le_mul (Or.inl hn0) (Or.inl (ENNReal.natCast_ne_top n)),
      ← ENNReal.ofReal_natCast n, ← ENNReal.ofReal_mul' (Nat.cast_nonneg _),
      ← ENNReal.ofReal_natCast (g n)]
    exact ENNReal.ofReal_le_ofReal hc
  have hhalf : ENNReal.ofReal (1 / 2) = 2⁻¹ := by
    rw [one_div, ENNReal.ofReal_inv_of_pos two_pos, ENNReal.ofReal_ofNat]
  have hpow : Tendsto (fun m : ℕ ↦ (1 / 2 : ℝ) ^ m) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  refine Prod.ext (le_antisymm ?_ ?_) (le_antisymm ?_ ?_)
  · -- `liminf ≤ 1/2`
    refine liminf_le_of_frequently_le' ?_
    refine ((frequently_le_two_mul_revealCount h).and_eventually (eventually_ge_atTop 1)).mono
      fun n ⟨h1, h2⟩ ↦ ?_
    rw [← hhalf]
    refine H2 _ n h2 ?_
    rw [hg]
    have : (n : ℝ) ≤ 2 * revealCount e n := by exact_mod_cast h1
    linarith
  · -- `1/2 ≤ liminf`
    have hT : Tendsto (fun m : ℕ ↦ ENNReal.ofReal (1 / 2 - 2 * (1 / 2 : ℝ) ^ m)) atTop
        (𝓝 2⁻¹) := by
      rw [← hhalf]
      have := (tendsto_const_nhds (x := (1 / 2 : ℝ))).sub (hpow.const_mul 2)
      rw [mul_zero, sub_zero] at this
      exact ENNReal.tendsto_ofReal this
    refine le_of_tendsto' hT fun m ↦ le_liminf_of_le (by isBoundedDefault) ?_
    filter_upwards [eventually_revealCount_le (hs m), eventually_ge_atTop 1] with n hn h1
    refine H1 _ n h1 ?_
    rw [hg]
    have h2 : (2 : ℝ) ^ (m + 1) * revealCount e n ≤ (2 ^ m + 4) * n := by exact_mod_cast hn
    have h3 : (2 : ℝ) ^ m * (1 / 2) ^ m = 1 := by rw [← mul_pow]; norm_num
    have h4 : (0 : ℝ) < 2 ^ m := by positivity
    rw [pow_succ] at h2
    nlinarith
  · -- `limsup ≤ 1`
    refine limsup_le_of_le (by isBoundedDefault) ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    rw [← ENNReal.ofReal_one]
    refine H2 _ n hn ?_
    rw [hg, one_mul]
    linarith [(Nat.cast_nonneg (revealCount e n) : (0 : ℝ) ≤ _)]
  · -- `1 ≤ limsup`
    have hT : Tendsto (fun m : ℕ ↦ ENNReal.ofReal (1 - (1 / 2 : ℝ) ^ m)) atTop (𝓝 1) := by
      rw [← ENNReal.ofReal_one]
      have := (tendsto_const_nhds (x := (1 : ℝ))).sub hpow
      rw [sub_zero] at this
      exact ENNReal.tendsto_ofReal this
    refine le_of_tendsto' hT fun m ↦ le_limsup_of_frequently_le ?_
    refine ((frequently_pow_mul_revealCount_le h (hs m)).and_eventually
      (eventually_ge_atTop 1)).mono fun n ⟨h1, h2⟩ ↦ ?_
    refine H1 _ n h2 ?_
    rw [hg]
    have h3 : (2 : ℝ) ^ m * revealCount e n ≤ n := by exact_mod_cast h1
    have h4 : (2 : ℝ) ^ m * (1 / 2) ^ m = 1 := by rw [← mul_pow]; norm_num
    have h5 : (0 : ℝ) ≤ (1 / 2) ^ m := by positivity
    nlinarith

/-! #### The mean number of revealed coordinates -/

/-- Membership of a fixed coordinate in the revealed set is a measurable condition on `e`. -/
lemma measurableSet_mem_revealedSet (i : ℕ) :
    MeasurableSet {e : ℕ → Bool | i ∈ revealedSet e} := by
  have h : {e : ℕ → Bool | i ∈ revealedSet e} =
      ⋃ k ∈ {k : ℕ | 2 ≤ k ∧ 2 ^ k ≤ i ∧ i < 2 ^ (k + 1)},
        (fun e : ℕ → Bool ↦ e k) ⁻¹' {true} := by
    ext e
    simp only [revealedSet, mem_ofPred_eq, mem_iUnion, mem_preimage, mem_singleton_iff,
      exists_prop]
    constructor
    · rintro ⟨k, hk, he, h1, h2⟩
      exact ⟨k, ⟨hk, h1, h2⟩, he⟩
    · rintro ⟨k, ⟨hk, h1, h2⟩, he⟩
      exact ⟨k, hk, he, h1, h2⟩
  rw [h]
  exact MeasurableSet.biUnion (to_countable _) fun k _ ↦
    (measurable_pi_apply k) (measurableSet_singleton _)

/-- The probability that the coordinate `i` is revealed: `1/k` if `i ∈ J_k`, `k ≥ 2`, else `0`. -/
noncomputable def revealedMass (i : ℕ) : ℝ :=
  if 2 ≤ Nat.log 2 i then ((Nat.log 2 i : ℕ) : ℝ)⁻¹ else 0

/-- `P(i ∈ S) ≤ revealedMass i` (in fact equality holds). -/
lemma measureReal_mem_revealedSet_le (i : ℕ) :
    revealIndicatorMeasure.real {e | i ∈ revealedSet e} ≤ revealedMass i := by
  have hsub : {e : ℕ → Bool | i ∈ revealedSet e} ⊆
      {e | 2 ≤ Nat.log 2 i ∧ e (Nat.log 2 i) = true} := by
    rintro e ⟨k, hk, he, h1, h2⟩
    rw [log_eq_of_mem_block h1 h2]
    exact ⟨hk, he⟩
  refine (measureReal_mono hsub).trans ?_
  rw [revealedMass]
  split_ifs with h
  · simp only [h, true_and]
    rw [measureReal_def, revealIndicatorMeasure_apply_eq_true, ENNReal.coe_toReal,
      NNReal.coe_inv, NNReal.coe_natCast]
  · simp [h]

/-- `0 ≤ revealedMass i ≤ 1`. -/
lemma revealedMass_nonneg (i : ℕ) : 0 ≤ revealedMass i := by
  unfold revealedMass; split_ifs <;> positivity

/-- On the block `[2^{K+1}, 2^{K+2})`, `revealedMass ≤ 1/(K+1)`. -/
lemma revealedMass_block_le (K x : ℕ) (hx : x < 2 ^ (K + 1)) :
    revealedMass (2 ^ (K + 1) + x) ≤ ((K : ℝ) + 1)⁻¹ := by
  have hlog : Nat.log 2 (2 ^ (K + 1) + x) = K + 1 :=
    Nat.log_eq_of_pow_le_of_lt_pow (Nat.le_add_right _ _) (by rw [pow_succ 2 (K + 1)]; omega)
  rw [revealedMass, hlog]
  split_ifs
  · push_cast; exact le_rfl
  · positivity

/-- `∑_{i < 2^{K+1}} P(i ∈ S) ≤ 12 · 2^K / (K + 2)`. -/
lemma sum_revealedMass_le (K : ℕ) :
    ∑ i ∈ Finset.range (2 ^ (K + 1)), revealedMass i ≤ 12 * 2 ^ K / ((K : ℝ) + 2) := by
  induction K with
  | zero =>
    have h : ∀ i ∈ Finset.range (2 ^ (0 + 1)), revealedMass i = 0 := by
      intro i hi
      simp only [zero_add, pow_one, Finset.mem_range] at hi
      have : Nat.log 2 i = 0 := Nat.log_of_lt (by omega)
      simp [revealedMass, this]
    rw [Finset.sum_eq_zero h]
    positivity
  | succ K ih =>
    have hsplit : 2 ^ (K + 1 + 1) = 2 ^ (K + 1) + 2 ^ (K + 1) := by ring
    rw [hsplit, Finset.sum_range_add]
    have h2 : ∑ x ∈ Finset.range (2 ^ (K + 1)), revealedMass (2 ^ (K + 1) + x) ≤
        2 ^ (K + 1) * ((K : ℝ) + 1)⁻¹ := by
      calc _ ≤ ∑ _x ∈ Finset.range (2 ^ (K + 1)), ((K : ℝ) + 1)⁻¹ :=
            Finset.sum_le_sum fun x hx ↦ revealedMass_block_le K x (Finset.mem_range.1 hx)
        _ = _ := by simp
    have hK : (0 : ℝ) ≤ K := Nat.cast_nonneg K
    have hp : (0 : ℝ) < 2 ^ K := by positivity
    calc _ ≤ 12 * 2 ^ K / ((K : ℝ) + 2) + 2 ^ (K + 1) * ((K : ℝ) + 1)⁻¹ := add_le_add ih h2
      _ ≤ 12 * 2 ^ (K + 1) / (((K + 1 : ℕ) : ℝ) + 2) := by
        push_cast
        rw [← div_eq_mul_inv, div_add_div _ _ (by positivity) (by positivity),
          div_le_div_iff₀ (by positivity) (by positivity), pow_succ]
        nlinarith [mul_nonneg hp.le (mul_nonneg hK hK), mul_nonneg hp.le hK]

/-- `∑_{i < n} P(i ∈ S) ≤ 12 n / log₂ n` for `n ≥ 2`. -/
lemma sum_range_revealedMass_le {n : ℕ} (hn : 2 ≤ n) :
    ∑ i ∈ Finset.range n, revealedMass i ≤ 12 * n / Real.logb 2 n := by
  set K := Nat.log 2 n
  have hK1 : 1 ≤ K := Nat.le_log_of_pow_le (by norm_num) (by simpa using hn)
  have hlt : n < 2 ^ (K + 1) := Nat.lt_pow_succ_log_self (by norm_num) n
  have hle : 2 ^ K ≤ n := Nat.pow_log_le_self 2 (by omega)
  have hsub : ∑ i ∈ Finset.range n, revealedMass i ≤
      ∑ i ∈ Finset.range (2 ^ (K + 1)), revealedMass i :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.2 hlt.le)
      fun i _ _ ↦ revealedMass_nonneg i
  have hlog_pos : 0 < Real.logb 2 n :=
    Real.logb_pos one_lt_two (by exact_mod_cast (show 1 < n by omega))
  have hlog_lt : Real.logb 2 n < K + 1 := by
    rw [Real.logb_lt_iff_lt_rpow one_lt_two (by positivity)]
    exact_mod_cast (show (n : ℝ) < 2 ^ (K + 1) by exact_mod_cast hlt)
  refine hsub.trans ((sum_revealedMass_le K).trans ?_)
  refine div_le_div₀ (by positivity) ?_ hlog_pos (by linarith)
  have : ((2 ^ K : ℕ) : ℝ) ≤ n := by exact_mod_cast hle
  push_cast at this
  linarith

/-- The number of revealed coordinates below `n` as a sum of indicators. -/
lemma revealCount_eq_sum (e : ℕ → Bool) (n : ℕ) :
    (revealCount e n : ℝ) =
      ∑ i ∈ Finset.range n, {e : ℕ → Bool | i ∈ revealedSet e}.indicator 1 e := by
  classical
  have h : Iio n ∩ revealedSet e = ↑((Finset.range n).filter (· ∈ revealedSet e)) := by
    ext i
    simp
  rw [revealCount, h, Set.ncard_coe_finset, Finset.card_filter]
  push_cast
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  simp [Set.indicator_apply]

/-- The number of revealed coordinates below `n` is a measurable function of `e`. -/
lemma measurable_revealCount (n : ℕ) : Measurable fun e ↦ (revealCount e n : ℝ) := by
  simp_rw [revealCount_eq_sum]
  exact Finset.measurable_sum _ fun i _ ↦
    (measurable_const.indicator (measurableSet_mem_revealedSet i))

/-- Example 7.8: the mean number of revealed coordinates below `n` is at most
`12 n / log₂ n`. -/
theorem integral_revealCount_le {n : ℕ} (hn : 2 ≤ n) :
    ∫ e, (revealCount e n : ℝ) ∂revealIndicatorMeasure ≤ 12 * n / Real.logb 2 n := by
  simp_rw [revealCount_eq_sum]
  rw [integral_finsetSum _ fun i _ ↦ ?_]
  swap
  · exact (integrable_const (1 : ℝ)).indicator (measurableSet_mem_revealedSet i)
  simp_rw [integral_indicator_one (measurableSet_mem_revealedSet _)]
  exact (Finset.sum_le_sum fun i _ ↦ measureReal_mem_revealedSet_le i).trans
    (sum_range_revealedMass_le hn)

end revealed

end Kolmogorov.PointToSet
