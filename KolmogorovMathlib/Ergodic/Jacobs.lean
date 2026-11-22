/-
Copyright (c) 2026 Emma Dinowitz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emma Dinowitz
-/
import KolmogorovMathlib.Ergodic.FinePartitions
import KolmogorovMathlib.Ergodic.ErgodicDecomposition
import Mathlib.Analysis.Convex.Integral

/-!
# Jacobs' theorem: the Kolmogorov–Sinai entropy is affine over integral decompositions

Let `ρ` be a probability measure on a parameter space `Ω`, `κ : Kernel Ω X` a Markov kernel whose
values `κ ω` are `T`-invariant for `ρ`-almost every `ω`, and `μ = ∫ κ ω dρ(ω) = ρ.bind κ`.

* `jacobs_entropyRate_bind`: for every finite measurable partition `P`,
  `h_μ(T, P) = ∫ h_{κ ω}(T, P) dρ(ω)`.
* `jacobs_ksEntropy_bind` (Jacobs' theorem): on a compact metric space,
  `h_μ(T) = ∫ h_{κ ω}(T) dρ(ω)`; in particular
  (`jacobs_ksEntropy_eq_lintegral_ergodicDecomposition`) the Kolmogorov–Sinai entropy of an
  invariant measure is the mean entropy of its ergodic components
  (`exists_ergodicDecomposition`).

## Proof

`≥` for a partition (`jacobs_lintegral_entropyRate_le`, no invariance needed): by Jensen's
inequality for the concave `t ↦ -t log t`, `∫ H_{κ ω}(P^n) dρ ≤ H_μ(P^n)` for every `n`.

`≤` for a partition (`jacobs_entropyRate_le_lintegral`). Fix `N ≥ 1` and `ε > 0`. Quantize the
vector `(κ ω (C))_C` of masses of the `|ι|^N` cells `C` of `P^N` on a grid of mesh `1/M`; the
fibres `Ω_g` of the quantization form a finite measurable partition of `Ω`. Then
`μ = ∑_g μ_g`, `μ_g = ∫_{Ω_g} κ ω dρ`, each `μ_g` is invariant, and by subadditivity of
`t ↦ -t log t`, `H_μ(Q) ≤ ∑_g H(μ_g, Q) = ∑_g (ρ(Ω_g) H_{ν_g}(Q) - ρ(Ω_g) log₂ ρ(Ω_g))` with
`ν_g = μ_g / ρ(Ω_g)`. With `Q = P^{kN}`, subadditivity of `n ↦ H_{ν_g}(P^n)` gives
`H_μ(P^{kN}) ≤ k ∑_g ρ(Ω_g) H_{ν_g}(P^N) + C`. The masses `ν_g(C)` are averages of masses
`κ ω (C)`, `ω ∈ Ω_g`, all in one grid interval, so by uniform continuity of `-t log t`,
`ρ(Ω_g) H_{ν_g}(P^N) ≤ ∫_{Ω_g} H_{κ ω}(P^N) dρ + ρ(Ω_g) N ε`. Dividing by `kN` and letting
`k → ∞`: `h_μ(T, P) ≤ ∫ H_{κ ω}(P^N)/N dρ + ε`. Finally `H_{κ ω}(P^N)/N → h_{κ ω}(T, P)` a.e.,
boundedly, so dominated convergence gives the claim.

For the Kolmogorov–Sinai entropy, `≤` follows by taking suprema. For `≥` on a compact metric
space, fix partitions `P_j` with cells of diameter `→ 0` (`jacobs_exists_finePartitions`); by
Walters, Theorem 8.3 (`tendsto_entropyRate_ksEntropy`) `h_{κ ω}(T, P_j) → h_{κ ω}(T)` for a.e.
`ω`, and Fatou's lemma gives `∫ h_{κ ω}(T) dρ ≤ liminf_j h_μ(T, P_j) ≤ h_μ(T)`.

Only the measurable functions `ω ↦ h_{κ ω}(T, P)` enter limit theorems; on a compact metric space
`ω ↦ h_{κ ω}(T)` is almost everywhere a `liminf` of them, hence a.e.-measurable
(`jacobs_aemeasurable_ksEntropy`), so `∫⁻ ω, h_{κ ω}(T) dρ` is an honest integral.

Blueprint node `erg:jacobs`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal

namespace Kolmogorov.Ergodic

/-! ### Real-variable facts about `entropyTerm` -/

section Real

/-- `entropyTerm q = negMulLog q / log 2` (through `toReal`). -/
private lemma jacobs_entropyTerm_eq (q : ℝ≥0∞) :
    entropyTerm q = Real.negMulLog q.toReal / Real.log 2 := by
  simp only [entropyTerm, Real.negMulLog, Real.logb]
  ring

/-- `entropyTerm` is measurable. -/
private lemma jacobs_measurable_entropyTerm : Measurable entropyTerm := by
  have : entropyTerm = fun q ↦ Real.negMulLog q.toReal / Real.log 2 :=
    funext jacobs_entropyTerm_eq
  rw [this]
  exact ((Real.continuous_negMulLog.measurable).comp ENNReal.measurable_toReal).div_const _

/-- `entropyTerm q ≤ 1 / log 2` for every `q`. -/
private lemma jacobs_entropyTerm_le (q : ℝ≥0∞) : entropyTerm q ≤ (Real.log 2)⁻¹ := by
  rw [jacobs_entropyTerm_eq, div_eq_mul_inv]
  have hlog : 0 < (Real.log 2)⁻¹ := inv_pos.2 (Real.log_pos one_lt_two)
  have h := Real.negMulLog_le_one_sub_self (ENNReal.toReal_nonneg (a := q))
  have h1 : Real.negMulLog q.toReal ≤ 1 := h.trans (by linarith [ENNReal.toReal_nonneg (a := q)])
  nlinarith

/-- Masses of a probability measure are at most one, in `ℝ`. -/
private lemma jacobs_toReal_le_one {X : Type*} [MeasurableSpace X] (ν : Measure X)
    [IsProbabilityMeasure ν] (A : Set X) : (ν A).toReal ≤ 1 :=
  ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using prob_le_one (μ := ν) (s := A))

/-- Subadditivity of `t ↦ -t log t` on `[0, ∞)`. -/
private lemma jacobs_negMulLog_add_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.negMulLog (a + b) ≤ Real.negMulLog a + Real.negMulLog b := by
  have key : ∀ {a b : ℝ}, 0 ≤ a → 0 ≤ b → -a * Real.log (a + b) ≤ -a * Real.log a := by
    intro a b ha hb
    rcases ha.eq_or_lt with rfl | ha'
    · simp
    · have := Real.log_le_log ha' (le_add_of_nonneg_right hb)
      nlinarith
  simp only [Real.negMulLog]
  have h1 := key ha hb
  have h2 := key hb ha
  rw [add_comm b a] at h2
  nlinarith

/-- Subadditivity of `t ↦ -t log t` over finite sums of nonnegative reals. -/
private lemma jacobs_negMulLog_sum_le {G : Type*} (s : Finset G) {x : G → ℝ}
    (hx : ∀ g, 0 ≤ x g) : Real.negMulLog (∑ g ∈ s, x g) ≤ ∑ g ∈ s, Real.negMulLog (x g) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert g s hg ih =>
    rw [Finset.sum_insert hg, Finset.sum_insert hg]
    exact (jacobs_negMulLog_add_le (hx g) (Finset.sum_nonneg fun _ _ ↦ hx _)).trans
      (add_le_add_right ih _)

/-- Uniform continuity of `entropyTerm` on masses at most one. -/
private lemma jacobs_exists_grid {η : ℝ} (hη : 0 < η) :
    ∃ M : ℕ, 0 < M ∧ ∀ a b : ℝ≥0∞, a ≤ 1 → b ≤ 1 → |a.toReal - b.toReal| ≤ 1 / M →
      |entropyTerm a - entropyTerm b| ≤ η := by
  have hlog : 0 < Real.log 2 := Real.log_pos one_lt_two
  have huc := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).uniformContinuousOn_of_continuous
    Real.continuous_negMulLog.continuousOn
  obtain ⟨δ, hδ, hδf⟩ := Metric.uniformContinuousOn_iff_le.1 huc (η * Real.log 2)
    (mul_pos hη hlog)
  refine ⟨⌊1 / δ⌋₊ + 1, Nat.succ_pos _, fun a b ha hb hab ↦ ?_⟩
  have hM : 1 / ((⌊1 / δ⌋₊ + 1 : ℕ) : ℝ) ≤ δ := by
    rw [div_le_iff₀ (by positivity)]
    have := Nat.lt_floor_add_one (1 / δ)
    rw [div_lt_iff₀ hδ] at this
    push_cast
    nlinarith
  have hmem : ∀ c : ℝ≥0∞, c ≤ 1 → c.toReal ∈ Set.Icc (0 : ℝ) 1 := fun c hc ↦
    ⟨ENNReal.toReal_nonneg, by simpa using ENNReal.toReal_mono ENNReal.one_ne_top hc⟩
  have h := hδf _ (hmem a ha) _ (hmem b hb) (by rw [Real.dist_eq]; exact hab.trans hM)
  rw [Real.dist_eq] at h
  rw [jacobs_entropyTerm_eq, jacobs_entropyTerm_eq, ← sub_div, abs_div,
    abs_of_pos hlog, div_le_iff₀ hlog]
  exact h

end Real

section General

variable {X : Type*} [MeasurableSpace X] {Ω : Type*} [MeasurableSpace Ω]

/-- The entropy of a fixed family of measurable sets under the values of a kernel is a
measurable function of the parameter. -/
private lemma jacobs_measurable_partitionEntropy {ι : Type*} [Fintype ι] (κ : Kernel Ω X)
    {Q : ι → Set X} (hQ : ∀ i, MeasurableSet (Q i)) :
    Measurable fun ω ↦ partitionEntropy (κ ω) Q :=
  Finset.measurable_sum _ fun i _ ↦ jacobs_measurable_entropyTerm.comp (κ.measurable_coe (hQ i))

/-- The entropy rate of a fixed partition under the values of a kernel is a measurable function
of the parameter. -/
private lemma jacobs_measurable_entropyRate {ι : Type*} [Fintype ι] [DecidableEq ι]
    (κ : Kernel Ω X) {T : X → X} (hT : Measurable T) {P : ι → Set X}
    (hP : IsMeasurablePartition P) : Measurable fun ω ↦ entropyRate (κ ω) T P :=
  Measurable.iInf fun n ↦ Measurable.iInf fun _ ↦ ENNReal.measurable_ofReal.comp
    ((jacobs_measurable_partitionEntropy κ (hP.refinement hT n).measurableSet).div_const _)

/-- The entropy of a family of sets under a probability measure is at most `|ι| / log 2`. -/
private lemma jacobs_partitionEntropy_le {ι : Type*} [Fintype ι] (ν : Measure X)
    (Q : ι → Set X) : partitionEntropy ν Q ≤ Fintype.card ι * (Real.log 2)⁻¹ := by
  rw [partitionEntropy]
  calc ∑ i, entropyTerm (ν (Q i)) ≤ ∑ _i : ι, (Real.log 2)⁻¹ :=
        Finset.sum_le_sum fun i _ ↦ jacobs_entropyTerm_le _
    _ = _ := by simp

/-- The function `ω ↦ H_{κ ω}(Q)` is integrable. -/
private lemma jacobs_integrable_partitionEntropy {ι : Type*} [Fintype ι] (ρ : Measure Ω)
    [IsFiniteMeasure ρ] (κ : Kernel Ω X) [IsMarkovKernel κ] {Q : ι → Set X}
    (hQ : ∀ i, MeasurableSet (Q i)) : Integrable (fun ω ↦ partitionEntropy (κ ω) Q) ρ := by
  refine Integrable.of_bound (jacobs_measurable_partitionEntropy κ hQ).aestronglyMeasurable
    (Fintype.card ι * (Real.log 2)⁻¹) (Eventually.of_forall fun ω ↦ ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (partitionEntropy_nonneg _ _)]
  exact jacobs_partitionEntropy_le _ _

/-- Jensen's inequality for one cell: `∫ -κ_ω(C) log₂ κ_ω(C) dρ ≤ -μ(C) log₂ μ(C)`. -/
private lemma jacobs_integral_entropyTerm_le (ρ : Measure Ω) [IsProbabilityMeasure ρ]
    (κ : Kernel Ω X) [IsMarkovKernel κ] {C : Set X} (hC : MeasurableSet C) :
    ∫ ω, entropyTerm (κ ω C) ∂ρ ≤ entropyTerm (ρ.bind κ C) := by
  have hf : Measurable fun ω ↦ (κ ω C).toReal := (κ.measurable_coe hC).ennreal_toReal
  have hfi : Integrable (fun ω ↦ (κ ω C).toReal) ρ := by
    refine Integrable.of_bound hf.aestronglyMeasurable 1 (Eventually.of_forall fun ω ↦ ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
    simpa using ENNReal.toReal_mono ENNReal.one_ne_top (prob_le_one (μ := κ ω) (s := C))
  have hgi : Integrable (Real.negMulLog ∘ fun ω ↦ (κ ω C).toReal) ρ := by
    refine Integrable.of_bound (Real.continuous_negMulLog.measurable.comp hf).aestronglyMeasurable
      1 (Eventually.of_forall fun ω ↦ ?_)
    have h1 : (κ ω C).toReal ≤ 1 := by
      simpa using ENNReal.toReal_mono ENNReal.one_ne_top (prob_le_one (μ := κ ω) (s := C))
    rw [Function.comp_apply, Real.norm_eq_abs,
      abs_of_nonneg (Real.negMulLog_nonneg ENNReal.toReal_nonneg h1)]
    exact (Real.negMulLog_le_one_sub_self ENNReal.toReal_nonneg).trans
      (by linarith [ENNReal.toReal_nonneg (a := κ ω C)])
  have hJ := Real.concaveOn_negMulLog.le_map_integral Real.continuous_negMulLog.continuousOn
    isClosed_Ici (Eventually.of_forall fun ω ↦ (ENNReal.toReal_nonneg : 0 ≤ (κ ω C).toReal))
    hfi hgi
  have hmean : ∫ ω, (κ ω C).toReal ∂ρ = (ρ.bind κ C).toReal := by
    rw [Measure.bind_apply hC κ.measurable.aemeasurable,
      integral_toReal (κ.measurable_coe hC).aemeasurable
        (Eventually.of_forall fun ω ↦ measure_lt_top _ _)]
  simp_rw [jacobs_entropyTerm_eq]
  rw [integral_div, ← hmean]
  exact div_le_div_of_nonneg_right hJ (Real.log_pos one_lt_two).le

/-- Concavity of entropy: `∫ H_{κ ω}(Q) dρ ≤ H_μ(Q)` for `μ = ρ.bind κ`. -/
private lemma jacobs_integral_partitionEntropy_le {ι : Type*} [Fintype ι] (ρ : Measure Ω)
    [IsProbabilityMeasure ρ] (κ : Kernel Ω X) [IsMarkovKernel κ] {Q : ι → Set X}
    (hQ : ∀ i, MeasurableSet (Q i)) :
    ∫ ω, partitionEntropy (κ ω) Q ∂ρ ≤ partitionEntropy (ρ.bind κ) Q := by
  simp only [partitionEntropy]
  rw [integral_finsetSum _ fun i _ ↦ ?_]
  · exact Finset.sum_le_sum fun i _ ↦ jacobs_integral_entropyTerm_le ρ κ (hQ i)
  · refine Integrable.of_bound
      (jacobs_measurable_entropyTerm.comp (κ.measurable_coe (hQ i))).aestronglyMeasurable
      (Real.log 2)⁻¹ (Eventually.of_forall fun ω ↦ ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (entropyTerm_nonneg prob_le_one)]
    exact jacobs_entropyTerm_le _

/-- The easy half of Jacobs' theorem for one partition (concavity of entropy): the mean entropy
rate of the components is at most the entropy rate of the mixture. No invariance is needed.
Blueprint node `erg:jacobs`. -/
theorem jacobs_lintegral_entropyRate_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ρ : Measure Ω) [IsProbabilityMeasure ρ] (κ : Kernel Ω X) [IsMarkovKernel κ] (T : X → X)
    (hT : Measurable T) {P : ι → Set X} (hP : IsMeasurablePartition P) :
    ∫⁻ ω, entropyRate (κ ω) T P ∂ρ ≤ entropyRate (ρ.bind κ) T P := by
  refine le_iInf₂ fun n hn ↦ ?_
  have hQ := (hP.refinement hT n).measurableSet
  calc ∫⁻ ω, entropyRate (κ ω) T P ∂ρ
      ≤ ∫⁻ ω, ENNReal.ofReal (partitionEntropy (κ ω) (refinement T P n) / n) ∂ρ :=
        lintegral_mono fun ω ↦ iInf₂_le n hn
    _ = ENNReal.ofReal (∫ ω, partitionEntropy (κ ω) (refinement T P n) / n ∂ρ) :=
        (ofReal_integral_eq_lintegral_ofReal
          ((jacobs_integrable_partitionEntropy ρ κ hQ).div_const _)
          (Eventually.of_forall fun ω ↦
            div_nonneg (partitionEntropy_nonneg _ _) n.cast_nonneg)).symm
    _ ≤ ENNReal.ofReal (refinementEntropy (ρ.bind κ) T P n / n) := by
        refine ENNReal.ofReal_le_ofReal ?_
        rw [integral_div]
        exact div_le_div_of_nonneg_right (jacobs_integral_partitionEntropy_le ρ κ hQ)
          n.cast_nonneg

/-! ### The hard half: finite mixtures and quantization -/

/-- The entropy of `t • ν` on the cells of a family whose `ν`-masses sum to one (or `t = 0`):
`∑_i entropyTerm (t ν(Q_i)) = t H_ν(Q) + entropyTerm t`. -/
private lemma jacobs_sum_negMulLog_mul {ι : Type*} [Fintype ι] {ν : Measure X} {t : ℝ≥0∞}
    {Q : ι → Set X} (h : t ≠ 0 → ∑ i, (ν (Q i)).toReal = 1) :
    ∑ i, Real.negMulLog (t.toReal * (ν (Q i)).toReal) / Real.log 2 =
      t.toReal * partitionEntropy ν Q + entropyTerm t := by
  simp_rw [Real.negMulLog_mul, add_div]
  rw [Finset.sum_add_distrib, partitionEntropy, Finset.mul_sum]
  simp_rw [jacobs_entropyTerm_eq]
  by_cases ht : t = 0
  · simp [ht]
  · rw [← Finset.sum_div, ← Finset.sum_mul, h ht, one_mul, add_comm]
    congr 1
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    ring

/-- Entropy of a finite mixture: if `μ(Q_i) = ∑_g t_g ν_g(Q_i)` on the cells, then
`H_μ(Q) ≤ ∑_g (t_g H_{ν_g}(Q) + entropyTerm t_g)` (subadditivity of `-t log t`). -/
private lemma jacobs_partitionEntropy_mixture_le {ι G : Type*} [Fintype ι] [Fintype G]
    {μ : Measure X} {ν : G → Measure X} {t : G → ℝ≥0∞} {Q : ι → Set X}
    (ht : ∀ g, t g ≠ ⊤) (hfin : ∀ g i, ν g (Q i) ≠ ⊤)
    (hν : ∀ g, t g ≠ 0 → ∑ i, (ν g (Q i)).toReal = 1)
    (hμ : ∀ i, μ (Q i) = ∑ g, t g * ν g (Q i)) :
    partitionEntropy μ Q ≤ ∑ g, ((t g).toReal * partitionEntropy (ν g) Q + entropyTerm (t g)) := by
  have hlog : 0 < Real.log 2 := Real.log_pos one_lt_two
  calc partitionEntropy μ Q
      = ∑ i, Real.negMulLog (∑ g, (t g).toReal * (ν g (Q i)).toReal) / Real.log 2 := by
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        rw [jacobs_entropyTerm_eq, hμ i, ENNReal.toReal_sum fun g _ ↦
          ENNReal.mul_ne_top (ht g) (hfin g i)]
        simp_rw [ENNReal.toReal_mul]
    _ ≤ ∑ i, ∑ g, Real.negMulLog ((t g).toReal * (ν g (Q i)).toReal) / Real.log 2 := by
        refine Finset.sum_le_sum fun i _ ↦ ?_
        rw [← Finset.sum_div]
        exact div_le_div_of_nonneg_right (jacobs_negMulLog_sum_le _ fun g ↦
          mul_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg) hlog.le
    _ = ∑ g, ((t g).toReal * partitionEntropy (ν g) Q + entropyTerm (t g)) := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun g _ ↦ jacobs_sum_negMulLog_mul (hν g)

/-- Iterated subadditivity: `H_ν(P^{kN}) ≤ k H_ν(P^N)` for an invariant probability measure. -/
private lemma jacobs_refinementEntropy_mul_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    {ν : Measure X} [IsProbabilityMeasure ν] {T : X → X} (hT : MeasurePreserving T ν ν)
    {P : ι → Set X} (hP : IsMeasurablePartition P) (N k : ℕ) :
    refinementEntropy ν T P (k * N) ≤ k * refinementEntropy ν T P N := by
  induction k with
  | zero =>
    simp [refinementEntropy, partitionEntropy, refinement, entropyTerm]
  | succ k ih =>
    rw [Nat.succ_mul]
    refine (refinementEntropy_add_le hT hP (k * N) N).trans ?_
    push_cast
    linarith

/-- Two reals in `[a, a + d]` are at distance at most `d`. -/
private lemma jacobs_abs_sub_le {x y a d : ℝ} (hx : x ∈ Set.Icc a (a + d))
    (hy : y ∈ Set.Icc a (a + d)) : |x - y| ≤ d := by
  rw [abs_sub_le_iff]
  constructor <;> linarith [hx.1, hx.2, hy.1, hy.2]

/-- The grid label of a mass: `min ⌊x M⌋ M`. -/
private def jacobsLabel (M : ℕ) (x : ℝ) : Fin (M + 1) :=
  ⟨min ⌊x * M⌋₊ M, Nat.lt_succ_of_le (min_le_right _ _)⟩

/-- A mass in `[0, 1]` lies in the grid interval of its label. -/
private lemma jacobsLabel_mem {M : ℕ} (hM : 0 < M) {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    x ∈ Set.Icc ((jacobsLabel M x : ℕ) / M : ℝ) ((jacobsLabel M x : ℕ) / M + 1 / M) := by
  have hMr : (0 : ℝ) < M := Nat.cast_pos.2 hM
  have hfl : ⌊x * M⌋₊ ≤ M := by
    have : ⌊x * M⌋₊ ≤ ⌊(M : ℝ)⌋₊ := Nat.floor_le_floor (by nlinarith)
    simpa using this
  have hlab : (jacobsLabel M x : ℕ) = ⌊x * M⌋₊ := by
    simp [jacobsLabel, min_eq_left hfl]
  rw [hlab, ← add_div]
  constructor
  · rw [div_le_iff₀ hMr]
    exact Nat.floor_le (by positivity)
  · rw [le_div_iff₀ hMr]
    exact (Nat.lt_floor_add_one _).le

/-- The quantization map is measurable. -/
private lemma jacobs_measurable_label {M : ℕ} {f : Ω → ℝ} (hf : Measurable f) :
    Measurable fun ω ↦ jacobsLabel M (f ω) := by
  have h1 : Measurable fun ω ↦ ⌊f ω * M⌋₊ :=
    (Nat.floor_mono.measurable).comp (hf.mul_const _)
  exact (measurable_from_nat (f := fun n : ℕ ↦
    (⟨min n M, Nat.lt_succ_of_le (min_le_right _ _)⟩ : Fin (M + 1)))).comp h1

/-- The core estimate of the hard half: for `N ≥ 1` and `ε > 0`,
`h_μ(T, P) ≤ ∫ H_{κ ω}(P^N) dρ / N + ε`. Quantize the masses of the cells of `P^N` on a grid
fine enough for `ε`, compare the mixture with its finitely many pieces (subadditivity of
`-t log t`, iterated subadditivity of the pieces' refinement entropies), and compare each piece
with its components (uniform continuity of `-t log t`). -/
private lemma jacobs_entropyRate_le_integral_add {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ρ : Measure Ω) [IsProbabilityMeasure ρ] (κ : Kernel Ω X) [IsMarkovKernel κ] {T : X → X}
    (hinv : ∀ᵐ ω ∂ρ, MeasurePreserving T (κ ω) (κ ω)) {P : ι → Set X}
    (hP : IsMeasurablePartition P) {N : ℕ} (hN : 1 ≤ N) {ε : ℝ} (hε : 0 < ε) :
    entropyRate (ρ.bind κ) T P ≤
      ENNReal.ofReal ((∫ ω, partitionEntropy (κ ω) (refinement T P N) ∂ρ) / N + ε) := by
  obtain ⟨ω₀, hω₀⟩ := hinv.exists
  have hT := hω₀.measurable
  have hC : IsMeasurablePartition (refinement T P N) := hP.refinement hT N
  set η : ℝ := ε / (Fintype.card (Fin N → ι) + 1) with hη
  have hη0 : 0 < η := by positivity
  obtain ⟨M, hM, hgrid⟩ := jacobs_exists_grid hη0
  -- the quantization of the masses of the cells of `P^N`
  let Φ : Ω → (Fin N → ι) → Fin (M + 1) := fun ω w ↦
    jacobsLabel M (κ ω (refinement T P N w)).toReal
  have hΦ : Measurable Φ := measurable_pi_iff.2 fun w ↦
    jacobs_measurable_label (κ.measurable_coe (hC.measurableSet w)).ennreal_toReal
  let S : ((Fin N → ι) → Fin (M + 1)) → Set Ω := fun g ↦ Φ ⁻¹' {g}
  have hS : ∀ g, MeasurableSet (S g) := fun g ↦ hΦ (measurableSet_singleton g)
  have hSd : Pairwise (Function.onFun Disjoint S) := fun g g' h ↦
    (Set.disjoint_singleton.2 h).preimage Φ
  have hSu : ⋃ g, S g = Set.univ :=
    Set.eq_univ_of_forall fun ω ↦ Set.mem_iUnion.2 ⟨Φ ω, rfl⟩
  have hsplit : ∀ f : Ω → ℝ≥0∞, ∫⁻ ω, f ω ∂ρ = ∑ g, ∫⁻ ω in S g, f ω ∂ρ := fun f ↦ by
    have h := lintegral_iUnion (μ := ρ) hS hSd f
    rwa [hSu, Measure.restrict_univ, tsum_fintype] at h
  have ht : ∀ g, ρ (S g) ≠ ⊤ := fun g ↦ measure_ne_top _ _
  have htsum : ∑ g, (ρ (S g)).toReal = 1 := by
    have h := hsplit 1
    simp only [Pi.one_apply, lintegral_one, Measure.restrict_apply_univ, measure_univ] at h
    rw [← ENNReal.toReal_sum fun g _ ↦ ht g, ← h, ENNReal.toReal_one]
  -- the pieces of the mixture
  let ν : ((Fin N → ι) → Fin (M + 1)) → Measure X := fun g ↦ (ρ[|S g]).bind κ
  have hνA : ∀ g {A : Set X}, MeasurableSet A → ν g A = ∫⁻ ω, κ ω A ∂ρ[|S g] :=
    fun g A hA ↦ Measure.bind_apply hA κ.measurable.aemeasurable
  have hmix : ∀ {A : Set X}, MeasurableSet A → ρ.bind κ A = ∑ g, ρ (S g) * ν g A := by
    intro A hA
    rw [Measure.bind_apply hA κ.measurable.aemeasurable, hsplit]
    refine Finset.sum_congr rfl fun g _ ↦ ?_
    rw [hνA g hA]
    simp only [ProbabilityTheory.cond, lintegral_smul_measure, smul_eq_mul]
    by_cases h0 : ρ (S g) = 0
    · rw [h0, zero_mul, setLIntegral_measure_zero _ _ h0]
    · rw [← mul_assoc, ENNReal.mul_inv_cancel h0 (measure_ne_top _ _), one_mul]
  have hνprob : ∀ g, ρ (S g) ≠ 0 → IsProbabilityMeasure (ν g) := fun g h ↦ by
    have := cond_isProbabilityMeasure (μ := ρ) h
    exact ⟨by rw [hνA g MeasurableSet.univ]; simp⟩
  have hνfin : ∀ g {A : Set X}, MeasurableSet A → ν g A ≠ ⊤ := fun g A hA ↦ by
    rw [hνA g hA]
    refine ne_top_of_le_ne_top (measure_ne_top (ρ[|S g]) Set.univ) ?_
    calc ∫⁻ ω, κ ω A ∂ρ[|S g] ≤ ∫⁻ _, 1 ∂ρ[|S g] := lintegral_mono fun ω ↦ prob_le_one
      _ = _ := lintegral_one
  have hνinv : ∀ g, MeasurePreserving T (ν g) (ν g) := fun g ↦ by
    refine ⟨hT, Measure.ext fun A hA ↦ ?_⟩
    rw [Measure.map_apply hT hA, hνA g (hT hA), hνA g hA]
    exact lintegral_congr_ae (cond_absolutelyContinuous.ae_le
      (hinv.mono fun ω hω ↦ hω.measure_preimage hA.nullMeasurableSet))
  -- each piece is close to each of its components on the cells of `P^N`
  have hcell : ∀ g, ρ (S g) ≠ 0 → ∀ ω ∈ S g, ∀ w,
      entropyTerm (ν g (refinement T P N w)) ≤ entropyTerm (κ ω (refinement T P N w)) + η := by
    intro g hg ω hω w
    have := hνprob g hg
    have := cond_isProbabilityMeasure (μ := ρ) hg
    obtain ⟨lo, hlo0, hlo⟩ : ∃ lo : ℝ, 0 ≤ lo ∧ lo = ((g w : ℕ) : ℝ) / M :=
      ⟨_, by positivity, rfl⟩
    have hd0 : (0 : ℝ) ≤ lo + 1 / M := by positivity
    have hmemκ : ∀ ω' ∈ S g, (κ ω' (refinement T P N w)).toReal ∈ Set.Icc lo (lo + 1 / M) := by
      intro ω' hω'
      have h1 := jacobsLabel_mem hM (ENNReal.toReal_nonneg (a := κ ω' (refinement T P N w)))
        (jacobs_toReal_le_one (κ ω') _)
      have h2 : jacobsLabel M (κ ω' (refinement T P N w)).toReal = g w := congrFun hω' w
      rwa [h2, ← hlo] at h1
    have hae : ∀ᵐ ω' ∂ρ[|S g], ENNReal.ofReal lo ≤ κ ω' (refinement T P N w) ∧
        κ ω' (refinement T P N w) ≤ ENNReal.ofReal (lo + 1 / M) := by
      filter_upwards [ae_cond_mem (hS g)] with ω' hω'
      have h := hmemκ ω' hω'
      constructor
      · exact (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)).2 h.1
      · exact ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _) hd0 |>.2 h.2
    have hmemν : (ν g (refinement T P N w)).toReal ∈ Set.Icc lo (lo + 1 / M) := by
      rw [hνA g (hC.measurableSet w)]
      constructor
      · refine (ENNReal.ofReal_le_iff_le_toReal ?_).1 ?_
        · exact (hνA g (hC.measurableSet w)) ▸ hνfin g (hC.measurableSet w)
        · calc ENNReal.ofReal lo = ∫⁻ _, ENNReal.ofReal lo ∂ρ[|S g] := by simp
            _ ≤ _ := lintegral_mono_ae (hae.mono fun _ h ↦ h.1)
      · refine ENNReal.toReal_le_of_le_ofReal hd0 ?_
        calc ∫⁻ ω', κ ω' (refinement T P N w) ∂ρ[|S g]
            ≤ ∫⁻ _, ENNReal.ofReal (lo + 1 / M) ∂ρ[|S g] :=
              lintegral_mono_ae (hae.mono fun _ h ↦ h.2)
          _ = ENNReal.ofReal (lo + 1 / M) := by simp
    have h := hgrid _ _ prob_le_one prob_le_one (jacobs_abs_sub_le hmemν (hmemκ ω hω))
    linarith [(abs_sub_le_iff.1 h).1]
  have hint : ∀ g, (ρ (S g)).toReal * partitionEntropy (ν g) (refinement T P N) ≤
      ∫ ω in S g, partitionEntropy (κ ω) (refinement T P N) ∂ρ +
        (ρ (S g)).toReal * (Fintype.card (Fin N → ι) * η) := by
    intro g
    by_cases hg : ρ (S g) = 0
    · simp only [hg, ENNReal.toReal_zero, zero_mul, add_zero]
      exact setIntegral_nonneg (hS g) fun ω _ ↦ partitionEntropy_nonneg _ _
    · have hfib : ∀ ω ∈ S g, partitionEntropy (ν g) (refinement T P N) -
          Fintype.card (Fin N → ι) * η ≤ partitionEntropy (κ ω) (refinement T P N) := by
        intro ω hω
        have h : partitionEntropy (ν g) (refinement T P N) ≤
            ∑ w, (entropyTerm (κ ω (refinement T P N w)) + η) :=
          Finset.sum_le_sum fun w _ ↦ hcell g hg ω hω w
        rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at h
        exact sub_le_iff_le_add.2 h
      have h := setIntegral_ge_of_const_le (hS g) (measure_ne_top _ _) hfib
        (jacobs_integrable_partitionEntropy ρ κ hC.measurableSet).integrableOn
      rw [smul_eq_mul, measureReal_def, mul_sub] at h
      linarith
  -- summing over the pieces
  set I := ∫ ω, partitionEntropy (κ ω) (refinement T P N) ∂ρ with hI
  set D := ∑ g, entropyTerm (ρ (S g)) with hD
  have hsumint : ∑ g, ∫ ω in S g, partitionEntropy (κ ω) (refinement T P N) ∂ρ = I := by
    rw [← integral_iUnion_fintype hS hSd fun g ↦
      (jacobs_integrable_partitionEntropy ρ κ hC.measurableSet).integrableOn, hSu,
      setIntegral_univ]
  have hmain : ∀ k : ℕ, refinementEntropy (ρ.bind κ) T P (k * N) ≤
      k * (I + Fintype.card (Fin N → ι) * η) + D := by
    intro k
    have hQ := hP.refinement hT (k * N)
    have hk0 : (0 : ℝ) ≤ k := k.cast_nonneg
    calc refinementEntropy (ρ.bind κ) T P (k * N)
        ≤ ∑ g, ((ρ (S g)).toReal * partitionEntropy (ν g) (refinement T P (k * N)) +
            entropyTerm (ρ (S g))) := by
          refine jacobs_partitionEntropy_mixture_le ht (fun g i ↦ hνfin g (hQ.measurableSet i))
            (fun g hg ↦ ?_) (fun i ↦ hmix (hQ.measurableSet i))
          have := hνprob g hg
          simpa using (hQ.toReal_measure_eq_sum_inter (μ := ν g) MeasurableSet.univ).symm
      _ ≤ ∑ g, (k * ((ρ (S g)).toReal * partitionEntropy (ν g) (refinement T P N)) +
            entropyTerm (ρ (S g))) := by
          refine Finset.sum_le_sum fun g _ ↦ ?_
          by_cases hg : ρ (S g) = 0
          · simp [hg]
          · have := hνprob g hg
            have h := jacobs_refinementEntropy_mul_le (hνinv g) hP N k
            simp only [refinementEntropy] at h
            have ht0 : 0 ≤ (ρ (S g)).toReal := ENNReal.toReal_nonneg
            nlinarith
      _ ≤ ∑ g, (k * (∫ ω in S g, partitionEntropy (κ ω) (refinement T P N) ∂ρ +
            (ρ (S g)).toReal * (Fintype.card (Fin N → ι) * η)) + entropyTerm (ρ (S g))) :=
          Finset.sum_le_sum fun g _ ↦ add_le_add_left (mul_le_mul_of_nonneg_left (hint g) hk0) _
      _ = k * (I + Fintype.card (Fin N → ι) * η) + D := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_add_distrib, hsumint,
            ← Finset.sum_mul, htsum, one_mul]
  -- dividing by `kN` and letting `k → ∞`
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hcW : (Fintype.card (Fin N → ι) : ℝ) * η ≤ ε := by
    rw [hη, mul_div_assoc', div_le_iff₀ (by positivity)]
    nlinarith
  have hbound : ∀ k : ℕ, 1 ≤ k →
      entropyRate (ρ.bind κ) T P ≤ ENNReal.ofReal (I / N + ε + D / N / k) := by
    intro k hk
    have hkN : 1 ≤ k * N := Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega))
    refine (iInf₂_le (k * N) hkN).trans (ENNReal.ofReal_le_ofReal ?_)
    have hkr : (0 : ℝ) < k := by exact_mod_cast hk
    rw [div_le_iff₀ (by positivity), Nat.cast_mul]
    have hexp : (I / N + ε + D / N / k) * (k * N) = k * I + k * N * ε + D := by
      field_simp
    rw [hexp]
    have h1 := hmain k
    have h2 : (k : ℝ) * (Fintype.card (Fin N → ι) * η) ≤ k * N * ε := by
      have h3 : (k : ℝ) * ε ≤ k * N * ε := by
        have : (1 : ℝ) ≤ N := by exact_mod_cast hN
        nlinarith [mul_nonneg (mul_nonneg hkr.le hε.le) (sub_nonneg.2 this)]
      nlinarith
    nlinarith
  have hlim : Tendsto (fun k : ℕ ↦ ENNReal.ofReal (I / N + ε + D / N / k)) atTop
      (𝓝 (ENNReal.ofReal (I / N + ε))) := by
    have h := (tendsto_const_div_atTop_nhds_zero_nat (D / N)).const_add (I / N + ε)
    rw [add_zero] at h
    exact ENNReal.tendsto_ofReal h
  exact ge_of_tendsto hlim (eventually_atTop.2 ⟨1, hbound⟩)

/-- The hard half of Jacobs' theorem for one partition: the entropy rate of a mixture of
invariant measures is at most the mean entropy rate of the components.
Blueprint node `erg:jacobs`. -/
theorem jacobs_entropyRate_le_lintegral {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ρ : Measure Ω) [IsProbabilityMeasure ρ] (κ : Kernel Ω X) [IsMarkovKernel κ] {T : X → X}
    (hinv : ∀ᵐ ω ∂ρ, MeasurePreserving T (κ ω) (κ ω)) {P : ι → Set X}
    (hP : IsMeasurablePartition P) :
    entropyRate (ρ.bind κ) T P ≤ ∫⁻ ω, entropyRate (κ ω) T P ∂ρ := by
  obtain ⟨ω₀, hω₀⟩ := hinv.exists
  have hT := hω₀.measurable
  set F : ℕ → Ω → ℝ≥0∞ := fun N ω ↦
    ENNReal.ofReal (partitionEntropy (κ ω) (refinement T P N) / N)
  have hFm : ∀ N, Measurable (F N) := fun N ↦ ENNReal.measurable_ofReal.comp
    ((jacobs_measurable_partitionEntropy κ (hP.refinement hT N).measurableSet).div_const _)
  have hlog : 0 ≤ Real.logb 2 (Fintype.card ι) :=
    (partitionEntropy_nonneg (κ ω₀) P).trans (partitionEntropy_le_logb_card (κ ω₀) hP)
  have hFb : ∀ N, ∀ᵐ ω ∂ρ, F N ω ≤ ENNReal.ofReal (Real.logb 2 (Fintype.card ι)) :=
    fun N ↦ Eventually.of_forall fun ω ↦ by
      refine ENNReal.ofReal_le_ofReal ?_
      rcases Nat.eq_zero_or_pos N with rfl | hN
      · simpa using hlog
      · rw [div_le_iff₀ (by exact_mod_cast hN)]
        have h := partitionEntropy_le_logb_card (κ ω) (hP.refinement hT N)
        rw [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow, Real.logb_pow] at h
        linarith
  have hFt : ∀ᵐ ω ∂ρ, Tendsto (fun N ↦ F N ω) atTop (𝓝 (entropyRate (κ ω) T P)) :=
    hinv.mono fun ω hω ↦ tendsto_refinementEntropy_div hω hP
  have hconv := tendsto_lintegral_of_dominated_convergence _ hFm hFb
    (by simp [lintegral_const]) hFt
  refine ENNReal.le_of_forall_pos_le_add fun ε hε _ ↦ ?_
  have hε' : (0 : ℝ) < ε := hε
  refine ge_of_tendsto (hconv.add (tendsto_const_nhds (x := (ε : ℝ≥0∞))))
    (eventually_atTop.2 ⟨1, fun N hN ↦ ?_⟩)
  refine (jacobs_entropyRate_le_integral_add ρ κ hinv hP hN hε').trans_eq ?_
  have hint := (jacobs_integrable_partitionEntropy ρ κ
    (hP.refinement hT N).measurableSet).div_const (N : ℝ)
  rw [ENNReal.ofReal_add (div_nonneg (integral_nonneg fun ω ↦ partitionEntropy_nonneg _ _)
    N.cast_nonneg) hε'.le, ENNReal.ofReal_coe_nnreal, ← integral_div,
    ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall fun ω ↦
      div_nonneg (partitionEntropy_nonneg _ _) N.cast_nonneg)]

/-- Jacobs' theorem for one partition: the entropy rate of a finite measurable partition is
affine over integral decompositions into invariant measures. Blueprint node `erg:jacobs`. -/
theorem jacobs_entropyRate_bind {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ρ : Measure Ω) [IsProbabilityMeasure ρ] (κ : Kernel Ω X) [IsMarkovKernel κ] {T : X → X}
    (hinv : ∀ᵐ ω ∂ρ, MeasurePreserving T (κ ω) (κ ω)) {P : ι → Set X}
    (hP : IsMeasurablePartition P) :
    entropyRate (ρ.bind κ) T P = ∫⁻ ω, entropyRate (κ ω) T P ∂ρ := by
  obtain ⟨ω, hω⟩ := hinv.exists
  exact le_antisymm (jacobs_entropyRate_le_lintegral ρ κ hinv hP)
    (jacobs_lintegral_entropyRate_le ρ κ T hω.measurable hP)

/-- Jacobs' theorem, upper half, on any measurable space: the Kolmogorov–Sinai entropy of a
mixture of invariant measures is at most the mean entropy of the components.
Blueprint node `erg:jacobs`. -/
theorem jacobs_ksEntropy_bind_le (ρ : Measure Ω) [IsProbabilityMeasure ρ] (κ : Kernel Ω X)
    [IsMarkovKernel κ] {T : X → X} (hinv : ∀ᵐ ω ∂ρ, MeasurePreserving T (κ ω) (κ ω)) :
    ksEntropy (ρ.bind κ) T ≤ ∫⁻ ω, ksEntropy (κ ω) T ∂ρ := by
  refine iSup_le fun p ↦ iSup_le fun P ↦ iSup_le fun hP ↦ ?_
  exact (jacobs_entropyRate_le_lintegral ρ κ hinv hP).trans
    (lintegral_mono fun ω ↦ entropyRate_le_ksEntropy (κ ω) T hP)

end General

section Compact

variable {X : Type*} [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
  {Ω : Type*} [MeasurableSpace Ω]

/-- A compact metric space has finite measurable partitions with cells of diameter at most
`2 / (j + 1)`, for every `j`. Blueprint node `erg:jacobs`. -/
theorem jacobs_exists_finePartitions :
    ∃ (p : ℕ → ℕ) (P : (j : ℕ) → Fin (p j) → Set X), (∀ j, IsMeasurablePartition (P j)) ∧
      ∀ j i, Metric.diam (P j i) ≤ 2 / (j + 1) := by
  have key : ∀ r : ℝ, 0 < r → ∃ (p : ℕ) (Q : Fin p → Set X), IsMeasurablePartition Q ∧
      ∀ i, Metric.diam (Q i) ≤ 2 * r := by
    intro r hr
    obtain ⟨t, -, htf, hcov⟩ := finite_cover_balls_of_compact (isCompact_univ (X := X)) hr
    set e := htf.toFinset.equivFin
    set p := htf.toFinset.card
    let f : ℕ → Set X := fun n ↦
      if h : n < p then Metric.ball ((e.symm ⟨n, h⟩ : X)) r else ∅
    have hf : ∀ n, MeasurableSet (f n) := fun n ↦ by
      by_cases h : n < p
      · simp only [f, h, dite_true]
        exact measurableSet_ball
      · simp only [f, h, dite_false]
        exact MeasurableSet.empty
    refine ⟨p, fun i ↦ disjointed f i, ⟨fun i ↦ MeasurableSet.disjointed hf i,
      fun i j hij ↦ disjoint_disjointed f (Fin.val_injective.ne hij), ?_⟩, fun i ↦ ?_⟩
    · refine Set.eq_univ_of_forall fun x ↦ ?_
      have hx : x ∈ ⋃ n, f n := by
        obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.1 (hcov (Set.mem_univ x))
        have hy' : y ∈ htf.toFinset := htf.mem_toFinset.2 hy
        refine Set.mem_iUnion.2 ⟨e ⟨y, hy'⟩, ?_⟩
        simp only [f, (e ⟨y, hy'⟩).isLt, dite_true, Fin.eta, Equiv.symm_apply_apply]
        exact hxy
      rw [← iUnion_disjointed] at hx
      obtain ⟨n, hn⟩ := Set.mem_iUnion.1 hx
      have hnp : n < p := by
        by_contra h
        have := disjointed_subset f n hn
        simp [f, h] at this
      exact Set.mem_iUnion.2 ⟨⟨n, hnp⟩, hn⟩
    · have hsub : disjointed f i ⊆ Metric.ball ((e.symm i : X)) r := by
        refine (disjointed_subset f i).trans ?_
        simp [f, i.isLt]
      exact (Metric.diam_mono hsub Metric.isBounded_ball).trans (Metric.diam_ball hr.le)
  choose p P hP hdiam using fun j : ℕ ↦ key (1 / (j + 1)) (by positivity)
  refine ⟨p, P, hP, fun j i ↦ (hdiam j i).trans_eq ?_⟩
  ring

/-- Jacobs' theorem, lower half, on a compact metric space: the mean entropy of invariant
components is at most the entropy of the mixture. Blueprint node `erg:jacobs`. -/
theorem jacobs_lintegral_ksEntropy_le (ρ : Measure Ω) [IsProbabilityMeasure ρ]
    (κ : Kernel Ω X) [IsMarkovKernel κ] {T : X → X}
    (hinv : ∀ᵐ ω ∂ρ, MeasurePreserving T (κ ω) (κ ω)) :
    ∫⁻ ω, ksEntropy (κ ω) T ∂ρ ≤ ksEntropy (ρ.bind κ) T := by
  obtain ⟨ω₀, hω₀⟩ := hinv.exists
  have hT := hω₀.measurable
  obtain ⟨p, P, hP, hdiam⟩ := jacobs_exists_finePartitions (X := X)
  have hr : Tendsto (fun j : ℕ ↦ (2 : ℝ) / (j + 1)) atTop (𝓝 0) := by
    have h := (tendsto_const_div_atTop_nhds_zero_nat (2 : ℝ)).comp (tendsto_add_atTop_nat 1)
    refine h.congr fun j ↦ ?_
    simp
  have hlim : ∀ᵐ ω ∂ρ, Filter.liminf (fun j ↦ entropyRate (κ ω) T (P j)) atTop =
      ksEntropy (κ ω) T :=
    hinv.mono fun ω hω ↦ (tendsto_entropyRate_ksEntropy hω hP hr hdiam).liminf_eq
  calc ∫⁻ ω, ksEntropy (κ ω) T ∂ρ
      = ∫⁻ ω, Filter.liminf (fun j ↦ entropyRate (κ ω) T (P j)) atTop ∂ρ :=
        (lintegral_congr_ae (hlim.mono fun ω hω ↦ hω.symm))
    _ ≤ Filter.liminf (fun j ↦ ∫⁻ ω, entropyRate (κ ω) T (P j) ∂ρ) atTop :=
        lintegral_liminf_le fun j ↦ jacobs_measurable_entropyRate κ hT (hP j)
    _ ≤ Filter.liminf (fun _ : ℕ ↦ ksEntropy (ρ.bind κ) T) atTop :=
        liminf_le_liminf (Eventually.of_forall fun j ↦
          (jacobs_lintegral_entropyRate_le ρ κ T hT (hP j)).trans
            (entropyRate_le_ksEntropy _ T (hP j)))
    _ = ksEntropy (ρ.bind κ) T := liminf_const _

/-- On a compact metric space, the entropy `ω ↦ h_{κ ω}(T)` of the components of a kernel with
a.e. invariant values is almost everywhere measurable (an a.e. limit of entropy rates of fine
partitions). Blueprint node `erg:jacobs`. -/
theorem jacobs_aemeasurable_ksEntropy (ρ : Measure Ω) [IsProbabilityMeasure ρ]
    (κ : Kernel Ω X) [IsMarkovKernel κ] {T : X → X}
    (hinv : ∀ᵐ ω ∂ρ, MeasurePreserving T (κ ω) (κ ω)) :
    AEMeasurable (fun ω ↦ ksEntropy (κ ω) T) ρ := by
  obtain ⟨ω₀, hω₀⟩ := hinv.exists
  have hT := hω₀.measurable
  obtain ⟨p, P, hP, hdiam⟩ := jacobs_exists_finePartitions (X := X)
  have hr : Tendsto (fun j : ℕ ↦ (2 : ℝ) / (j + 1)) atTop (𝓝 0) := by
    have h := (tendsto_const_div_atTop_nhds_zero_nat (2 : ℝ)).comp (tendsto_add_atTop_nat 1)
    refine h.congr fun j ↦ ?_
    simp
  refine (Measurable.liminf fun j ↦ jacobs_measurable_entropyRate κ hT (hP j)).aemeasurable.congr
    (hinv.mono fun ω hω ↦ (tendsto_entropyRate_ksEntropy hω hP hr hdiam).liminf_eq)

/-- **Jacobs' theorem**: on a compact metric space, the Kolmogorov–Sinai entropy of a mixture
`ρ.bind κ` of invariant probability measures is the mean of the entropies of the components.
Blueprint node `erg:jacobs`. -/
theorem jacobs_ksEntropy_bind (ρ : Measure Ω) [IsProbabilityMeasure ρ] (κ : Kernel Ω X)
    [IsMarkovKernel κ] {T : X → X} (hinv : ∀ᵐ ω ∂ρ, MeasurePreserving T (κ ω) (κ ω)) :
    ksEntropy (ρ.bind κ) T = ∫⁻ ω, ksEntropy (κ ω) T ∂ρ :=
  le_antisymm (jacobs_ksEntropy_bind_le ρ κ hinv) (jacobs_lintegral_ksEntropy_le ρ κ hinv)

/-- Jacobs' theorem along the ergodic decomposition: for a continuous map of a compact metric
space and an invariant Borel probability measure `μ`, there is an ergodic decomposition
`μ = ∫ κ x dμ(x)` (`exists_ergodicDecomposition`) with `h_μ(T) = ∫ h_{κ x}(T) dμ(x)`.
Blueprint node `erg:jacobs`. -/
theorem jacobs_ksEntropy_eq_lintegral_ergodicDecomposition {T : X → X} (hT : Continuous T)
    (μ : Measure X) [IsProbabilityMeasure μ] (hμ : MeasurePreserving T μ μ) :
    ∃ κ : Kernel X X, IsMarkovKernel κ ∧ μ.bind κ = μ ∧ (∀ᵐ x ∂μ, Ergodic T (κ x)) ∧
      ksEntropy μ T = ∫⁻ x, ksEntropy (κ x) T ∂μ := by
  obtain ⟨κ, hκ, hbind, herg⟩ := exists_ergodicDecomposition hT μ hμ
  refine ⟨κ, hκ, hbind, herg, ?_⟩
  have h := jacobs_ksEntropy_bind μ κ (herg.mono fun _ h ↦ h.toMeasurePreserving)
  rwa [hbind] at h

end Compact

end Kolmogorov.Ergodic
