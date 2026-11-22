/-
Copyright (c) 2026 Emma Dinowitz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emma Dinowitz
-/
import KolmogorovMathlib.Ergodic.PartitionEntropy
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.MeasureTheory.Measure.Regular

/-!
# Partitions of small diameter compute the Kolmogorov–Sinai entropy

Walters, *An Introduction to Ergodic Theory*, Theorem 8.3: on a compact metric space, if the
diameters of finite Borel partitions `P_j` tend to `0`, then `h_μ(T, P_j) → h_μ(T)`. This is
input (I4) of the note *Orbit complexity of Martin-Löf random points equals entropy*.

* `exists_condEntropy_lt_of_diam_lt` (Walters, Lemma 8.5-type): for a finite measurable
  partition `Q` and `ε > 0` there is `δ > 0` such that `H_μ(Q | P) < ε` for every finite
  measurable partition `P` whose cells have diameter `< δ`. Proof: approximate the cells `Q_j`
  from inside by closed (hence compact) sets `K_j` (regularity); a cell of `P` of diameter below
  their mutual distance meets at most one `K_j`, so `P` refines the partition `R` whose cell `R_i`
  collects the cells of `P` labelled `i`; then `H_μ(Q | P) ≤ H_μ(Q | R)`, and every off-diagonal
  mass `μ(Q_j ∩ R_i)`, `i ≠ j`, is at most `μ(Q_j \ K_j)`, which is small.
* `tendsto_entropyRate_ksEntropy`: the sequence form of Walters, Theorem 8.3.
* `lt_entropyRate_of_diam_lt` (input (I4)): for every `H < h_μ(T)` there is `δ > 0` such that
  every finite measurable partition with cells of diameter `< δ` has `H < h_μ(T, P)`.
  Proof: `entropyRate_le_add_condEntropy` and the previous lemma.

Blueprint node `erg:fine-partitions`.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal

namespace Kolmogorov.Ergodic

variable {X : Type*} [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]

/-- The local entropy of a vector of masses is controlled by its entries off one index: for
nonnegative `a` with `∑ a ≤ 1` and any index `j₀`,
`∑_j (-a_j log₂ a_j) - (-r log₂ r) ≤ ∑_{j ≠ j₀} (-a_j log₂ a_j + a_j / ln 2)` where `r = ∑ a`. -/
private theorem sum_negMulLogb_sub_le {ι : Type*} [Fintype ι] [DecidableEq ι] (a : ι → ℝ)
    (ha : ∀ j, 0 ≤ a j) (hs : ∑ j, a j ≤ 1) (j₀ : ι) :
    ∑ j, -a j * Real.logb 2 (a j) - -(∑ j, a j) * Real.logb 2 (∑ j, a j) ≤
      ∑ j ∈ Finset.univ.erase j₀, (-a j * Real.logb 2 (a j) + a j / Real.log 2) := by
  set r := ∑ j, a j with hr
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hr0 : 0 ≤ r := Finset.sum_nonneg fun j _ ↦ ha j
  have hlogr : Real.logb 2 r ≤ 0 := Real.logb_nonpos one_lt_two hr0 hs
  have hrest : r = a j₀ + ∑ j ∈ Finset.univ.erase j₀, a j :=
    (Finset.add_sum_erase _ _ (Finset.mem_univ j₀)).symm
  have hsplit : ∑ j, -a j * Real.logb 2 (a j) - -r * Real.logb 2 r =
      (-a j₀ * Real.logb 2 (a j₀) + a j₀ * Real.logb 2 r) +
        ∑ j ∈ Finset.univ.erase j₀, (-a j * Real.logb 2 (a j) + a j * Real.logb 2 r) := by
    rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.add_sum_erase _ _ (Finset.mem_univ j₀)]
    rw [hrest]
    ring
  have hj₀ : -a j₀ * Real.logb 2 (a j₀) + a j₀ * Real.logb 2 r ≤
      (∑ j ∈ Finset.univ.erase j₀, a j) / Real.log 2 := by
    rcases (ha j₀).eq_or_lt with h0 | hpos
    · rw [← h0]
      simp only [neg_zero, zero_mul, add_zero]
      exact div_nonneg (Finset.sum_nonneg fun j _ ↦ ha j) hlog2.le
    · have hnn : 0 ≤ ∑ j ∈ Finset.univ.erase j₀, a j := Finset.sum_nonneg fun j _ ↦ ha j
      have hrpos : 0 < r := by rw [hrest]; linarith
      have hlog := Real.log_le_sub_one_of_pos (div_pos hrpos hpos)
      rw [Real.log_div hrpos.ne' hpos.ne'] at hlog
      simp only [Real.logb]
      rw [le_div_iff₀ hlog2]
      have : (-a j₀ * (Real.log (a j₀) / Real.log 2) + a j₀ * (Real.log r / Real.log 2)) *
          Real.log 2 = a j₀ * (Real.log r - Real.log (a j₀)) := by
        field_simp
        ring
      rw [this]
      calc a j₀ * (Real.log r - Real.log (a j₀)) ≤ a j₀ * (r / a j₀ - 1) :=
            mul_le_mul_of_nonneg_left hlog hpos.le
        _ = r - a j₀ := by field_simp
        _ = ∑ j ∈ Finset.univ.erase j₀, a j := by rw [hrest]; ring
  have hRHS : ∑ j ∈ Finset.univ.erase j₀, (-a j * Real.logb 2 (a j) + a j / Real.log 2) =
      ∑ j ∈ Finset.univ.erase j₀, -a j * Real.logb 2 (a j) +
        (∑ j ∈ Finset.univ.erase j₀, a j) / Real.log 2 := by
    rw [Finset.sum_add_distrib, Finset.sum_div]
  have hle : ∑ j ∈ Finset.univ.erase j₀, (-a j * Real.logb 2 (a j) + a j * Real.logb 2 r) ≤
      ∑ j ∈ Finset.univ.erase j₀, -a j * Real.logb 2 (a j) := by
    have hnp : ∑ j ∈ Finset.univ.erase j₀, a j * Real.logb 2 r ≤ 0 :=
      Finset.sum_nonpos fun j _ ↦ mul_nonpos_of_nonneg_of_nonpos (ha j) hlogr
    rw [Finset.sum_add_distrib]
    linarith
  rw [hsplit, hRHS]
  linarith

omit [MetricSpace X] [CompactSpace X] [BorelSpace X] in
/-- The mass of a measurable set is the sum of the masses of its traces on the cells of a
measurable partition. -/
private theorem measure_eq_sum_inter {ι : Type*} [Fintype ι] (μ : Measure X) {Q : ι → Set X}
    (hQ : IsMeasurablePartition Q) {B : Set X} (hB : MeasurableSet B) :
    μ B = ∑ j, μ (Q j ∩ B) := by
  have hU : B = ⋃ j, Q j ∩ B := by rw [← Set.iUnion_inter, hQ.iUnion_eq, Set.univ_inter]
  conv_lhs => rw [hU]
  rw [measure_iUnion, tsum_fintype]
  · exact fun j k hjk ↦ (hQ.disjoint hjk).mono Set.inter_subset_left Set.inter_subset_left
  · exact fun j ↦ (hQ.measurableSet j).inter hB

omit [MetricSpace X] [CompactSpace X] [BorelSpace X] in
/-- The conditional entropy `H_μ(Q | R)` as a sum over the cells of `R` of the "local"
entropies `∑_j φ(μ(Q_j ∩ R_i)) - φ(μ(R_i))`, `φ(t) = -t log₂ t`, for a measurable partition `Q`
and measurable cells `R_i`. -/
private theorem condEntropy_eq_sum {ι κ : Type*} [Fintype ι] [Fintype κ] (μ : Measure X)
    [IsFiniteMeasure μ] {Q : ι → Set X} {R : κ → Set X} (hQ : IsMeasurablePartition Q)
    (hR : ∀ i, MeasurableSet (R i)) :
    condEntropy μ Q R = ∑ i, (∑ j, -(μ (Q j ∩ R i)).toReal * Real.logb 2 (μ (Q j ∩ R i)).toReal
      - -(∑ j, (μ (Q j ∩ R i)).toReal) * Real.logb 2 (∑ j, (μ (Q j ∩ R i)).toReal)) := by
  unfold condEntropy partitionEntropy partitionJoin
  rw [Fintype.sum_prod_type_right, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [measure_eq_sum_inter μ hQ (hR i)]
  simp only [entropyTerm]
  rw [ENNReal.toReal_sum fun j _ ↦ measure_ne_top _ _]

/-- Partitions of small diameter almost determine a fixed partition: for every finite measurable
partition `Q` and `ε > 0` there is `δ > 0` with `H_μ(Q | P) < ε` whenever every cell of the finite
measurable partition `P` has diameter `< δ`. Blueprint node `erg:fine-partitions`. -/
theorem exists_condEntropy_lt_of_diam_lt (μ : Measure X) [IsProbabilityMeasure μ] {q : ℕ}
    {Q : Fin q → Set X} (hQ : IsMeasurablePartition Q) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ (p : ℕ) (P : Fin p → Set X), IsMeasurablePartition P →
      (∀ i, Metric.diam (P i) < δ) → condEntropy μ Q P < ε := by
  classical
  -- `X` is nonempty, hence so is the index type of `Q`
  obtain ⟨i₀⟩ : Nonempty (Fin q) := by
    have hX : (Set.univ : Set X).Nonempty := by
      by_contra h
      rw [Set.not_nonempty_iff_eq_empty] at h
      simpa [h] using measure_univ (μ := μ)
    obtain ⟨x, hx⟩ := hX
    rw [← hQ.iUnion_eq] at hx
    obtain ⟨i, -⟩ := Set.mem_iUnion.1 hx
    exact ⟨i⟩
  -- the bound on the small terms
  set c : ℝ := ε / (q * q + 1) with hc_def
  have hc : 0 < c := by positivity
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hg : ∀ᶠ t in 𝓝 (0 : ℝ), -t * Real.logb 2 t + t / Real.log 2 < c := by
    have heq : (fun t : ℝ ↦ -t * Real.logb 2 t + t / Real.log 2) =
        fun t ↦ Real.negMulLog t / Real.log 2 + t / Real.log 2 := by
      funext t
      simp only [Real.logb, Real.negMulLog]
      ring
    have hcont : Continuous fun t : ℝ ↦ Real.negMulLog t / Real.log 2 + t / Real.log 2 := by
      have := Real.continuous_negMulLog
      fun_prop
    have ht : Tendsto (fun t : ℝ ↦ -t * Real.logb 2 t + t / Real.log 2) (𝓝 0) (𝓝 0) := by
      rw [heq]
      simpa using hcont.tendsto 0
    exact ht.eventually (gt_mem_nhds hc)
  obtain ⟨η, hη, hηg⟩ := Metric.eventually_nhds_iff.1 hg
  -- inner approximation of the cells of `Q` by compact sets
  have hK : ∀ j, ∃ K, K ⊆ Q j ∧ IsClosed K ∧ μ (Q j \ K) < ENNReal.ofReal η := fun j ↦
    (hQ.measurableSet j).exists_isClosed_sdiff_lt (measure_ne_top _ _)
      (ENNReal.ofReal_pos.2 hη).ne'
  choose K hKQ hKc hKμ using hK
  -- the compact sets are at positive mutual distance
  have hsep : ∀ᶠ δ in 𝓝[>] (0 : ℝ), ∀ i j : Fin q, ∀ x ∈ K i, ∀ y ∈ K j, dist x y < δ → i = j := by
    refine Filter.eventually_all.2 fun i ↦ Filter.eventually_all.2 fun j ↦ ?_
    by_cases hij : i = j
    · exact Filter.Eventually.of_forall fun _ _ _ _ _ _ ↦ hij
    have hdisj : Disjoint (K i) (K j) := (hQ.disjoint hij).mono (hKQ i) (hKQ j)
    obtain ⟨δ₀, hδ₀, hd⟩ := hdisj.exists_thickenings (hKc i).isCompact (hKc j)
    filter_upwards [Ioo_mem_nhdsGT hδ₀] with δ hδ x hx y hy hxy
    exact (Set.disjoint_left.1 hd (Metric.self_subset_thickening hδ₀ _ hx)
      (Metric.mem_thickening_iff.2 ⟨y, hy, hxy.trans hδ.2⟩)).elim
  obtain ⟨δ, hδsep, hδpos⟩ := (hsep.and self_mem_nhdsWithin).exists
  refine ⟨δ, hδpos, fun p P hP hdiam ↦ ?_⟩
  -- a cell of `P` meets at most one of the compact sets
  have huniq : ∀ a i j, (P a ∩ K i).Nonempty → (P a ∩ K j).Nonempty → i = j := by
    rintro a i j ⟨x, hxP, hxK⟩ ⟨y, hyP, hyK⟩
    exact hδsep i j x hxK y hyK ((Metric.dist_le_diam_of_mem Metric.isBounded_of_compactSpace
      hxP hyP).trans_lt (hdiam a))
  let label : Fin p → Fin q := fun a ↦
    if h : ∃ i, (P a ∩ K i).Nonempty then h.choose else i₀
  have hlabel : ∀ a i, (P a ∩ K i).Nonempty → label a = i := by
    intro a i h
    have h' : ∃ i, (P a ∩ K i).Nonempty := ⟨i, h⟩
    simp only [label, h', ↓reduceDIte]
    exact huniq a _ _ h'.choose_spec h
  -- the coarser partition `R`
  let R : Fin q → Set X := fun i ↦ ⋃ (a : Fin p) (_ : label a = i), P a
  have hmemP : ∀ x, ∃ a, x ∈ P a := fun x ↦
    Set.mem_iUnion.1 (hP.iUnion_eq.symm ▸ Set.mem_univ x)
  have hR : IsMeasurablePartition R := by
    refine ⟨fun i ↦ MeasurableSet.iUnion fun a ↦ MeasurableSet.iUnion fun _ ↦
      hP.measurableSet a, ?_, ?_⟩
    · intro i j hij
      refine Set.disjoint_left.2 fun x hx hx' ↦ ?_
      simp only [R, Set.mem_iUnion] at hx hx'
      obtain ⟨a, ha, hxa⟩ := hx
      obtain ⟨b, hb, hxb⟩ := hx'
      have hab : a = b := by
        by_contra hab
        exact Set.disjoint_left.1 (hP.disjoint hab) hxa hxb
      subst hab
      exact hij (ha.symm.trans hb)
    · refine Set.eq_univ_of_forall fun x ↦ ?_
      obtain ⟨a, ha⟩ := hmemP x
      exact Set.mem_iUnion.2 ⟨label a, Set.mem_iUnion₂.2 ⟨a, rfl, ha⟩⟩
  have hPR : Refines P R := fun a ↦ ⟨label a, fun x hx ↦ Set.mem_iUnion₂.2 ⟨a, rfl, hx⟩⟩
  have hKR : ∀ j, K j ⊆ R j := by
    intro j x hx
    obtain ⟨a, ha⟩ := hmemP x
    exact Set.mem_iUnion₂.2 ⟨a, hlabel a j ⟨x, ha, hx⟩, ha⟩
  have hsmall : ∀ i j, j ≠ i → (μ (Q j ∩ R i)).toReal < η := by
    intro i j hji
    refine ENNReal.toReal_lt_of_lt_ofReal (lt_of_le_of_lt (measure_mono ?_) (hKμ j))
    rintro x ⟨hxQ, hxR⟩
    exact ⟨hxQ, fun hxK ↦ Set.disjoint_left.1 (hR.disjoint hji) (hKR j hxK) hxR⟩
  -- the estimate
  calc condEntropy μ Q P ≤ condEntropy μ Q R := condEntropy_le_of_refines μ hQ hP hR hPR
    _ = ∑ i, (∑ j, -(μ (Q j ∩ R i)).toReal * Real.logb 2 (μ (Q j ∩ R i)).toReal
          - -(∑ j, (μ (Q j ∩ R i)).toReal) * Real.logb 2 (∑ j, (μ (Q j ∩ R i)).toReal)) :=
        condEntropy_eq_sum μ hQ hR.measurableSet
    _ ≤ ∑ i, ∑ j ∈ Finset.univ.erase i, (-(μ (Q j ∩ R i)).toReal *
          Real.logb 2 (μ (Q j ∩ R i)).toReal + (μ (Q j ∩ R i)).toReal / Real.log 2) := by
        refine Finset.sum_le_sum fun i _ ↦ sum_negMulLogb_sub_le _ (fun j ↦ ENNReal.toReal_nonneg)
          ?_ i
        rw [← ENNReal.toReal_sum fun j _ ↦ measure_ne_top _ _]
        rw [← measure_eq_sum_inter μ hQ (hR.measurableSet i)]
        exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by
          rw [ENNReal.ofReal_one]
          exact prob_le_one)
    _ ≤ ∑ _i : Fin q, ∑ _j : Fin q, c := by
        refine Finset.sum_le_sum fun i _ ↦ ?_
        refine (Finset.sum_le_sum fun j hj ↦ (hηg ?_).le).trans
          (Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
            fun _ _ _ ↦ hc.le)
        rw [Real.dist_eq, sub_zero, abs_of_nonneg ENNReal.toReal_nonneg]
        exact hsmall i j (Finset.ne_of_mem_erase hj)
    _ = q * q * c := by simp [mul_assoc]
    _ < ε := by
        rw [hc_def, ← mul_div_assoc, div_lt_iff₀ (by positivity)]
        nlinarith

/-- Input (I4) of the note (Walters, Theorem 8.3): for every `H < h_μ(T)` there is `δ > 0` such
that every finite measurable partition whose cells have diameter `< δ` has entropy rate `> H`.
Blueprint node `erg:fine-partitions`. -/
theorem lt_entropyRate_of_diam_lt {μ : Measure X} [IsProbabilityMeasure μ] {T : X → X}
    (hT : MeasurePreserving T μ μ) {H : ℝ≥0∞} (hH : H < ksEntropy μ T) :
    ∃ δ > 0, ∀ (p : ℕ) (P : Fin p → Set X), IsMeasurablePartition P →
      (∀ i, Metric.diam (P i) < δ) → H < entropyRate μ T P := by
  obtain ⟨q, hq⟩ := lt_iSup_iff.1 hH
  obtain ⟨Q, hQ⟩ := lt_iSup_iff.1 hq
  obtain ⟨hQp, hHQ⟩ := lt_iSup_iff.1 hQ
  have hfin : entropyRate μ T Q ≠ ∞ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (entropyRate_le_logb_card μ hT.measurable hQp)
  have hHfin : H ≠ ∞ := ne_top_of_lt hHQ
  set ε := (entropyRate μ T Q).toReal - H.toReal with hε_def
  have hε : 0 < ε := sub_pos.2 ((ENNReal.toReal_lt_toReal hHfin hfin).2 hHQ)
  have hsum : H + ENNReal.ofReal ε = entropyRate μ T Q := by
    rw [ENNReal.ofReal_sub _ ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hfin,
      ENNReal.ofReal_toReal hHfin]
    exact add_tsub_cancel_of_le hHQ.le
  obtain ⟨δ, hδ, hδP⟩ := exists_condEntropy_lt_of_diam_lt μ hQp hε
  refine ⟨δ, hδ, fun p P hP hdiam ↦ ?_⟩
  refine lt_of_not_ge fun hle ↦ ?_
  have hcond := hδP p P hP hdiam
  have h1 := entropyRate_le_add_condEntropy hT hQp hP
  have h2 : entropyRate μ T P + ENNReal.ofReal (condEntropy μ Q P) < H + ENNReal.ofReal ε :=
    calc entropyRate μ T P + ENNReal.ofReal (condEntropy μ Q P)
        ≤ H + ENNReal.ofReal (condEntropy μ Q P) := add_le_add_left hle _
      _ < H + ENNReal.ofReal ε :=
        ENNReal.add_lt_add_left hHfin ((ENNReal.ofReal_lt_ofReal_iff hε).2 hcond)
  rw [hsum] at h2
  exact (h1.trans_lt h2).false

/-- Walters, Theorem 8.3, sequence form: if the cells of the finite measurable partitions `P j`
have diameters tending to `0` uniformly, then `h_μ(T, P j) → h_μ(T)`.
Blueprint node `erg:fine-partitions`. -/
theorem tendsto_entropyRate_ksEntropy {μ : Measure X} [IsProbabilityMeasure μ] {T : X → X}
    (hT : MeasurePreserving T μ μ) {p : ℕ → ℕ} {P : (j : ℕ) → Fin (p j) → Set X}
    (hP : ∀ j, IsMeasurablePartition (P j)) {r : ℕ → ℝ} (hr : Tendsto r atTop (𝓝 0))
    (hdiam : ∀ j i, Metric.diam (P j i) ≤ r j) :
    Tendsto (fun j ↦ entropyRate μ T (P j)) atTop (𝓝 (ksEntropy μ T)) := by
  refine tendsto_order.2 ⟨fun H hH ↦ ?_, fun H hH ↦ ?_⟩
  · obtain ⟨δ, hδ, hδP⟩ := lt_entropyRate_of_diam_lt hT hH
    filter_upwards [hr.eventually (gt_mem_nhds hδ)] with j hj
    exact hδP (p j) (P j) (hP j) fun i ↦ (hdiam j i).trans_lt hj
  · exact Filter.Eventually.of_forall fun j ↦
      (entropyRate_le_ksEntropy μ T (hP j)).trans_lt hH

end Kolmogorov.Ergodic
