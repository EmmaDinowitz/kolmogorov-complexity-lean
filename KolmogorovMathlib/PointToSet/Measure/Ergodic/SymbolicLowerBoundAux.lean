/-
Copyright (c) 2026 Emma Dinowitz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emma Dinowitz
-/
import KolmogorovMathlib.PointToSet.Measure.Ergodic.WordRandomness
import KolmogorovMathlib.Ergodic.PartitionEntropy
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog


/-!
# Binary suffices in (I3): the coded measure and its entropy

Auxiliary material for `SymbolicLowerBound` (the reduction "Binary suffices in (I3)" of the note
*Orbit complexity of Martin-Löf random points equals entropy*). For a measure `ν` on `ℕ → Fin p`
(`p ≥ 1`) we use the one-hot block code `C = blockCode p : (ℕ → Fin p) → (ℕ → Bool)`, bit `n`
of `C ω` being `[ω (n / p) = n % p]` (blocks of `b = p` bits; any injective code works, and the
one-hot code needs no binary digits). Then

* `blockPush ν = ν' = C_* ν`, invariant under `σ^p` (`blockPush_map_iterate`), and
  `blockAvg ν = ν'' = (1/p) ∑_{j<p} σ^j_* ν'` (`blockAvg_apply`);
* `ν''` is a shift-invariant (`blockAvg_map_shift`) ergodic (`ergodic_blockAvg`) probability
  measure, and `ν(C⁻¹ s) ≤ p ν''(s)` (`blockPush_le_blockAvg`);
* `shiftEntropy_le_mul_blockAvg`: `h_ν(σ) ≤ p · h_{ν''}(σ)`. Concavity of `-x log x` gives
  `H_{ν''}(ξ^N) ≥ (1/p) ∑_j H_{σ^j_* ν'}(ξ^N)` (`blockEntropy_average_ge`); subadditivity of the
  partition entropy gives `H_{σ^j_* ν'}(ξ^N) ≥ H_{ν'}(ξ^{j+N}) - H_{ν'}(ξ^j)`
  (`blockEntropy_add_le`), and `H_{ν'}(ξ^{pk}) = H_ν(ξ^k)` (`blockEntropy_blockPush`); since
  `shiftEntropy` is an infimum, the bound is passed to every `k` through the subadditivity of
  `N ↦ H_{ν''}(ξ^N)` for the invariant `ν''` (`blockEntropy_mul_le`).

The generic facts on the block entropy use the partition entropy of
`KolmogorovMathlib.Ergodic.PartitionEntropy` (`partitionEntropy_join_le`, `condEntropy_nonneg`).
Blueprint node `erg:symbolic-lower`.
-/

namespace Kolmogorov.PointToSet.SymbolicLower

open Filter Set MeasureTheory Kolmogorov.Ergodic
open scoped ENNReal

section generic

variable {β : Type*}

/-- The window cylinder `{y | y (j + i) = v i, i < k}` (`= σ^{-j} [v]`). -/
def winCyl (j k : ℕ) (v : Fin k → β) : Set (ℕ → β) :=
  {y | ∀ i : Fin k, y (j + i) = v i}

/-- The iterates of the shift: `σ^j x = (x (i + j))_i`. -/
lemma iterate_shift (x : ℕ → β) (j : ℕ) : shiftMap^[j] x = fun i ↦ x (i + j) :=
  iterate_shiftMap x j

/-- Cylinders are window cylinders at `0`. -/
lemma wordCylinder_eq_winCyl {k : ℕ} (v : Fin k → β) : wordCylinder v = winCyl 0 k v := by
  ext y; simp [wordCylinder, winCyl]

/-- The cylinder of a concatenation. -/
lemma wordCylinder_append {j k : ℕ} (u : Fin j → β) (v : Fin k → β) :
    wordCylinder (Fin.append u v) = wordCylinder u ∩ winCyl j k v := by
  ext y
  simp only [wordCylinder, winCyl, mem_ofPred_eq, mem_inter_iff]
  rw [Fin.forall_fin_add]
  simp [Fin.append_left, Fin.append_right]

/-- The pull-back of a cylinder under `σ^j` is the window cylinder at `j`. -/
lemma preimage_iterate_wordCylinder (j k : ℕ) (v : Fin k → β) :
    shiftMap^[j] ⁻¹' wordCylinder v = winCyl j k v := by
  ext y
  simp only [mem_preimage, wordCylinder, winCyl, mem_ofPred_eq, iterate_shift, add_comm]

variable [MeasurableSpace β] [MeasurableSingletonClass β]

omit [MeasurableSingletonClass β] in
/-- The shift is measurable. -/
lemma measurable_shift : Measurable (shiftMap : (ℕ → β) → ℕ → β) :=
  Measurable.of_eval fun i ↦ measurable_pi_apply (i + 1)

/-- Window cylinders are measurable. -/
lemma measurableSet_winCyl (j k : ℕ) (v : Fin k → β) : MeasurableSet (winCyl j k v) := by
  have : winCyl j k v = ⋂ i : Fin k, (fun y : ℕ → β ↦ y (j + i)) ⁻¹' {v i} := by
    ext y; simp [winCyl]
  rw [this]
  exact MeasurableSet.iInter fun i ↦ measurable_pi_apply _ (measurableSet_singleton _)

/-- Cylinders are measurable. -/
lemma measurableSet_wordCylinder' {k : ℕ} (v : Fin k → β) : MeasurableSet (wordCylinder v) := by
  rw [wordCylinder_eq_winCyl]; exact measurableSet_winCyl 0 k v

/-- The window cylinders of a fixed position and length form a measurable partition. -/
lemma isMeasurablePartition_winCyl (j k : ℕ) :
    IsMeasurablePartition (winCyl (β := β) j k) where
  measurableSet := measurableSet_winCyl j k
  disjoint := by
    intro v w hvw
    refine Set.disjoint_left.2 fun y hv hw ↦ hvw ?_
    funext i
    rw [← hv i, ← hw i]
  iUnion_eq := by
    refine Set.eq_univ_of_forall fun y ↦ Set.mem_iUnion.2 ⟨fun i ↦ y (j + i), fun i ↦ rfl⟩

/-- Cylinders form a measurable partition. -/
lemma isMeasurablePartition_wordCylinder (k : ℕ) :
    IsMeasurablePartition (wordCylinder (α := β) (k := k)) := by
  have : (wordCylinder (α := β) (k := k)) = winCyl 0 k := funext wordCylinder_eq_winCyl
  rw [this]; exact isMeasurablePartition_winCyl 0 k

omit [MeasurableSingletonClass β] in
/-- An invariant measure is invariant under the iterates. -/
lemma map_iterate_of_map_eq {μ : Measure (ℕ → β)} (h : μ.map shiftMap = μ) (j : ℕ) :
    μ.map shiftMap^[j] = μ := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Function.iterate_succ, ← Measure.map_map (measurable_shift.iterate j) measurable_shift, h,
      ih]

variable [Fintype β]

omit [MeasurableSingletonClass β] in
/-- `blockEntropy` is the partition entropy of the cylinder partition. -/
lemma blockEntropy_eq_partitionEntropy (μ : Measure (ℕ → β)) (k : ℕ) :
    blockEntropy μ k = partitionEntropy μ (wordCylinder (α := β) (k := k)) := rfl

/-- The entropy of the window partition at `j` is the block entropy of `σ^j_* μ`. -/
lemma partitionEntropy_winCyl (μ : Measure (ℕ → β)) (j k : ℕ) :
    partitionEntropy μ (winCyl (β := β) j k) = blockEntropy (μ.map shiftMap^[j]) k := by
  simp only [blockEntropy, partitionEntropy, entropyTerm]
  refine Finset.sum_congr rfl fun v _ ↦ ?_
  rw [Measure.map_apply (measurable_shift.iterate j) (measurableSet_wordCylinder' v),
    preimage_iterate_wordCylinder]

omit [MeasurableSingletonClass β] in
/-- `H(ξ^{j+k})` as the entropy of the join of `ξ^j` and the window partition at `j`. -/
lemma blockEntropy_add_eq_join (μ : Measure (ℕ → β)) (j k : ℕ) :
    blockEntropy μ (j + k) =
      partitionEntropy μ (partitionJoin (wordCylinder (α := β) (k := j)) (winCyl j k)) := by
  simp only [blockEntropy, partitionEntropy, partitionJoin]
  refine (Fintype.sum_equiv (Fin.appendEquiv j k) _ _ fun x ↦ ?_).symm
  change _ = entropyTerm (μ (wordCylinder (Fin.append x.1 x.2)))
  rw [wordCylinder_append]

/-- `H(ξ^{j+k}) ≤ H(ξ^j) + H(σ^{-j} ξ^k)`. -/
lemma blockEntropy_add_le (μ : Measure (ℕ → β)) [IsProbabilityMeasure μ] (j k : ℕ) :
    blockEntropy μ (j + k) ≤ blockEntropy μ j + partitionEntropy μ (winCyl (β := β) j k) := by
  rw [blockEntropy_add_eq_join]
  exact partitionEntropy_join_le μ (isMeasurablePartition_wordCylinder j)
    (isMeasurablePartition_winCyl j k)

/-- `H(ξ^j) ≤ H(ξ^{j+k})`. -/
lemma blockEntropy_le_add (μ : Measure (ℕ → β)) [IsProbabilityMeasure μ] (j k : ℕ) :
    blockEntropy μ j ≤ blockEntropy μ (j + k) := by
  have h := condEntropy_nonneg μ (isMeasurablePartition_winCyl (β := β) j k)
    (isMeasurablePartition_wordCylinder j)
  have he : partitionEntropy μ (partitionJoin (winCyl (β := β) j k) (wordCylinder (k := j))) =
      blockEntropy μ (j + k) := by
    rw [blockEntropy_add_eq_join]
    simp only [partitionEntropy, partitionJoin]
    exact Fintype.sum_equiv (Equiv.prodComm _ _) _ _ fun x ↦ by simp [Set.inter_comm]
  simp only [condEntropy, he] at h
  rw [blockEntropy_eq_partitionEntropy]
  linarith

/-- `k ↦ H(ξ^k)` is monotone. -/
lemma blockEntropy_mono (μ : Measure (ℕ → β)) [IsProbabilityMeasure μ] {m n : ℕ} (h : m ≤ n) :
    blockEntropy μ m ≤ blockEntropy μ n := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  exact blockEntropy_le_add μ m k

/-- Subadditivity of the block entropy of an invariant measure. -/
lemma blockEntropy_add_le_of_inv {μ : Measure (ℕ → β)} [IsProbabilityMeasure μ]
    (h : μ.map shiftMap = μ) (j k : ℕ) :
    blockEntropy μ (j + k) ≤ blockEntropy μ j + blockEntropy μ k := by
  have := blockEntropy_add_le μ j k
  rwa [partitionEntropy_winCyl, map_iterate_of_map_eq h] at this

/-- `H(ξ^{nk}) ≤ n H(ξ^k)` for an invariant measure. -/
lemma blockEntropy_mul_le {μ : Measure (ℕ → β)} [IsProbabilityMeasure μ]
    (h : μ.map shiftMap = μ) (n k : ℕ) :
    blockEntropy μ (n * k) ≤ n * blockEntropy μ k := by
  induction n with
  | zero =>
    simp only [zero_mul, CharP.cast_eq_zero]
    simp [blockEntropy, wordCylinder]
  | succ n ih =>
    rw [Nat.succ_mul]
    push_cast
    linarith [blockEntropy_add_le_of_inv h (n * k) k]

/-- The entropy term through `negMulLog`. -/
lemma entropyTerm_eq_negMulLog (q : ℝ≥0∞) :
    entropyTerm q = Real.negMulLog q.toReal / Real.log 2 := by
  simp only [entropyTerm, Real.negMulLog, Real.logb]
  ring

omit [MeasurableSingletonClass β] in
/-- Concavity of the block entropy: the entropy of an average of finite measures is at least the
average of the entropies. -/
lemma blockEntropy_average_ge (μs : ℕ → Measure (ℕ → β)) [∀ j, IsFiniteMeasure (μs j)] {b : ℕ}
    (hb : 0 < b) (k : ℕ) :
    (b : ℝ)⁻¹ * ∑ j ∈ Finset.range b, blockEntropy (μs j) k ≤
      blockEntropy ((b : ℝ≥0∞)⁻¹ • ∑ j ∈ Finset.range b, μs j) k := by
  simp only [blockEntropy, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_le_sum fun w _ ↦ ?_
  have hterm : ∀ q : ℝ≥0∞, -q.toReal * Real.logb 2 q.toReal = entropyTerm q := fun _ ↦ rfl
  simp only [hterm, entropyTerm_eq_negMulLog]
  have hval : (((b : ℝ≥0∞)⁻¹ • ∑ j ∈ Finset.range b, μs j) (wordCylinder w)).toReal =
      ∑ j ∈ Finset.range b, (b : ℝ)⁻¹ • ((μs j) (wordCylinder w)).toReal := by
    rw [Measure.smul_apply, Measure.coe_finsetSum, Finset.sum_apply, smul_eq_mul,
      ENNReal.toReal_mul, ENNReal.toReal_sum fun j _ ↦ measure_ne_top _ _, Finset.mul_sum]
    simp
  rw [hval]
  have hlog : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hJ := Real.concaveOn_negMulLog.le_map_sum (t := Finset.range b)
    (w := fun _ ↦ (b : ℝ)⁻¹) (p := fun j ↦ ((μs j) (wordCylinder w)).toReal)
    (fun _ _ ↦ by positivity) (by simp [hb.ne']) (fun _ _ ↦ Set.mem_Ici.2 ENNReal.toReal_nonneg)
  simp only [smul_eq_mul] at hJ ⊢
  calc ∑ j ∈ Finset.range b, (b : ℝ)⁻¹ * (Real.negMulLog ((μs j) (wordCylinder w)).toReal /
        Real.log 2)
      = (∑ j ∈ Finset.range b, (b : ℝ)⁻¹ * Real.negMulLog ((μs j) (wordCylinder w)).toReal) /
        Real.log 2 := by rw [Finset.sum_div]; simp [mul_div_assoc]
    _ ≤ _ := div_le_div_of_nonneg_right hJ hlog.le

end generic

/-! ### The one-hot block code and the averaged measure -/

section code

variable {p : ℕ}

/-- The one-hot block code `C : (ℕ → Fin p) → (ℕ → Bool)`: bit `n` of `C ω` says whether the
symbol `ω (n / p)` equals `n % p`; each symbol becomes a block of `p` bits. -/
def blockCode (p : ℕ) (ω : ℕ → Fin p) : ℕ → Bool :=
  fun n ↦ decide ((ω (n / p) : ℕ) = n % p)

/-- `C` conjugates `σ` to `σ^p`. -/
lemma blockCode_shiftMap (hp : 0 < p) (ω : ℕ → Fin p) :
    blockCode p (shiftMap ω) = shiftMap^[p] (blockCode p ω) := by
  funext n
  rw [iterate_shift]
  simp only [blockCode, shiftMap, Nat.add_div_right n hp, Nat.add_mod_right]
  rfl

/-- The block code is measurable. -/
lemma measurable_blockCode : Measurable (blockCode p) :=
  Measurable.of_eval fun n ↦
    (measurable_from_top (f := fun a : Fin p ↦ decide ((a : ℕ) = n % p))).comp
      (measurable_pi_apply (n / p))

/-- The push-forward `ν' = C_* ν` of a measure on `ℕ → Fin p` to the binary shift. -/
noncomputable def blockPush (ν : Measure (ℕ → Fin p)) : Measure (ℕ → Bool) :=
  ν.map (blockCode p)

/-- The averaged measure `ν'' = (1/p) ∑_{j<p} σ^j_* ν'`. -/
noncomputable def blockAvg (ν : Measure (ℕ → Fin p)) : Measure (ℕ → Bool) :=
  (p : ℝ≥0∞)⁻¹ • ∑ j ∈ Finset.range p, (blockPush ν).map shiftMap^[j]

/-- Reindexing a cyclic sum: if `g p = g 0` then `∑_{j<p} g (j+1) = ∑_{j<p} g j`. -/
lemma sum_range_succ_eq_of_cyclic (g : ℕ → ℝ≥0∞) {p : ℕ} (hp : 0 < p) (h : g p = g 0) :
    ∑ j ∈ Finset.range p, g (j + 1) = ∑ j ∈ Finset.range p, g j := by
  obtain ⟨q, rfl⟩ := Nat.exists_eq_add_of_lt hp
  rw [zero_add] at h ⊢
  rw [Finset.sum_range_succ, h, Finset.sum_range_succ' g]

/-- `ν'(s) = ν(C⁻¹ s)`. -/
lemma blockPush_apply (ν : Measure (ℕ → Fin p)) {s : Set (ℕ → Bool)} (hs : MeasurableSet s) :
    blockPush ν s = ν (blockCode p ⁻¹' s) :=
  Measure.map_apply measurable_blockCode hs

/-- `ν''(s) = (1/p) ∑_{j<p} ν(C⁻¹ σ^{-j} s)`. -/
lemma blockAvg_apply (ν : Measure (ℕ → Fin p)) {s : Set (ℕ → Bool)} (hs : MeasurableSet s) :
    blockAvg ν s = (p : ℝ≥0∞)⁻¹ *
      ∑ j ∈ Finset.range p, ν (blockCode p ⁻¹' (shiftMap^[j] ⁻¹' s)) := by
  rw [blockAvg, Measure.smul_apply, Measure.coe_finsetSum, Finset.sum_apply, smul_eq_mul]
  congr 1
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [Measure.map_apply (measurable_shift.iterate j) hs,
    blockPush_apply ν (measurable_shift.iterate j hs)]

/-- `ν'` is a probability measure. -/
instance (ν : Measure (ℕ → Fin p)) [IsProbabilityMeasure ν] :
    IsProbabilityMeasure (blockPush ν) := by
  rw [blockPush]; infer_instance

/-- `ν'` is invariant under `σ^p`. -/
lemma blockPush_map_iterate {ν : Measure (ℕ → Fin p)} (hp : 0 < p) (hν : ν.map shiftMap = ν) :
    (blockPush ν).map shiftMap^[p] = blockPush ν := by
  rw [blockPush, Measure.map_map (measurable_shift.iterate p) measurable_blockCode]
  have : shiftMap^[p] ∘ blockCode p = blockCode p ∘ shiftMap := by
    funext ω; simp [blockCode_shiftMap hp]
  rw [this, ← Measure.map_map measurable_blockCode measurable_shift, hν]

/-- `ν''` is a probability measure. -/
lemma isProbabilityMeasure_blockAvg (ν : Measure (ℕ → Fin p)) [IsProbabilityMeasure ν]
    (hp : 0 < p) : IsProbabilityMeasure (blockAvg ν) := by
  constructor
  rw [blockAvg_apply ν MeasurableSet.univ]
  simp only [preimage_univ, measure_univ, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
    mul_one]
  exact ENNReal.inv_mul_cancel (by exact_mod_cast hp.ne') (ENNReal.natCast_ne_top p)

/-- `ν''` is shift-invariant. -/
lemma blockAvg_map_shift {ν : Measure (ℕ → Fin p)} (hp : 0 < p) (hν : ν.map shiftMap = ν) :
    (blockAvg ν).map shiftMap = blockAvg ν := by
  ext s hs
  rw [Measure.map_apply measurable_shift hs, blockAvg_apply ν (measurable_shift hs),
    blockAvg_apply ν hs]
  congr 1
  have hpre : ∀ j, shiftMap^[j] ⁻¹' (shiftMap ⁻¹' s) = shiftMap^[j + 1] ⁻¹' s := by
    intro j
    rw [Function.iterate_succ', Set.preimage_comp]
  simp only [hpre]
  have hlast : ν (blockCode p ⁻¹' (shiftMap^[p] ⁻¹' s)) =
      ν (blockCode p ⁻¹' (shiftMap^[0] ⁻¹' s)) := by
    have h : ((blockPush ν).map shiftMap^[p]) s = blockPush ν s := by
      rw [blockPush_map_iterate hp hν]
    rw [Measure.map_apply (measurable_shift.iterate p) hs, blockPush_apply ν hs,
      blockPush_apply ν (measurable_shift.iterate p hs)] at h
    simpa using h
  exact sum_range_succ_eq_of_cyclic (fun j ↦ ν (blockCode p ⁻¹' (shiftMap^[j] ⁻¹' s))) hp hlast

/-- `ν'' ` is ergodic. -/
lemma ergodic_blockAvg {ν : Measure (ℕ → Fin p)} [IsProbabilityMeasure ν] (hp : 0 < p)
    (hν : Ergodic shiftMap ν) : Ergodic shiftMap (blockAvg ν) := by
  refine Ergodic.of_preimage_eq ⟨measurable_shift, blockAvg_map_shift hp hν.map_eq⟩ ?_
  intro s hs hinv
  have hiter : ∀ j, shiftMap^[j] ⁻¹' s = s := by
    intro j
    induction j with
    | zero => rfl
    | succ j ih => rw [Function.iterate_succ', Set.preimage_comp, hinv, ih]
  have hval : ∀ t : Set (ℕ → Bool), MeasurableSet t → (∀ j, shiftMap^[j] ⁻¹' t = t) →
      blockAvg ν t = ν (blockCode p ⁻¹' t) := by
    intro t ht htj
    rw [blockAvg_apply ν ht]
    simp only [htj, Finset.sum_const, Finset.card_range, nsmul_eq_mul, ← mul_assoc]
    rw [ENNReal.inv_mul_cancel (by exact_mod_cast hp.ne') (ENNReal.natCast_ne_top p), one_mul]
  have hCinv : shiftMap ⁻¹' (blockCode p ⁻¹' s) = blockCode p ⁻¹' s := by
    rw [← Set.preimage_comp]
    have : blockCode p ∘ shiftMap = shiftMap^[p] ∘ blockCode p := by
      funext ω; simp [blockCode_shiftMap hp]
    rw [this, Set.preimage_comp, hiter]
  have hmeas : MeasurableSet (blockCode p ⁻¹' s) := measurable_blockCode hs
  rcases hν.measure_self_or_compl_eq_zero hmeas.nullMeasurableSet (by rw [hCinv]) with h | h
  · refine eventuallyEmptyOrUniv_iff'.2 (Or.inl ?_)
    rw [ae_eq_empty, hval s hs hiter, h]
  · refine eventuallyEmptyOrUniv_iff'.2 (Or.inr ?_)
    rw [ae_eq_univ, hval sᶜ hs.compl (fun j ↦ by rw [Set.preimage_compl, hiter]),
      Set.preimage_compl, h]

/-- `ν' ≤ p ν''` on measurable sets. -/
lemma blockPush_le_blockAvg (ν : Measure (ℕ → Fin p)) (hp : 0 < p) {s : Set (ℕ → Bool)}
    (hs : MeasurableSet s) : ν (blockCode p ⁻¹' s) ≤ p * blockAvg ν s := by
  rw [blockAvg_apply ν hs, ← mul_assoc,
    ENNReal.mul_inv_cancel (by exact_mod_cast hp.ne') (ENNReal.natCast_ne_top p), one_mul]
  exact Finset.single_le_sum (f := fun j ↦ ν (blockCode p ⁻¹' (shiftMap^[j] ⁻¹' s)))
    (fun _ _ ↦ zero_le) (Finset.mem_range.2 hp)

/-- The block code on words of length `k`. -/
def blockWord {k : ℕ} (u : Fin k → Fin p) : Fin (p * k) → Bool :=
  fun n ↦ decide (((u ⟨n / p, Nat.div_lt_of_lt_mul n.2⟩ : Fin p) : ℕ) = n % p)

/-- The position of bit `u i` in block `i`. -/
private lemma blockPos_lt {k : ℕ} (i : Fin k) (a : Fin p) : p * i + a < p * k := by
  have h1 : (i : ℕ) + 1 ≤ k := i.2
  have h2 : p * ((i : ℕ) + 1) ≤ p * k := Nat.mul_le_mul_left p h1
  have h3 : (a : ℕ) < p := a.2
  rw [Nat.mul_succ] at h2
  omega

/-- Division and remainder at the position of bit `a` in block `i`. -/
private lemma blockPos_div_mod (i a : ℕ) (ha : a < p) :
    (p * i + a) / p = i ∧ (p * i + a) % p = a := by
  have hp : 0 < p := lt_of_le_of_lt (Nat.zero_le a) ha
  refine ⟨?_, ?_⟩
  · rw [Nat.mul_add_div hp, Nat.div_eq_of_lt ha, add_zero]
  · rw [Nat.mul_add_mod, Nat.mod_eq_of_lt ha]

/-- The cylinder of a coded word pulls back to the cylinder of the word. -/
lemma preimage_blockCode_blockWord {k : ℕ} (u : Fin k → Fin p) :
    blockCode p ⁻¹' wordCylinder (blockWord u) = wordCylinder u := by
  ext ω
  simp only [mem_preimage, wordCylinder, mem_ofPred_eq, blockCode, blockWord]
  constructor
  · intro h i
    have hpos := blockPos_lt i (u i)
    obtain ⟨hd, hm⟩ := blockPos_div_mod i (u i) (u i).2
    have := h ⟨p * i + u i, hpos⟩
    simp only [hd, hm] at this
    have h' : ((ω i : Fin p) : ℕ) = u i := by simpa using this
    exact Fin.ext h'
  · intro h n
    rw [h ⟨n / p, Nat.div_lt_of_lt_mul n.2⟩]

/-- A binary word whose cylinder meets the image of `C` is a coded word. -/
lemma mem_range_blockWord_of_mem {k : ℕ} {v : Fin (p * k) → Bool} {ω : ℕ → Fin p}
    (h : ω ∈ blockCode p ⁻¹' wordCylinder v) : v ∈ Set.range (blockWord (k := k)) := by
  refine ⟨fun i ↦ ω i, funext fun n ↦ ?_⟩
  rw [← h n]
  rfl

/-- The block code on words is injective. -/
lemma blockWord_injective {k : ℕ} : Function.Injective (blockWord (p := p) (k := k)) := by
  intro u u' h
  funext i
  have hpos := blockPos_lt i (u i)
  obtain ⟨hd, hm⟩ := blockPos_div_mod i (u i) (u i).2
  have := congrFun h ⟨p * i + u i, hpos⟩
  simp only [blockWord, hd, hm] at this
  exact (Fin.ext (by simpa using this.symm)).symm

/-- `H_{ν'}(ξ^{pk}) = H_ν(ξ^k)`. -/
lemma blockEntropy_blockPush (ν : Measure (ℕ → Fin p)) (k : ℕ) :
    blockEntropy (blockPush ν) (p * k) = blockEntropy ν k := by
  refine (Fintype.sum_of_injective blockWord blockWord_injective _ _ (fun v hv ↦ ?_)
    fun u ↦ ?_).symm
  · have : blockPush ν (wordCylinder v) = 0 := by
      rw [blockPush_apply ν (measurableSet_wordCylinder' v)]
      have he : blockCode p ⁻¹' wordCylinder v = ∅ :=
        Set.eq_empty_of_forall_notMem fun ω hω ↦ hv (mem_range_blockWord_of_mem hω)
      rw [he, measure_empty]
    simp [this]
  · rw [blockPush_apply ν (measurableSet_wordCylinder' _), preimage_blockCode_blockWord]

/-- The entropy estimate behind `h_{ν''}(σ) ≥ h_ν(σ) / p`:
`H_{ν''}(ξ^N) ≥ H_ν(ξ^{⌊N/p⌋}) - c` with `c` independent of `N`. -/
lemma blockEntropy_blockAvg_ge (ν : Measure (ℕ → Fin p)) [IsProbabilityMeasure ν] (hp : 0 < p)
    (N : ℕ) :
    blockEntropy ν (N / p) -
        (p : ℝ)⁻¹ * ∑ j ∈ Finset.range p, blockEntropy (blockPush ν) j ≤
      blockEntropy (blockAvg ν) N := by
  have h1 := blockEntropy_average_ge (fun j ↦ (blockPush ν).map shiftMap^[j]) hp N
  have h2 : ∀ j, blockEntropy ν (N / p) - blockEntropy (blockPush ν) j ≤
      blockEntropy ((blockPush ν).map shiftMap^[j]) N := by
    intro j
    rw [← partitionEntropy_winCyl]
    have h3 := blockEntropy_add_le (blockPush ν) j N
    have h4 := blockEntropy_mono (blockPush ν) (show p * (N / p) ≤ j + N from
      (Nat.mul_div_le N p).trans (Nat.le_add_left N j))
    rw [blockEntropy_blockPush] at h4
    linarith
  have hp' : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne'
  calc blockEntropy ν (N / p) - (p : ℝ)⁻¹ * ∑ j ∈ Finset.range p, blockEntropy (blockPush ν) j
      = (p : ℝ)⁻¹ * ∑ j ∈ Finset.range p,
          (blockEntropy ν (N / p) - blockEntropy (blockPush ν) j) := by
        rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_sub,
          ← mul_assoc, inv_mul_cancel₀ hp', one_mul]
    _ ≤ (p : ℝ)⁻¹ * ∑ j ∈ Finset.range p, blockEntropy ((blockPush ν).map shiftMap^[j]) N := by
        gcongr with j
        exact h2 j
    _ ≤ blockEntropy (blockAvg ν) N := h1

/-- `h_ν(σ) ≤ p · h_{ν''}(σ)`. -/
lemma shiftEntropy_le_mul_blockAvg (ν : Measure (ℕ → Fin p)) [IsProbabilityMeasure ν]
    (hp : 0 < p) (hν : ν.map shiftMap = ν) :
    shiftEntropy ν ≤ p * shiftEntropy (blockAvg ν) := by
  have := isProbabilityMeasure_blockAvg ν hp
  set t := (shiftEntropy ν).toReal with ht_def
  set c := (p : ℝ)⁻¹ * ∑ j ∈ Finset.range p, blockEntropy (blockPush ν) j with hc_def
  have hfin : shiftEntropy ν ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (iInf₂_le 1 le_rfl)
  have hnonneg : ∀ (μ : Measure (ℕ → Fin p)) [IsProbabilityMeasure μ] (M : ℕ),
      0 ≤ blockEntropy μ M := fun μ _ M ↦ partitionEntropy_nonneg μ _
  have ht0 : 0 ≤ t := ENNReal.toReal_nonneg
  have hc0 : 0 ≤ c := by
    refine mul_nonneg (by positivity) (Finset.sum_nonneg fun j _ ↦ partitionEntropy_nonneg _ _)
  have ht : ∀ M : ℕ, t * M ≤ blockEntropy ν M := by
    intro M
    rcases Nat.eq_zero_or_pos M with rfl | hM
    · simpa using hnonneg ν 0
    have hM' : (0 : ℝ) < M := by exact_mod_cast hM
    have := ENNReal.toReal_le_of_le_ofReal (div_nonneg (hnonneg ν M) hM'.le)
      (iInf₂_le M hM : shiftEntropy ν ≤ _)
    exact (le_div_iff₀ hM').1 this
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have key : ∀ k : ℕ, 1 ≤ k → t / p ≤ blockEntropy (blockAvg ν) k / k := by
    intro k hk
    have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
    refine le_of_forall_pos_le_add fun ε hε ↦ ?_
    obtain ⟨n, hn⟩ := exists_nat_gt ((t + c) / ε)
    have hn0 : (0 : ℝ) < n := lt_of_le_of_lt (div_nonneg (by linarith) hε.le) hn
    have hsub := blockEntropy_mul_le (blockAvg_map_shift hp hν) n k
    have hlow := blockEntropy_blockAvg_ge ν hp (n * k)
    have hQ := ht (n * k / p)
    have hdiv : ((n * k : ℕ) : ℝ) < ((n * k / p : ℕ) : ℝ) * p + p := by
      have h := Nat.lt_div_mul_add (a := n * k) hp
      exact_mod_cast h
    push_cast at hdiv
    set X := blockEntropy (blockAvg ν) k
    set Q := ((n * k / p : ℕ) : ℝ)
    -- `n X ≥ t Q - c` and `Q p + p > n k`
    have hA : t * Q - c ≤ n * X := by linarith
    have hB : t * (n * k) ≤ (t * Q) * p + t * p := by nlinarith
    have hC : t * (n * k) ≤ (n * X + c) * p + t * p := by nlinarith
    -- divide by `n k p`
    have hpos : (0 : ℝ) < n * k * p := by positivity
    have hD : t / p ≤ X / k + (c + t) / (n * k) := by
      rw [div_add_div _ _ (by positivity) (by positivity), div_le_div_iff₀ (by positivity)
        (by positivity)]
      nlinarith
    have hE : (c + t) / (n * k) ≤ (t + c) / n := by
      rw [add_comm c t]
      exact div_le_div_of_nonneg_left (by linarith) hn0 (by nlinarith)
    have hF : (t + c) / n < ε := by
      rw [div_lt_iff₀ hn0]
      rw [div_lt_iff₀ hε] at hn
      linarith
    linarith
  have hlow : ENNReal.ofReal (t / p) ≤ shiftEntropy (blockAvg ν) :=
    le_iInf₂ fun k hk ↦ ENNReal.ofReal_le_ofReal (key k hk)
  calc shiftEntropy ν = ENNReal.ofReal t := (ENNReal.ofReal_toReal hfin).symm
    _ = p * ENNReal.ofReal (t / p) := by
        rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg p),
          mul_div_cancel₀ _ (by positivity)]
    _ ≤ p * shiftEntropy (blockAvg ν) := by gcongr

end code

end Kolmogorov.PointToSet.SymbolicLower
