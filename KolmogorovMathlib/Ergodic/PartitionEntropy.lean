/-
Copyright (c) 2026 Emma Dinowitz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emma Dinowitz
-/
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.Subadditive
import Mathlib.Dynamics.Ergodic.MeasurePreserving
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

/-!
# Kolmogorov–Sinai entropy of finite partitions

Mathlib has no Kolmogorov–Sinai entropy. This module defines it for a map `T : X → X` and a
measure `μ`, in bits, from finite measurable partitions indexed by a finite type, and proves
the classical properties used in the note *Orbit complexity of Martin-Löf random points equals
entropy* (Walters, *An Introduction to Ergodic Theory*, Ch. 4).

* `IsMeasurablePartition P`: a family `P : ι → Set X` of pairwise disjoint measurable sets
  covering `X`.
* `entropyTerm q = -q log₂ q` (for `q ∈ [0, ∞]`, through `toReal`), `partitionEntropy μ P =
  H_μ(P)`, `condEntropy μ P Q = H_μ(P | Q) = H_μ(P ∨ Q) - H_μ(Q)`.
* `refinement T P n`: the cells `⋂_{k < n} T^{-k} P_{w_k}` of `P^n = ⋁_{k<n} T^{-k} P`, indexed by
  words `w : Fin n → ι`; `refinementEntropy μ T P n = H_μ(P^n)`.
* `entropyRate μ T P = h_μ(T, P) = inf_{n ≥ 1} H_μ(P^n) / n` (the same form as `shiftEntropy`
  on a shift), and `ksEntropy μ T = h_μ(T)`, the supremum of `entropyRate μ T P` over finite
  measurable partitions indexed by `Fin p`.

Main statements: subadditivity of `n ↦ H_μ(P^n)` and the limit form of `entropyRate`
(Fekete), invariance under null modifications of the cells and under reindexing, and the
inequality `h_μ(T, P) ≤ h_μ(T, Q) + H_μ(P | Q)` (Walters, Theorem 4.12(iv)).
Blueprint node `erg:partition-entropy`.

## Proof outline

Everything is reduced to one real inequality, the log-sum inequality
`sum_mul_log_sub_mul_log_le` (termwise Gibbs: `a log c - a log a ≤ c - a`). In natural units,
`H_μ(Q | P) log 2 = ∑_j ∑_i μ(Q_i ∩ P_j) (log μ(P_j) - log μ(Q_i ∩ P_j))`; grouping the cells of
a finer partition `P` inside the cells of `R` and applying the log-sum inequality gives
`condEntropy_le_of_refines`, whence (conditioning on the trivial partition)
`condEntropy_le_partitionEntropy` and the subadditivity of the join. With the reindexing
`P^{m+n} = P^m ∨ T^{-m} P^n` (`refinement_append`, through `Fin.appendEquiv`) and invariance
(`partitionEntropy_preimage`), `n ↦ H_μ(P^n)` is subadditive and Fekete's lemma
(`Subadditive.tendsto_lim`) identifies the infimum `entropyRate` with the limit. Walters 4.12(iv)
follows from `H_μ(P^n) ≤ H_μ(Q^n) + H_μ(P^n | Q^n)` and `H_μ(P^n | Q^n) ≤ n H_μ(P | Q)`, by
induction with the chain rule `condEntropy_join_le`.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal

namespace Kolmogorov.Ergodic

variable {X : Type*} [MeasurableSpace X]

/-- A finite measurable partition: pairwise disjoint measurable cells covering the space.
Blueprint node `erg:partition-entropy`. -/
structure IsMeasurablePartition {ι : Type*} (P : ι → Set X) : Prop where
  /-- Every cell is measurable. -/
  measurableSet : ∀ i, MeasurableSet (P i)
  /-- The cells are pairwise disjoint. -/
  disjoint : Pairwise (Function.onFun Disjoint P)
  /-- The cells cover the space. -/
  iUnion_eq : ⋃ i, P i = Set.univ

/-- The entropy contribution `-q log₂ q` of a cell of mass `q` (computed through `toReal`).
Blueprint node `erg:partition-entropy`. -/
def entropyTerm (q : ℝ≥0∞) : ℝ :=
  -q.toReal * Real.logb 2 q.toReal

/-- The Shannon entropy in bits `H_μ(P) = -∑_i μ(P_i) log₂ μ(P_i)` of a finite family of sets.
Blueprint node `erg:partition-entropy`. -/
def partitionEntropy (μ : Measure X) {ι : Type*} [Fintype ι] (P : ι → Set X) : ℝ :=
  ∑ i, entropyTerm (μ (P i))

/-- The join `P ∨ Q`, indexed by pairs. Blueprint node `erg:partition-entropy`. -/
def partitionJoin {ι κ : Type*} (P : ι → Set X) (Q : κ → Set X) : ι × κ → Set X :=
  fun ij ↦ P ij.1 ∩ Q ij.2

/-- The conditional entropy `H_μ(P | Q) = H_μ(P ∨ Q) - H_μ(Q)`.
Blueprint node `erg:partition-entropy`. -/
def condEntropy (μ : Measure X) {ι κ : Type*} [Fintype ι] [Fintype κ] (P : ι → Set X)
    (Q : κ → Set X) : ℝ :=
  partitionEntropy μ (partitionJoin P Q) - partitionEntropy μ Q

/-- The cells of the refinement `P^n = ⋁_{k<n} T^{-k} P`: for a word `w : Fin n → ι`, the set of
points `x` with `T^k x ∈ P_{w_k}` for all `k < n`. Blueprint node `erg:partition-entropy`. -/
def refinement (T : X → X) {ι : Type*} (P : ι → Set X) (n : ℕ) (w : Fin n → ι) : Set X :=
  ⋂ k : Fin n, T^[k] ⁻¹' P (w k)

/-- `H_μ(P^n)`, the entropy of the `n`-th refinement. Blueprint node `erg:partition-entropy`. -/
def refinementEntropy (μ : Measure X) (T : X → X) {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P : ι → Set X) (n : ℕ) : ℝ :=
  partitionEntropy μ (refinement T P n)

/-- The entropy rate `h_μ(T, P) = inf_{n ≥ 1} H_μ(P^n) / n` of a partition, in bits.
Blueprint node `erg:partition-entropy`. -/
def entropyRate (μ : Measure X) (T : X → X) {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P : ι → Set X) : ℝ≥0∞ :=
  ⨅ n : ℕ, ⨅ (_ : 1 ≤ n), ENNReal.ofReal (refinementEntropy μ T P n / n)

/-- The Kolmogorov–Sinai entropy `h_μ(T)` in bits: the supremum of `h_μ(T, P)` over finite
measurable partitions `P : Fin p → Set X`. Blueprint node `erg:partition-entropy`. -/
def ksEntropy (μ : Measure X) (T : X → X) : ℝ≥0∞ :=
  ⨆ (p : ℕ) (P : Fin p → Set X) (_ : IsMeasurablePartition P), entropyRate μ T P

section Properties

variable {ι κ : Type*}

/-! ### Real-analytic helpers -/

/-- `entropyTerm q * log 2 = -(q log q)`: `entropyTerm` in natural units. -/
private lemma entropyTerm_mul_log_two (q : ℝ≥0∞) :
    entropyTerm q * Real.log 2 = -(q.toReal * Real.log q.toReal) := by
  have h : Real.log 2 ≠ 0 := (Real.log_pos one_lt_two).ne'
  rw [entropyTerm, Real.logb]
  field_simp

/-- The termwise Gibbs inequality `a log c - a log a ≤ c - a`. -/
private lemma gibbs_term {a c : ℝ} (ha : 0 ≤ a) (hc : 0 ≤ c) (hac : 0 < a → 0 < c) :
    a * Real.log c - a * Real.log a ≤ c - a := by
  rcases ha.eq_or_lt with rfl | ha'
  · simpa using hc
  · have hc' := hac ha'
    have h := Real.log_le_sub_one_of_pos (div_pos hc' ha')
    rw [Real.log_div hc'.ne' ha'.ne'] at h
    have h2 : a * (Real.log c - Real.log a) ≤ a * (c / a - 1) :=
      mul_le_mul_of_nonneg_left h ha
    have h3 : a * (c / a) = c := by field_simp
    nlinarith

/-- The log-sum inequality: for `0 ≤ a_j ≤ p_j`,
`∑ a_j log (p_j / a_j) ≤ (∑ a_j) log ((∑ p_j) / (∑ a_j))`, written without divisions.
Blueprint node `erg:partition-entropy`. -/
private theorem sum_mul_log_sub_mul_log_le {α : Type*} (s : Finset α) (a p : α → ℝ)
    (ha : ∀ j ∈ s, 0 ≤ a j) (hap : ∀ j ∈ s, a j ≤ p j) :
    ∑ j ∈ s, (a j * Real.log (p j) - a j * Real.log (a j)) ≤
      (∑ j ∈ s, a j) * Real.log (∑ j ∈ s, p j) -
        (∑ j ∈ s, a j) * Real.log (∑ j ∈ s, a j) := by
  have hA : 0 ≤ ∑ j ∈ s, a j := Finset.sum_nonneg ha
  rcases hA.eq_or_lt with hA0 | hApos
  · have hz : ∀ j ∈ s, a j = 0 := (Finset.sum_eq_zero_iff_of_nonneg ha).1 hA0.symm
    rw [← hA0, Finset.sum_eq_zero fun j hj ↦ by simp [hz j hj]]
    simp
  · obtain ⟨A, hAdef⟩ : ∃ A, A = ∑ j ∈ s, a j := ⟨_, rfl⟩
    obtain ⟨P, hPdef⟩ : ∃ P, P = ∑ j ∈ s, p j := ⟨_, rfl⟩
    rw [← hAdef] at hApos ⊢
    rw [← hPdef]
    have hAP : A ≤ P := hAdef ▸ hPdef ▸ Finset.sum_le_sum hap
    have hPpos : 0 < P := hApos.trans_le hAP
    have key : ∀ j ∈ s, a j * Real.log (p j * A / P) - a j * Real.log (a j) ≤
        p j * A / P - a j := by
      intro j hj
      refine gibbs_term (ha j hj) ?_ ?_
      · exact div_nonneg (mul_nonneg ((ha j hj).trans (hap j hj)) hApos.le) hPpos.le
      · intro h
        exact div_pos (mul_pos (h.trans_le (hap j hj)) hApos) hPpos
    have hsum := Finset.sum_le_sum key
    have hc : ∑ j ∈ s, p j * A / P = A := by
      rw [← Finset.sum_div, ← Finset.sum_mul, ← hPdef]
      field_simp
    have hlog : ∀ j ∈ s, a j * Real.log (p j * A / P) =
        a j * Real.log (p j) + a j * Real.log A - a j * Real.log P := by
      intro j hj
      rcases (ha j hj).eq_or_lt with h0 | hpos
      · rw [← h0]
        ring
      · have hp : 0 < p j := hpos.trans_le (hap j hj)
        rw [Real.log_div (mul_pos hp hApos).ne' hPpos.ne', Real.log_mul hp.ne' hApos.ne']
        ring
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, hc, Finset.sum_congr rfl hlog,
      Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul,
      ← hAdef] at hsum
    rw [Finset.sum_sub_distrib]
    linarith

/-! ### Measures of cells -/

/-- The mass of a measurable set is the sum of the masses of its traces on the cells of a
measurable partition. Blueprint node `erg:partition-entropy`. -/
theorem IsMeasurablePartition.toReal_measure_eq_sum_inter [Fintype ι] {μ : Measure X}
    [IsFiniteMeasure μ] {P : ι → Set X} (hP : IsMeasurablePartition P) {S : Set X}
    (hS : MeasurableSet S) : (μ S).toReal = ∑ i, (μ (P i ∩ S)).toReal := by
  have hU : S = ⋃ i, P i ∩ S := by rw [← Set.iUnion_inter, hP.iUnion_eq, Set.univ_inter]
  conv_lhs => rw [hU]
  rw [measure_iUnion (fun i j hij ↦ Disjoint.mono Set.inter_subset_left Set.inter_subset_left
    (hP.disjoint hij)) (fun i ↦ (hP.measurableSet i).inter hS), tsum_fintype,
    ENNReal.toReal_sum (fun _ _ ↦ measure_ne_top _ _)]

/-- `H_μ(Q | P)` in natural units, as a sum over the cells of `P` of
`∑_i μ(Q_i ∩ P_j) (log μ(P_j) - log μ(Q_i ∩ P_j))`. -/
private lemma condEntropy_mul_log_two [Fintype ι] [Fintype κ] {μ : Measure X}
    [IsFiniteMeasure μ] {Q : ι → Set X} {P : κ → Set X} (hQ : IsMeasurablePartition Q)
    (hP : ∀ j, MeasurableSet (P j)) :
    condEntropy μ Q P * Real.log 2 =
      ∑ j, ∑ i, ((μ (Q i ∩ P j)).toReal * Real.log (μ (P j)).toReal -
        (μ (Q i ∩ P j)).toReal * Real.log (μ (Q i ∩ P j)).toReal) := by
  simp only [condEntropy, partitionEntropy, sub_mul, Finset.sum_mul, entropyTerm_mul_log_two,
    partitionJoin]
  rw [Fintype.sum_prod_type, Finset.sum_comm, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [Finset.sum_sub_distrib, ← Finset.sum_mul, ← hQ.toReal_measure_eq_sum_inter (hP j),
    Finset.sum_neg_distrib]
  ring

/-- Conditional entropy is nonnegative: `H_μ(Q) ≤ H_μ(P ∨ Q)`.
Blueprint node `erg:partition-entropy`. -/
theorem condEntropy_nonneg [Fintype ι] [Fintype κ] (μ : Measure X) [IsProbabilityMeasure μ]
    {P : ι → Set X}
    {Q : κ → Set X} (hP : IsMeasurablePartition P) (hQ : IsMeasurablePartition Q) :
    0 ≤ condEntropy μ P Q := by
  have hlog : 0 < Real.log 2 := Real.log_pos one_lt_two
  rw [← mul_nonneg_iff_of_pos_right hlog, condEntropy_mul_log_two hP hQ.measurableSet]
  refine Finset.sum_nonneg fun j _ ↦ Finset.sum_nonneg fun i _ ↦ ?_
  rw [sub_nonneg]
  rcases ENNReal.toReal_nonneg.eq_or_lt with h0 | hpos
  · rw [← h0]
    simp
  · refine mul_le_mul_of_nonneg_left (Real.log_le_log hpos ?_) hpos.le
    exact ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono Set.inter_subset_right)

/-! ### Partitions -/

/-- `-q log₂ q ≥ 0` for a mass `q ≤ 1`. Blueprint node `erg:partition-entropy`. -/
theorem entropyTerm_nonneg {q : ℝ≥0∞} (hq : q ≤ 1) : 0 ≤ entropyTerm q := by
  have hlog : 0 < Real.log 2 := Real.log_pos one_lt_two
  rw [← mul_nonneg_iff_of_pos_right hlog, entropyTerm_mul_log_two, neg_nonneg]
  have h1 : q.toReal ≤ 1 := by
    simpa using ENNReal.toReal_mono ENNReal.one_ne_top hq
  exact mul_nonpos_of_nonneg_of_nonpos ENNReal.toReal_nonneg
    (Real.log_nonpos ENNReal.toReal_nonneg h1)

/-- The entropy of a family of sets is nonnegative for a measure of mass at most one.
Blueprint node `erg:partition-entropy`. -/
theorem partitionEntropy_nonneg [Fintype ι] (μ : Measure X) [IsProbabilityMeasure μ]
    (P : ι → Set X) :
    0 ≤ partitionEntropy μ P :=
  Finset.sum_nonneg fun _ _ ↦ entropyTerm_nonneg prob_le_one

/-- The refinements of a measurable partition are measurable partitions.
Blueprint node `erg:partition-entropy`. -/
theorem IsMeasurablePartition.refinement {T : X → X} (hT : Measurable T) {P : ι → Set X}
    (hP : IsMeasurablePartition P) (n : ℕ) : IsMeasurablePartition (refinement T P n) := by
  refine ⟨fun w ↦ MeasurableSet.iInter fun k ↦ hT.iterate k (hP.measurableSet _), ?_, ?_⟩
  · intro w w' hww'
    obtain ⟨k, hk⟩ := Function.ne_iff.1 hww'
    refine Set.disjoint_left.2 fun x hx hx' ↦ ?_
    exact Set.disjoint_left.1 (hP.disjoint hk) (Set.mem_iInter.1 hx k) (Set.mem_iInter.1 hx' k)
  · refine Set.eq_univ_of_forall fun x ↦ ?_
    have h : ∀ k : Fin n, ∃ i, T^[k] x ∈ P i := fun k ↦
      Set.mem_iUnion.1 (hP.iUnion_eq ▸ Set.mem_univ (T^[k] x))
    choose w hw using h
    exact Set.mem_iUnion.2 ⟨w, Set.mem_iInter.2 hw⟩

/-- The join of two measurable partitions is a measurable partition.
Blueprint node `erg:partition-entropy`. -/
theorem IsMeasurablePartition.join {P : ι → Set X} {Q : κ → Set X}
    (hP : IsMeasurablePartition P) (hQ : IsMeasurablePartition Q) :
    IsMeasurablePartition (partitionJoin P Q) := by
  refine ⟨fun ij ↦ (hP.measurableSet _).inter (hQ.measurableSet _), ?_, ?_⟩
  · rintro ⟨i, j⟩ ⟨i', j'⟩ h
    by_cases hi : i = i'
    · have hj : j ≠ j' := fun hj ↦ h (by rw [hi, hj])
      exact Disjoint.mono Set.inter_subset_right Set.inter_subset_right (hQ.disjoint hj)
    · exact Disjoint.mono Set.inter_subset_left Set.inter_subset_left (hP.disjoint hi)
  · refine Set.eq_univ_of_forall fun x ↦ ?_
    obtain ⟨i, hi⟩ := Set.mem_iUnion.1 (hP.iUnion_eq ▸ Set.mem_univ x)
    obtain ⟨j, hj⟩ := Set.mem_iUnion.1 (hQ.iUnion_eq ▸ Set.mem_univ x)
    exact Set.mem_iUnion.2 ⟨(i, j), hi, hj⟩

/-- The preimage of a measurable partition under a measurable map is a measurable partition.
Blueprint node `erg:partition-entropy`. -/
theorem IsMeasurablePartition.preimage {S : X → X} (hS : Measurable S) {P : ι → Set X}
    (hP : IsMeasurablePartition P) : IsMeasurablePartition (fun i ↦ S ⁻¹' P i) :=
  ⟨fun i ↦ hS (hP.measurableSet i), fun _ _ hij ↦ (hP.disjoint hij).preimage S, by
    rw [← Set.preimage_iUnion, hP.iUnion_eq, Set.preimage_univ]⟩

/-- The trivial partition `{X}`. -/
private lemma isMeasurablePartition_univ :
    IsMeasurablePartition (fun _ : Unit ↦ (Set.univ : Set X)) :=
  ⟨fun _ ↦ MeasurableSet.univ, fun a b h ↦ (h (Subsingleton.elim a b)).elim, Set.iUnion_const _⟩

/-! ### Reindexing -/

/-- The entropy of a family of sets only depends on the masses of its cells, up to reindexing.
Blueprint node `erg:partition-entropy`. -/
theorem partitionEntropy_congr_equiv [Fintype ι] [Fintype κ] (μ : Measure X) {P : ι → Set X}
    {Q : κ → Set X} (e : κ ≃ ι) (h : ∀ k, μ (Q k) = μ (P (e k))) :
    partitionEntropy μ Q = partitionEntropy μ P :=
  Fintype.sum_equiv e _ _ fun k ↦ by rw [h]

/-- The join is commutative for the entropy. Blueprint node `erg:partition-entropy`. -/
theorem partitionEntropy_join_comm [Fintype ι] [Fintype κ] (μ : Measure X) (P : ι → Set X)
    (Q : κ → Set X) :
    partitionEntropy μ (partitionJoin P Q) = partitionEntropy μ (partitionJoin Q P) :=
  partitionEntropy_congr_equiv μ (Equiv.prodComm ι κ) fun _ ↦ by
    simp [partitionJoin, Set.inter_comm]

/-- The join is associative for the entropy. Blueprint node `erg:partition-entropy`. -/
theorem partitionEntropy_join_assoc {ι' : Type*} [Fintype ι] [Fintype κ] [Fintype ι']
    (μ : Measure X) (A : ι → Set X) (B : κ → Set X) (C : ι' → Set X) :
    partitionEntropy μ (partitionJoin (partitionJoin A B) C) =
      partitionEntropy μ (partitionJoin A (partitionJoin B C)) :=
  partitionEntropy_congr_equiv μ (Equiv.prodAssoc ι κ ι') fun _ ↦ by
    simp [partitionJoin, Set.inter_assoc]

/-- Conditional entropy is invariant under reindexing of both partitions.
Blueprint node `erg:partition-entropy`. -/
theorem condEntropy_congr_equiv {ι₁ ι₂ κ₁ κ₂ : Type*} [Fintype ι₁] [Fintype ι₂] [Fintype κ₁]
    [Fintype κ₂] (μ : Measure X) {P₁ : ι₁ → Set X} {P₂ : ι₂ → Set X} {Q₁ : κ₁ → Set X}
    {Q₂ : κ₂ → Set X} (e : ι₁ ≃ ι₂) (e' : κ₁ ≃ κ₂) (hP : ∀ i, P₁ i = P₂ (e i))
    (hQ : ∀ j, Q₁ j = Q₂ (e' j)) :
    condEntropy μ P₁ Q₁ = condEntropy μ P₂ Q₂ := by
  unfold condEntropy
  rw [partitionEntropy_congr_equiv μ e' fun j ↦ by rw [hQ],
    partitionEntropy_congr_equiv μ (P := partitionJoin P₂ Q₂) (e.prodCongr e') fun ij ↦ by
      simp [partitionJoin, hP, hQ]]

/-! ### Conditional entropy -/

/-- `P` refines `R`: every cell of `P` lies in some cell of `R`.
Blueprint node `erg:partition-entropy`. -/
def Refines (P : ι → Set X) (R : κ → Set X) : Prop :=
  ∀ i, ∃ j, P i ⊆ R j

/-- Conditioning on a finer partition decreases conditional entropy:
`H_μ(Q | P) ≤ H_μ(Q | R)` when `P` refines `R`. Blueprint node `erg:partition-entropy`. -/
theorem condEntropy_le_of_refines {ι' : Type*} [Fintype ι'] [Fintype ι] [Fintype κ]
    (μ : Measure X) [IsProbabilityMeasure μ] {Q : ι' → Set X} {P : ι → Set X}
    {R : κ → Set X} (hQ : IsMeasurablePartition Q) (hP : IsMeasurablePartition P)
    (hR : IsMeasurablePartition R) (hPR : Refines P R) :
    condEntropy μ Q P ≤ condEntropy μ Q R := by
  classical
  choose f hf using hPR
  have hlog : 0 < Real.log 2 := Real.log_pos one_lt_two
  rw [← mul_le_mul_iff_of_pos_right hlog, condEntropy_mul_log_two hQ hP.measurableSet,
    condEntropy_mul_log_two hQ hR.measurableSet]
  have hcell : ∀ (S : Set X) k j, S ∩ R k ∩ P j = if f j = k then S ∩ P j else ∅ := by
    intro S k j
    split_ifs with h
    · subst h
      ext x
      simp only [Set.mem_inter_iff]
      constructor
      · rintro ⟨⟨hS, -⟩, hPx⟩
        exact ⟨hS, hPx⟩
      · rintro ⟨hS, hPx⟩
        exact ⟨⟨hS, hf j hPx⟩, hPx⟩
    · ext x
      simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false]
      rintro ⟨⟨-, hRx⟩, hPx⟩
      exact Set.disjoint_left.1 (hR.disjoint h) (hf j hPx) hRx
  have hb : ∀ S : Set X, MeasurableSet S → ∀ k, (μ (S ∩ R k)).toReal =
      ∑ j ∈ Finset.univ.filter (fun j ↦ f j = k), (μ (S ∩ P j)).toReal := by
    intro S hS k
    rw [Finset.sum_filter, hP.toReal_measure_eq_sum_inter (hS.inter (hR.measurableSet k))]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [Set.inter_comm, hcell]
    split_ifs <;> simp
  have hbR : ∀ k, (μ (R k)).toReal =
      ∑ j ∈ Finset.univ.filter (fun j ↦ f j = k), (μ (P j)).toReal := by
    intro k
    simpa using hb Set.univ MeasurableSet.univ k
  calc ∑ j, ∑ i, ((μ (Q i ∩ P j)).toReal * Real.log (μ (P j)).toReal -
        (μ (Q i ∩ P j)).toReal * Real.log (μ (Q i ∩ P j)).toReal)
      = ∑ i, ∑ k, ∑ j ∈ Finset.univ.filter (fun j ↦ f j = k),
          ((μ (Q i ∩ P j)).toReal * Real.log (μ (P j)).toReal -
            (μ (Q i ∩ P j)).toReal * Real.log (μ (Q i ∩ P j)).toReal) := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun i _ ↦ (Finset.sum_fiberwise _ _ _).symm
    _ ≤ ∑ i, ∑ k,
          ((∑ j ∈ Finset.univ.filter (fun j ↦ f j = k), (μ (Q i ∩ P j)).toReal) *
              Real.log (∑ j ∈ Finset.univ.filter (fun j ↦ f j = k), (μ (P j)).toReal) -
            (∑ j ∈ Finset.univ.filter (fun j ↦ f j = k), (μ (Q i ∩ P j)).toReal) *
              Real.log (∑ j ∈ Finset.univ.filter (fun j ↦ f j = k), (μ (Q i ∩ P j)).toReal)) :=
        Finset.sum_le_sum fun i _ ↦ Finset.sum_le_sum fun k _ ↦
          sum_mul_log_sub_mul_log_le _ (fun j ↦ (μ (Q i ∩ P j)).toReal)
            (fun j ↦ (μ (P j)).toReal) (fun _ _ ↦ ENNReal.toReal_nonneg)
            (fun _ _ ↦ ENNReal.toReal_mono (measure_ne_top _ _)
              (measure_mono Set.inter_subset_right))
    _ = ∑ k, ∑ i, ((μ (Q i ∩ R k)).toReal * Real.log (μ (R k)).toReal -
          (μ (Q i ∩ R k)).toReal * Real.log (μ (Q i ∩ R k)).toReal) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun k _ ↦ Finset.sum_congr rfl fun i _ ↦ ?_
        rw [hb _ (hQ.measurableSet i) k, hbR k]

/-- Refining a partition increases its entropy: `H_μ(A) ≤ H_μ(B)` when `B` refines `A`.
Blueprint node `erg:partition-entropy`. -/
theorem partitionEntropy_le_of_refines [Fintype ι] [Fintype κ] (μ : Measure X)
    [IsProbabilityMeasure μ] {A : ι → Set X} {B : κ → Set X} (hA : IsMeasurablePartition A)
    (hB : IsMeasurablePartition B) (hBA : Refines B A) :
    partitionEntropy μ A ≤ partitionEntropy μ B := by
  classical
  choose f hf using hBA
  have h1 := condEntropy_nonneg μ hB hA
  have hcell : ∀ j i, B j ∩ A i = if f j = i then B j else ∅ := by
    intro j i
    split_ifs with h
    · subst h
      exact Set.inter_eq_left.2 (hf j)
    · exact Set.disjoint_iff_inter_eq_empty.1 (Disjoint.mono_left (hf j) (hA.disjoint h))
  have h2 : partitionEntropy μ (partitionJoin B A) = partitionEntropy μ B := by
    unfold partitionEntropy
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    simp only [partitionJoin, hcell]
    rw [Finset.sum_eq_single (f j) (fun i _ hi ↦ by simp [Ne.symm hi, entropyTerm]) (by simp)]
    simp
  unfold condEntropy at h1
  linarith

/-- Conditioning decreases entropy: `H_μ(Q | P) ≤ H_μ(Q)`.
Blueprint node `erg:partition-entropy`. -/
theorem condEntropy_le_partitionEntropy [Fintype ι] [Fintype κ] (μ : Measure X)
    [IsProbabilityMeasure μ] {Q : κ → Set X} {P : ι → Set X} (hQ : IsMeasurablePartition Q)
    (hP : IsMeasurablePartition P) : condEntropy μ Q P ≤ partitionEntropy μ Q := by
  have h := condEntropy_le_of_refines μ hQ hP isMeasurablePartition_univ
    (fun _ ↦ ⟨(), Set.subset_univ _⟩)
  have h2 : condEntropy μ Q (fun _ : Unit ↦ (Set.univ : Set X)) = partitionEntropy μ Q := by
    simp [condEntropy, partitionEntropy, partitionJoin, entropyTerm, Fintype.sum_prod_type]
  linarith

/-- Subadditivity of the entropy of a join: `H_μ(P ∨ Q) ≤ H_μ(P) + H_μ(Q)`.
Blueprint node `erg:partition-entropy`. -/
theorem partitionEntropy_join_le [Fintype ι] [Fintype κ] (μ : Measure X) [IsProbabilityMeasure μ]
    {P : ι → Set X}
    {Q : κ → Set X} (hP : IsMeasurablePartition P) (hQ : IsMeasurablePartition Q) :
    partitionEntropy μ (partitionJoin P Q) ≤ partitionEntropy μ P + partitionEntropy μ Q := by
  have h := condEntropy_le_partitionEntropy μ hP hQ
  unfold condEntropy at h
  linarith

/-- The chain rule inequality `H_μ(A ∨ B | C) ≤ H_μ(A | C) + H_μ(B | C)`.
Blueprint node `erg:partition-entropy`. -/
theorem condEntropy_join_le {ι' : Type*} [Fintype ι] [Fintype κ] [Fintype ι'] (μ : Measure X)
    [IsProbabilityMeasure μ] {A : ι → Set X} {B : κ → Set X} {C : ι' → Set X}
    (hA : IsMeasurablePartition A) (hB : IsMeasurablePartition B)
    (hC : IsMeasurablePartition C) :
    condEntropy μ (partitionJoin A B) C ≤ condEntropy μ A C + condEntropy μ B C := by
  have h1 : condEntropy μ (partitionJoin A B) C =
      condEntropy μ A (partitionJoin B C) + condEntropy μ B C := by
    simp only [condEntropy]
    rw [partitionEntropy_join_assoc]
    ring
  have h2 := condEntropy_le_of_refines μ hA (hB.join hC) hC
    (fun ij ↦ ⟨ij.2, Set.inter_subset_right⟩)
  linarith

/-- The entropy of a family of measurable sets is invariant under pulling back by a
measure-preserving map. Blueprint node `erg:partition-entropy`. -/
theorem partitionEntropy_preimage [Fintype ι] {μ : Measure X} {S : X → X}
    (hS : MeasurePreserving S μ μ) {P : ι → Set X} (hP : ∀ i, MeasurableSet (P i)) :
    partitionEntropy μ (fun i ↦ S ⁻¹' P i) = partitionEntropy μ P :=
  Finset.sum_congr rfl fun i _ ↦ by rw [hS.measure_preimage (hP i).nullMeasurableSet]

/-- Conditional entropy is invariant under pulling back by a measure-preserving map.
Blueprint node `erg:partition-entropy`. -/
theorem condEntropy_preimage [Fintype ι] [Fintype κ] {μ : Measure X} {S : X → X}
    (hS : MeasurePreserving S μ μ) {P : ι → Set X} {Q : κ → Set X}
    (hP : ∀ i, MeasurableSet (P i)) (hQ : ∀ j, MeasurableSet (Q j)) :
    condEntropy μ (fun i ↦ S ⁻¹' P i) (fun j ↦ S ⁻¹' Q j) = condEntropy μ P Q := by
  unfold condEntropy
  rw [partitionEntropy_preimage hS hQ]
  congr 1
  exact partitionEntropy_preimage hS (P := partitionJoin P Q) fun ij ↦ (hP _).inter (hQ _)

/-! ### Refinements -/

omit [MeasurableSpace X] in
/-- `P^{m+n} = P^m ∨ T^{-m} P^n`, cell by cell. Blueprint node `erg:partition-entropy`. -/
theorem refinement_append (T : X → X) (P : ι → Set X) {m n : ℕ} (u : Fin m → ι)
    (v : Fin n → ι) :
    refinement T P (m + n) (Fin.append u v) =
      refinement T P m u ∩ T^[m] ⁻¹' refinement T P n v := by
  ext x
  simp only [refinement, Set.mem_inter_iff, Set.mem_iInter, Set.mem_preimage]
  rw [Fin.forall_fin_add]
  refine and_congr (forall_congr' fun i ↦ ?_) (forall_congr' fun j ↦ ?_)
  · rw [Fin.append_left, Fin.val_castAdd]
  · rw [Fin.append_right, Fin.val_natAdd, add_comm, Function.iterate_add_apply]

omit [MeasurableSpace X] in
/-- `P^1 = P`, cell by cell. Blueprint node `erg:partition-entropy`. -/
theorem refinement_one (T : X → X) (P : ι → Set X) (w : Fin 1 → ι) :
    refinement T P 1 w = P (w 0) := by
  ext x
  simp [refinement, Fin.forall_fin_one]

/-- `H_μ(P^{m+n}) = H_μ(P^m ∨ T^{-m} P^n)`. -/
private lemma refinementEntropy_add_eq [Fintype ι] (μ : Measure X) (T : X → X)
    (P : ι → Set X) (m n : ℕ) :
    partitionEntropy μ (refinement T P (m + n)) =
      partitionEntropy μ (partitionJoin (refinement T P m)
        (fun v ↦ T^[m] ⁻¹' refinement T P n v)) :=
  (partitionEntropy_congr_equiv μ (Fin.appendEquiv m n) fun uv ↦ by
    change _ = μ (refinement T P (m + n) (Fin.append uv.1 uv.2))
    rw [refinement_append]
    rfl).symm

/-- Subadditivity of the refinement entropies of an invariant measure:
`H_μ(P^{m+n}) ≤ H_μ(P^m) + H_μ(P^n)`. Blueprint node `erg:partition-entropy`. -/
theorem refinementEntropy_add_le [Fintype ι] [DecidableEq ι] {μ : Measure X}
    [IsProbabilityMeasure μ] {T : X → X}
    (hT : MeasurePreserving T μ μ) {P : ι → Set X} (hP : IsMeasurablePartition P) (m n : ℕ) :
    refinementEntropy μ T P (m + n) ≤ refinementEntropy μ T P m + refinementEntropy μ T P n := by
  have hm := hP.refinement hT.measurable m
  have hn := hP.refinement hT.measurable n
  unfold refinementEntropy
  rw [refinementEntropy_add_eq, ← partitionEntropy_preimage (hT.iterate m) hn.measurableSet]
  exact partitionEntropy_join_le μ hm (hn.preimage (hT.iterate m).measurable)

/-- The entropy rate is the limit of `H_μ(P^n) / n` (Fekete's lemma).
Blueprint node `erg:partition-entropy`. -/
theorem tendsto_refinementEntropy_div [Fintype ι] [DecidableEq ι] {μ : Measure X}
    [IsProbabilityMeasure μ] {T : X → X}
    (hT : MeasurePreserving T μ μ) {P : ι → Set X} (hP : IsMeasurablePartition P) :
    Tendsto (fun n : ℕ ↦ ENNReal.ofReal (refinementEntropy μ T P n / n)) atTop
      (𝓝 (entropyRate μ T P)) := by
  have hsub : Subadditive (fun n ↦ refinementEntropy μ T P n) :=
    fun m n ↦ refinementEntropy_add_le hT hP m n
  have hbdd : BddBelow (Set.range fun n ↦ refinementEntropy μ T P n / n) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨n, rfl⟩
    exact div_nonneg (partitionEntropy_nonneg _ _) n.cast_nonneg
  have hlim := (ENNReal.continuous_ofReal.tendsto _).comp (hsub.tendsto_lim hbdd)
  have heq : entropyRate μ T P = ENNReal.ofReal hsub.lim := by
    apply le_antisymm
    · exact ge_of_tendsto hlim (eventually_atTop.2 ⟨1, fun n hn ↦ iInf₂_le n hn⟩)
    · exact le_iInf₂ fun n hn ↦
        ENNReal.ofReal_le_ofReal (hsub.lim_le_div hbdd (Nat.one_le_iff_ne_zero.1 hn))
  rw [heq]
  exact hlim

/-- The entropy of a measurable partition is at most `log₂` of the number of its cells.
Blueprint node `erg:partition-entropy`. -/
theorem partitionEntropy_le_logb_card [Fintype ι] (μ : Measure X) [IsProbabilityMeasure μ]
    {P : ι → Set X} (hP : IsMeasurablePartition P) :
    partitionEntropy μ P ≤ Real.logb 2 (Fintype.card ι) := by
  have hlog : 0 < Real.log 2 := Real.log_pos one_lt_two
  rw [← mul_le_mul_iff_of_pos_right hlog, Real.logb, div_mul_cancel₀ _ hlog.ne']
  simp only [partitionEntropy, Finset.sum_mul, entropyTerm_mul_log_two]
  rcases isEmpty_or_nonempty ι with hι | hι
  · simp
  have hsum : ∑ i, (μ (P i)).toReal = 1 := by
    simpa using (hP.toReal_measure_eq_sum_inter (μ := μ) MeasurableSet.univ).symm
  have hN : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have key : ∀ i ∈ Finset.univ, (μ (P i)).toReal * Real.log (Fintype.card ι : ℝ)⁻¹ -
      (μ (P i)).toReal * Real.log (μ (P i)).toReal ≤
        (Fintype.card ι : ℝ)⁻¹ - (μ (P i)).toReal :=
    fun _ _ ↦ gibbs_term ENNReal.toReal_nonneg (inv_nonneg.2 hN.le) fun _ ↦ inv_pos.2 hN
  have h := Finset.sum_le_sum key
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul, hsum, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul, mul_inv_cancel₀ hN.ne', Real.log_inv] at h
  rw [Finset.sum_neg_distrib]
  linarith

/-- The entropy rate is finite: `h_μ(T, P) ≤ log₂ |ι|`. Blueprint node `erg:partition-entropy`. -/
theorem entropyRate_le_logb_card [Fintype ι] [DecidableEq ι] (μ : Measure X)
    [IsProbabilityMeasure μ] {T : X → X}
    (hT : Measurable T) {P : ι → Set X} (hP : IsMeasurablePartition P) :
    entropyRate μ T P ≤ ENNReal.ofReal (Real.logb 2 (Fintype.card ι)) := by
  refine (iInf₂_le 1 le_rfl : entropyRate μ T P ≤ _).trans (ENNReal.ofReal_le_ofReal ?_)
  rw [Nat.cast_one, div_one]
  have h := partitionEntropy_le_logb_card μ (hP.refinement hT 1)
  simpa [refinementEntropy, Fintype.card_fun] using h

/-- Changing the cells on null sets does not change the refinement entropies.
Blueprint node `erg:partition-entropy`. -/
theorem refinementEntropy_congr_ae [Fintype ι] [DecidableEq ι] {μ : Measure X} {T : X → X}
    (hT : MeasurePreserving T μ μ)
    {P Q : ι → Set X} (hPQ : ∀ i, P i =ᵐ[μ] Q i) (n : ℕ) :
    refinementEntropy μ T P n = refinementEntropy μ T Q n := by
  refine Finset.sum_congr rfl fun w _ ↦ ?_
  rw [refinement, refinement, measure_congr (Filter.EventuallyEqSet.iInter fun k : Fin n ↦
    (hT.iterate k).quasiMeasurePreserving.preimage_ae_eq (hPQ (w k)))]

/-- Changing the cells on null sets does not change the entropy rate.
Blueprint node `erg:partition-entropy`. -/
theorem entropyRate_congr_ae [Fintype ι] [DecidableEq ι] {μ : Measure X} {T : X → X}
    (hT : MeasurePreserving T μ μ)
    {P Q : ι → Set X} (hPQ : ∀ i, P i =ᵐ[μ] Q i) :
    entropyRate μ T P = entropyRate μ T Q := by
  simp only [entropyRate, refinementEntropy_congr_ae hT hPQ]

/-- The entropy rate does not depend on the indexing of the cells.
Blueprint node `erg:partition-entropy`. -/
theorem entropyRate_comp_equiv [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (μ : Measure X) (T : X → X) (P : ι → Set X) (e : κ ≃ ι) :
    entropyRate μ T (P ∘ e) = entropyRate μ T P := by
  have h : ∀ n, refinementEntropy μ T (P ∘ e) n = refinementEntropy μ T P n := fun n ↦
    partitionEntropy_congr_equiv μ (Equiv.piCongrRight fun _ : Fin n ↦ e) fun _ ↦ rfl
  simp only [entropyRate, h]

/-- Reindexing a measurable partition by an equivalence gives a measurable partition.
Blueprint node `erg:partition-entropy`. -/
theorem IsMeasurablePartition.comp_equiv {P : ι → Set X} (hP : IsMeasurablePartition P)
    (e : κ ≃ ι) : IsMeasurablePartition (P ∘ e) :=
  ⟨fun _ ↦ hP.measurableSet _, fun _ _ hij ↦ hP.disjoint (e.injective.ne hij), by
    rw [← hP.iUnion_eq]
    exact e.iSup_comp (g := P)⟩

/-- Every finite measurable partition has entropy rate at most `h_μ(T)`, whatever its finite
index type. Blueprint node `erg:partition-entropy`. -/
theorem entropyRate_le_ksEntropy [Fintype ι] [DecidableEq ι] (μ : Measure X) (T : X → X)
    {P : ι → Set X}
    (hP : IsMeasurablePartition P) : entropyRate μ T P ≤ ksEntropy μ T := by
  rw [← entropyRate_comp_equiv μ T P (Fintype.equivFin ι).symm]
  exact le_iSup₂_of_le (Fintype.card ι) (P ∘ (Fintype.equivFin ι).symm)
    (le_iSup_of_le (hP.comp_equiv _) le_rfl)

/-- `H_μ(P^n | Q^n) ≤ n H_μ(P | Q)` for an invariant measure and `n ≥ 1`. -/
private lemma condEntropy_refinement_le [Fintype ι] [Fintype κ] {μ : Measure X}
    [IsProbabilityMeasure μ] {T : X → X} (hT : MeasurePreserving T μ μ) {P : ι → Set X}
    {Q : κ → Set X} (hP : IsMeasurablePartition P) (hQ : IsMeasurablePartition Q) {n : ℕ}
    (hn : 1 ≤ n) :
    condEntropy μ (refinement T P n) (refinement T Q n) ≤ n * condEntropy μ P Q := by
  have h1 : condEntropy μ (refinement T P 1) (refinement T Q 1) = condEntropy μ P Q :=
    condEntropy_congr_equiv μ (Equiv.funUnique (Fin 1) ι) (Equiv.funUnique (Fin 1) κ)
      (refinement_one T P) (refinement_one T Q)
  induction n, hn using Nat.le_induction with
  | base => simpa using h1.le
  | succ n hn ih =>
    have hPn := hP.refinement hT.measurable n
    have hQn := hQ.refinement hT.measurable n
    have hP1 := hP.refinement hT.measurable 1
    have hQ1 := hQ.refinement hT.measurable 1
    have hS := hT.iterate n
    have hPn1 := hP1.preimage hS.measurable
    have hQn1 := hQ1.preimage hS.measurable
    have e1 : condEntropy μ (refinement T P (n + 1)) (refinement T Q (n + 1)) =
        condEntropy μ (partitionJoin (refinement T P n) (fun v ↦ T^[n] ⁻¹' refinement T P 1 v))
          (partitionJoin (refinement T Q n) (fun v ↦ T^[n] ⁻¹' refinement T Q 1 v)) :=
      (condEntropy_congr_equiv μ (Fin.appendEquiv n 1) (Fin.appendEquiv n 1)
        (fun uv ↦ (refinement_append T P uv.1 uv.2).symm)
        (fun uv ↦ (refinement_append T Q uv.1 uv.2).symm)).symm
    have h2 := condEntropy_join_le μ hPn hPn1 (hQn.join hQn1)
    have h3 := condEntropy_le_of_refines μ hPn (hQn.join hQn1) hQn
      (fun ij ↦ ⟨ij.1, Set.inter_subset_left⟩)
    have h4 := condEntropy_le_of_refines μ hPn1 (hQn.join hQn1) hQn1
      (fun ij ↦ ⟨ij.2, Set.inter_subset_right⟩)
    have h5 : condEntropy μ (fun v ↦ T^[n] ⁻¹' refinement T P 1 v)
        (fun v ↦ T^[n] ⁻¹' refinement T Q 1 v) = condEntropy μ P Q := by
      rw [condEntropy_preimage hS hP1.measurableSet hQ1.measurableSet, h1]
    rw [e1]
    push_cast
    linarith

/-- `H_μ(P^n) ≤ H_μ(Q^n) + n H_μ(P | Q)` for an invariant measure and `n ≥ 1`. -/
private lemma refinementEntropy_le_add_mul [Fintype ι] [DecidableEq ι] [Fintype κ]
    [DecidableEq κ] {μ : Measure X} [IsProbabilityMeasure μ] {T : X → X}
    (hT : MeasurePreserving T μ μ) {P : ι → Set X} {Q : κ → Set X}
    (hP : IsMeasurablePartition P) (hQ : IsMeasurablePartition Q) {n : ℕ} (hn : 1 ≤ n) :
    refinementEntropy μ T P n ≤ refinementEntropy μ T Q n + n * condEntropy μ P Q := by
  have h1 := condEntropy_nonneg μ (hQ.refinement hT.measurable n)
    (hP.refinement hT.measurable n)
  have h2 := condEntropy_refinement_le hT hP hQ hn
  unfold condEntropy at h1 h2
  rw [partitionEntropy_join_comm] at h1
  unfold refinementEntropy condEntropy
  linarith

/-- Walters, Theorem 4.12(iv): `h_μ(T, P) ≤ h_μ(T, Q) + H_μ(P | Q)`.
Blueprint node `erg:partition-entropy`. -/
theorem entropyRate_le_add_condEntropy [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    {μ : Measure X} [IsProbabilityMeasure μ] {T : X → X}
    (hT : MeasurePreserving T μ μ) {P : ι → Set X} {Q : κ → Set X}
    (hP : IsMeasurablePartition P) (hQ : IsMeasurablePartition Q) :
    entropyRate μ T P ≤ entropyRate μ T Q + ENNReal.ofReal (condEntropy μ P Q) := by
  refine le_of_tendsto_of_tendsto (tendsto_refinementEntropy_div hT hP)
    ((tendsto_refinementEntropy_div hT hQ).add tendsto_const_nhds)
    (eventually_atTop.2 ⟨1, fun n hn ↦ ?_⟩)
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  refine (ENNReal.ofReal_le_ofReal ?_).trans ENNReal.ofReal_add_le
  rw [div_le_iff₀ hnpos, add_mul, div_mul_cancel₀ _ hnpos.ne']
  have := refinementEntropy_le_add_mul hT hP hQ hn
  linarith

end Properties

end Kolmogorov.Ergodic
