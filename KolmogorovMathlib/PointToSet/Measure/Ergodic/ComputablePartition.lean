/-
Copyright (c) 2026 Emma Dinowitz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emma Dinowitz
-/
import KolmogorovMathlib.PointToSet.Measure.Ergodic.NullSphere
import KolmogorovMathlib.Ergodic.PartitionEntropy

/-!
# Computable partitions (Lemma 2)

Lemma 2 of the note *Orbit complexity of Martin-Löf random points equals entropy*: on a compact
space with an `A`-computable presentation and an `A`-computable probability measure `μ`, for every
`ε > 0` there are pairwise disjoint `A`-effectively open sets `U_1, …, U_p` of diameter `< ε` with
`μ(U_1 ∪ ⋯ ∪ U_p) = 1`.

* `IsComputablePartitionIn P A μ U`: `U : Fin p → Set X` is a uniformly `A`-c.e. open, pairwise
  disjoint family whose union has null complement.
* `exists_computablePartition` (Lemma 2). Proof: take a radius `r = r_m < ε/2` from
  `exists_nullSphere_radii`, cover `X` by finitely many balls `B(x_i, r)`, `i < p`
  (compactness), and put `U_i = B(x_i, r) ∩ ⋂_{l<i} {d(·, x_l) > r}`. The complement of `⋃ U_i`
  lies in the union of the spheres `{d(·, x_l) = r}`, `l < p`. The statement also returns a
  genuine measurable partition `Q` with `U_j ⊆ Q_j` and cells of diameter `< ε` (adjoin each
  point of the null remainder to the first `Q_i` with `d(y, x_i) ≤ r`, i.e.
  `Q_i = {d(·, x_i) ≤ r} ∩ ⋂_{l<i} {d(·, x_l) > r}`); since `μ(Q_j \ U_j) = 0`
  (`ae_eq_of_isComputablePartitionIn`), entropy computed from `Q` is entropy computed from `U`.

Blueprint node `erg:computable-partition`.
-/

namespace Kolmogorov.PointToSet

open Filter Set MeasureTheory
open scoped Topology ENNReal Computability

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

/-- A uniformly `A`-c.e. open, pairwise disjoint finite family whose union has `μ`-null
complement. Blueprint node `erg:computable-partition`. -/
def IsComputablePartitionIn (P : Presentation X) (A : Set ℕ) (μ : Measure X) {p : ℕ}
    (U : Fin p → Set X) : Prop :=
  IsCeOpenFamilyIn P A U ∧ Pairwise (Function.onFun Disjoint U) ∧ μ (⋃ j, U j)ᶜ = 0

omit [MeasurableSpace X] [BorelSpace X] in
/-- The cells `S_j ∩ ⋂_{l<j} {d(·, x_l) > ρ}` with `S_j ⊆ closedBall(x_j, ρ)` (the open and the
closed cells of Lemma 2) are pairwise disjoint. -/
private lemma pairwise_disjoint_cells {P : Presentation X} {ρ : ℝ} {p : ℕ} {S : ℕ → Set X}
    (hS : ∀ j, S j ⊆ Metric.closedBall (P.ι j) ρ) :
    Pairwise (Function.onFun Disjoint fun j : Fin p ↦
      S j ∩ ⋂ l ∈ List.range j, {y | ρ < dist y (P.ι l)}) := by
  -- the cell of the larger index avoids the closed ball of the smaller one
  have key : ∀ j j' : Fin p, (j : ℕ) < j' → Disjoint
      (S j ∩ ⋂ l ∈ List.range j, {y | ρ < dist y (P.ι l)})
      (S j' ∩ ⋂ l ∈ List.range j', {y | ρ < dist y (P.ι l)}) := by
    intro j j' hjj'
    refine Set.disjoint_left.mpr fun y hy hy' ↦ ?_
    have h1 : dist y (P.ι j) ≤ ρ := hS j hy.1
    have h2 : ρ < dist y (P.ι j) := mem_iInter₂.mp hy'.2 j (List.mem_range.mpr hjj')
    linarith
  intro j j' hne
  rcases lt_or_gt_of_ne (Fin.val_injective.ne hne) with h | h
  · exact key j j' h
  · exact (key j' j h).symm

/-- Lemma 2: for every `ε > 0` there is an `A`-computable partition into pieces of diameter
`< ε`, together with a measurable partition `Q` that contains it cellwise and has cells of
diameter `< ε`. Blueprint node `erg:computable-partition`. -/
theorem exists_computablePartition [CompactSpace X] [Nonempty X] (P : Presentation X)
    (A : Set ℕ) (μ : Measure X) [IsProbabilityMeasure μ] (hP : ComputablePresentationIn P A)
    (hμ : IsComputableMeasureIn P A μ) {ε : ℝ} (hε : 0 < ε) :
    ∃ (p : ℕ) (U Q : Fin p → Set X), 0 < p ∧ IsComputablePartitionIn P A μ U ∧
      Ergodic.IsMeasurablePartition Q ∧ (∀ j, U j ⊆ Q j) ∧ ∀ j, Metric.diam (Q j) < ε := by
  obtain ⟨r, hr, hrpos, hrdense, hnull⟩ := exists_nullSphere_radii P A μ hP hμ
  obtain ⟨m, hm⟩ := hrdense (ε / 4) (ε / 2) (by positivity) (by linarith)
  have hρ : 0 < r m := hrpos m
  -- a finite cover by balls `B(x_j, r_m)`, `j < p`
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun i : ℕ ↦ Metric.ball (P.ι i) (r m))
    (fun _ ↦ Metric.isOpen_ball) fun y _ ↦ by
      obtain ⟨k, hk⟩ := Metric.denseRange_iff.mp P.dense y (r m) hρ
      exact mem_iUnion.mpr ⟨k, Metric.mem_ball.mpr hk⟩
  set p := t.sup id + 1 with hp
  have hcover : ∀ y, ∃ j < p, dist y (P.ι j) < r m := by
    intro y
    obtain ⟨j, hj, hy⟩ := mem_iUnion₂.mp (ht (mem_univ y))
    exact ⟨j, Nat.lt_succ_of_le (Finset.le_sup (f := id) hj), hy⟩
  let C : ℕ → Set X := fun j ↦ ⋂ l ∈ List.range j, {y | r m < dist y (P.ι l)}
  let U : Fin p → Set X := fun j ↦ Metric.ball (P.ι j) (r m) ∩ C j
  let Q : Fin p → Set X := fun j ↦ Metric.closedBall (P.ι j) (r m) ∩ C j
  have hmemC : ∀ y j, y ∈ C j ↔ ∀ l < j, r m < dist y (P.ι l) := by
    intro y j
    simp only [C, mem_iInter₂, List.mem_range, mem_ofPred_eq]
  -- the least index whose (closed) ball contains a point
  have hleast : ∀ y (R : ℕ → Prop) [DecidablePred R], (∃ j < p, R j) →
      (∀ l < p, ¬ R l → r m < dist y (P.ι l)) → ∃ j : Fin p, R j ∧ y ∈ C j := by
    intro y R _ hex hR
    have hex' : ∃ j, R j := ⟨hex.choose, hex.choose_spec.2⟩
    have hfind : Nat.find hex' < p :=
      (Nat.find_min' hex' hex.choose_spec.2).trans_lt hex.choose_spec.1
    exact ⟨⟨Nat.find hex', hfind⟩, Nat.find_spec hex', (hmemC y _).mpr fun l hl ↦
      hR l (hl.trans hfind) (Nat.find_min hex' hl)⟩
  refine ⟨p, U, Q, Nat.succ_pos _, ⟨?_, ?_, ?_⟩, ⟨fun j ↦ ?_, ?_, ?_⟩, fun j ↦ ?_, fun j ↦ ?_⟩
  · -- uniform c.e. openness
    have hball := (isCeOpenFamilyIn_ball_of_computableRadius P A hP hr).comp
      (g := fun j : ℕ ↦ (j, m)) (Computable.id.pair (Computable.const m))
    have hgt := ((isCeOpenFamilyIn_dist_gt_of_computableRadius P A hP hr).comp
      (g := fun w : ℕ × ℕ ↦ (w.2, w.1)) (Computable.snd.pair Computable.fst)).biInter_list hP
    have hC := hgt.comp (g := fun j : ℕ ↦ (m, List.range j))
      ((Computable.const m).pair Primrec.list_range.to_comp)
    exact ((hball.inter P A hP hC).comp (g := fun j : Fin p ↦ (j : ℕ)) Primrec.fin_val.to_comp)
  · exact pairwise_disjoint_cells fun j ↦ Metric.ball_subset_closedBall
  · -- the complement lies in finitely many null spheres
    refine measure_mono_null (t := ⋃ l ∈ Finset.range p, Metric.sphere (P.ι l) (r m)) ?_
      ((measure_biUnion_null_iff (Finset.range p).countable_toSet).mpr fun l _ ↦ hnull l m)
    intro y hy
    by_contra hy'
    simp only [mem_iUnion, Finset.mem_range, Metric.mem_sphere, not_exists] at hy'
    obtain ⟨j, hj, hyC⟩ := hleast y (fun j ↦ dist y (P.ι j) < r m) (hcover y)
      fun l hlp hl ↦ lt_of_le_of_ne (not_lt.mp hl) (Ne.symm (hy' l hlp))
    exact hy (mem_iUnion.mpr ⟨j, Metric.mem_ball.mpr hj, hyC⟩)
  · exact measurableSet_closedBall.inter (MeasurableSet.biInter
      (List.range j).finite_toSet.countable fun l _ ↦
        measurableSet_lt measurable_const (continuous_id.dist continuous_const).measurable)
  · exact pairwise_disjoint_cells fun j ↦ subset_rfl
  · refine eq_univ_of_forall fun y ↦ ?_
    obtain ⟨j, hj, hyC⟩ := hleast y (fun j ↦ dist y (P.ι j) ≤ r m)
      (by obtain ⟨j, hjp, hj⟩ := hcover y; exact ⟨j, hjp, hj.le⟩) fun l _ hl ↦ not_le.mp hl
    exact mem_iUnion.mpr ⟨j, Metric.mem_closedBall.mpr hj, hyC⟩
  · exact inter_subset_inter_left _ Metric.ball_subset_closedBall
  · calc Metric.diam (Q j) ≤ Metric.diam (Metric.closedBall (P.ι j) (r m)) :=
          Metric.diam_mono inter_subset_left Metric.isBounded_closedBall
      _ ≤ 2 * r m := Metric.diam_closedBall hρ.le
      _ < ε := by linarith [hm.2]

omit [BorelSpace X] in
/-- The cells of a measurable partition that contains a computable partition cellwise differ
from it by null sets. Blueprint node `erg:computable-partition`. -/
theorem ae_eq_of_isComputablePartitionIn {P : Presentation X} {A : Set ℕ} {μ : Measure X}
    {p : ℕ} {U Q : Fin p → Set X} (hU : IsComputablePartitionIn P A μ U)
    (hQ : Ergodic.IsMeasurablePartition Q) (hUQ : ∀ j, U j ⊆ Q j) (j : Fin p) :
    U j =ᵐ[μ] Q j := by
  refine ae_eq_set.mpr ⟨by rw [sdiff_eq_empty.mpr (hUQ j), measure_empty], ?_⟩
  refine measure_mono_null (fun y hy ↦ ?_) hU.2.2
  rintro hyU
  obtain ⟨l, hl⟩ := mem_iUnion.mp hyU
  rcases eq_or_ne l j with rfl | hne
  · exact hy.2 hl
  · exact Set.disjoint_left.mp (hQ.disjoint hne) (hUQ l hl) hy.1

end Kolmogorov.PointToSet
