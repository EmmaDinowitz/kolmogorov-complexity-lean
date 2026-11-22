/-
Copyright (c) 2026 Emma Dinowitz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emma Dinowitz
-/
import KolmogorovMathlib.PointToSet.Measure.Ergodic.HoyrupCondInfo

/-!
# Chung's lemma for the conditional information

Lemma 4.2 of Hoyrup (STACS 2012; Petersen, *Ergodic Theory*, Corollary 2.2, p. 261): for a
shift-invariant probability measure `ν` on `ℕ → Bool`, `f* = sup_j condInfo ν j` is integrable.

Proof. For a symbol `a` and `λ > 0`, let `τ` be the first `j` with
`ν[a x₁ … x_j] < 2^{-λ} ν[x₁ … x_j]`. The words `x₁ … x_τ` at which `τ` stops form a prefix-free set
`S`, so `ν{x₀ = a, f* > λ} ≤ ∑_{v ∈ S} ν[a v] ≤ 2^{-λ} ∑_{v ∈ S} ν[v] ≤ 2^{-λ}`, using invariance
(`ν[v] = ν(σ^{-1}[v])`) and disjointness. Hence `ν{f* > λ} ≤ 2 · 2^{-λ}` and
`∫ f* ≤ ∫_0^∞ min(1, 2^{1-λ}) dλ < ∞`.

In Lean, `λ = m` ranges over `ℕ`; the stopping words are the first-hit sets `chungFirst`
(sequences `y` whose prefix `y↾j` is the first one with `ν[a (y↾j)] < 2^{-m} ν[y↾j]`), and the
layer cake is discrete: `t ≤ ∑_{m ∈ ℕ} 1[m < t]`, so `∫ f* ≤ ∑_m 2 · 2^{-m} = 4`.

Blueprint node `erg:hoyrup`.
-/

namespace Kolmogorov.PointToSet

open Filter Set MeasureTheory
open scoped Topology ENNReal Computability

/-- Prefixes of prefixes: `(y↾j).take i = y↾i` for `i ≤ j`. -/
private lemma chung_take_wordPrefix (y : ℕ → Bool) {i j : ℕ} (hij : i ≤ j) :
    (wordPrefix y j).take i = wordPrefix y i := by
  apply List.ext_getElem
  · simp [wordPrefix, hij]
  · intro k h1 h2
    simp [wordPrefix]


/-- The stopping condition of Chung's argument at a word `v`:
`-log₂ (ν[a v] / ν[v]) > m`. -/
private def chungHit (ν : Measure (ℕ → Bool)) (m : ℕ) (a : Bool) (v : List Bool) : Prop :=
  (m : ℝ≥0∞) < infoBits (ν (listCylinder (a :: v)) / ν (listCylinder v))

/-- The sequences `y` whose prefix of length `j` is the first prefix at which `chungHit` holds. -/
private def chungFirst (ν : Measure (ℕ → Bool)) (m : ℕ) (a : Bool) (j : ℕ) :
    Set (ℕ → Bool) :=
  {y | chungHit ν m a (wordPrefix y j) ∧ ∀ i < j, ¬ chungHit ν m a (wordPrefix y i)}

/-- At a stopping word, `ν[a v] ≤ 2^{-m} ν[v]`. -/
private lemma chungHit_le {ν : Measure (ℕ → Bool)} [IsProbabilityMeasure ν]
    (hν : MeasurePreserving shiftMap ν ν) {m : ℕ} {a : Bool} {v : List Bool}
    (h : chungHit ν m a v) :
    ν (listCylinder (a :: v)) ≤ (2 : ℝ≥0∞)⁻¹ ^ m * ν (listCylinder v) := by
  have hq : ν (listCylinder (a :: v)) / ν (listCylinder v) < (2 : ℝ≥0∞)⁻¹ ^ m := by
    by_contra hc
    exact not_lt.2 ((infoBits_antitone (not_lt.1 hc)).trans
      (infoBits_two_inv_pow m).le) h
  rcases eq_or_ne (ν (listCylinder v)) 0 with h0 | h0
  · have hsub : listCylinder (a :: v) ⊆ shiftMap ⁻¹' listCylinder v := by
      intro y hy i hi
      have := hy (i + 1) (by simp [hi])
      simpa [shiftMap] using this
    have hle := measure_mono (μ := ν) hsub
    rw [hν.measure_preimage (measurableSet_listCylinder v).nullMeasurableSet, h0] at hle
    simp [nonpos_iff_eq_zero.1 hle]
  · exact ((ENNReal.div_lt_iff (Or.inl h0) (Or.inl (measure_ne_top _ _))).1 hq).le

/-- The first-hit sets are pairwise disjoint. -/
private lemma pairwise_disjoint_chungFirst (ν : Measure (ℕ → Bool)) (m : ℕ) (a : Bool) :
    Pairwise (Function.onFun Disjoint (chungFirst ν m a)) := by
  intro j k hjk
  rw [Function.onFun, Set.disjoint_left]
  intro y hj hk
  rcases lt_or_gt_of_ne hjk with h | h
  · exact hk.2 j h hj.1
  · exact hj.2 k h hk.1

/-- The first-hit set at time `j` only depends on the first `j` symbols. -/
private lemma chungFirst_eq_preimage (ν : Measure (ℕ → Bool)) (m : ℕ) (a : Bool) (j : ℕ) :
    chungFirst ν m a j = (fun (y : ℕ → Bool) (i : Fin j) ↦ y i) ⁻¹'
      {w | chungHit ν m a (List.ofFn w) ∧
        ∀ i < j, ¬ chungHit ν m a ((List.ofFn w).take i)} := by
  ext y
  have hy : List.ofFn (fun i : Fin j ↦ y i) = wordPrefix y j := rfl
  simp only [chungFirst, mem_ofPred_eq, mem_preimage, hy]
  refine ⟨fun h ↦ ⟨h.1, fun i hi ↦ ?_⟩, fun h ↦ ⟨h.1, fun i hi ↦ ?_⟩⟩
  · rw [chung_take_wordPrefix y hi.le]
    exact h.2 i hi
  · have := h.2 i hi
    rwa [chung_take_wordPrefix y hi.le] at this

/-- The first-hit sets are measurable. -/
private lemma measurableSet_chungFirst (ν : Measure (ℕ → Bool)) (m : ℕ) (a : Bool) (j : ℕ) :
    MeasurableSet (chungFirst ν m a j) := by
  rw [chungFirst_eq_preimage]
  exact (Measurable.of_eval fun i ↦ measurable_pi_apply _) (Set.toFinite _).measurableSet

/-- `ν({x₀ = a} ∩ σ⁻¹ F_j) ≤ 2^{-m} ν(F_j)` for the first-hit set `F_j`. -/
private lemma measure_inter_preimage_chungFirst_le {ν : Measure (ℕ → Bool)}
    [IsProbabilityMeasure ν] (hν : MeasurePreserving shiftMap ν ν) (m : ℕ) (a : Bool)
    (j : ℕ) :
    ν ({x | x 0 = a} ∩ shiftMap ⁻¹' chungFirst ν m a j) ≤
      (2 : ℝ≥0∞)⁻¹ ^ m * ν (chungFirst ν m a j) := by
  classical
  set φ : (ℕ → Bool) → Fin j → Bool := fun y i ↦ y i with hφdef
  set S : Set (Fin j → Bool) := {w | chungHit ν m a (List.ofFn w) ∧
    ∀ i < j, ¬ chungHit ν m a ((List.ofFn w).take i)} with hSdef
  set Sf : Finset (Fin j → Bool) := Finset.univ.filter (· ∈ S) with hSfdef
  have hS : (Sf : Set (Fin j → Bool)) = S := by simp [Sf]
  have hφ : Measurable φ := Measurable.of_eval fun i ↦ measurable_pi_apply _
  have hσ : Measurable (shiftMap : (ℕ → Bool) → ℕ → Bool) :=
    Measurable.of_eval fun i ↦ measurable_pi_apply _
  have hB : MeasurableSet {x : ℕ → Bool | x 0 = a} :=
    show MeasurableSet ((fun x : ℕ → Bool ↦ x 0) ⁻¹' {a}) from
      measurable_pi_apply 0 (measurableSet_singleton a)
  have hcyl : ∀ w : Fin j → Bool,
      (φ ∘ shiftMap) ⁻¹' {w} ∩ {x | x 0 = a} = listCylinder (a :: List.ofFn w) := by
    intro w
    rw [← List.ofFn_cons, listCylinder_ofFn]
    ext x
    simp [wordCylinder, Fin.forall_fin_succ, funext_iff, φ, shiftMap, and_comm, eq_comm]
  have hcyl' : ∀ w : Fin j → Bool, φ ⁻¹' {w} = listCylinder (List.ofFn w) := by
    intro w
    rw [listCylinder_ofFn]
    ext y
    simp [wordCylinder, funext_iff, φ, eq_comm]
  rw [chungFirst_eq_preimage, ← hSdef]
  calc ν ({x | x 0 = a} ∩ shiftMap ⁻¹' (φ ⁻¹' S))
      = ν.restrict {x | x 0 = a} ((φ ∘ shiftMap) ⁻¹' ↑Sf) := by
        rw [Measure.restrict_apply' hB, hS, inter_comm]
        rfl
    _ = ∑ w ∈ Sf, ν.restrict {x | x 0 = a} ((φ ∘ shiftMap) ⁻¹' {w}) :=
        (sum_measure_preimage_singleton _ fun w _ ↦
          (hφ.comp hσ) (measurableSet_singleton w)).symm
    _ = ∑ w ∈ Sf, ν (listCylinder (a :: List.ofFn w)) :=
        Finset.sum_congr rfl fun w _ ↦ by rw [Measure.restrict_apply' hB, hcyl]
    _ ≤ ∑ w ∈ Sf, (2 : ℝ≥0∞)⁻¹ ^ m * ν (listCylinder (List.ofFn w)) :=
        Finset.sum_le_sum fun w hw ↦ chungHit_le hν (Finset.mem_filter.1 hw).2.1
    _ = (2 : ℝ≥0∞)⁻¹ ^ m * ∑ w ∈ Sf, ν (φ ⁻¹' {w}) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun w _ ↦ by rw [hcyl']
    _ = (2 : ℝ≥0∞)⁻¹ ^ m * ν (φ ⁻¹' S) := by
        rw [sum_measure_preimage_singleton _ fun w _ ↦ hφ (measurableSet_singleton w), hS]

/-- The key estimate of Chung's lemma: `ν{x₀ = a, sup_j condInfo ν j > m} ≤ 2^{-m}`. -/
private lemma measure_fst_eq_lt_iSup_condInfo_le {ν : Measure (ℕ → Bool)}
    [IsProbabilityMeasure ν] (hν : MeasurePreserving shiftMap ν ν) (m : ℕ) (a : Bool) :
    ν {x | x 0 = a ∧ (m : ℝ≥0∞) < ⨆ j, condInfo ν j x} ≤ (2 : ℝ≥0∞)⁻¹ ^ m := by
  classical
  have hsub : {x | x 0 = a ∧ (m : ℝ≥0∞) < ⨆ j, condInfo ν j x} ⊆
      ⋃ j, {x | x 0 = a} ∩ shiftMap ⁻¹' chungFirst ν m a j := by
    rintro x ⟨hx0, hx⟩
    obtain ⟨j, hj⟩ := lt_iSup_iff.1 hx
    have hP : ∃ j, chungHit ν m a (wordPrefix (shiftMap x) j) := by
      refine ⟨j, ?_⟩
      rw [condInfo, wordPrefix_succ, hx0] at hj
      exact hj
    exact mem_iUnion.2 ⟨Nat.find hP, hx0, Nat.find_spec hP, fun i hi ↦ Nat.find_min hP hi⟩
  calc ν {x | x 0 = a ∧ (m : ℝ≥0∞) < ⨆ j, condInfo ν j x}
      ≤ ν (⋃ j, {x | x 0 = a} ∩ shiftMap ⁻¹' chungFirst ν m a j) := measure_mono hsub
    _ ≤ ∑' j, ν ({x | x 0 = a} ∩ shiftMap ⁻¹' chungFirst ν m a j) := measure_iUnion_le _
    _ ≤ ∑' j, (2 : ℝ≥0∞)⁻¹ ^ m * ν (chungFirst ν m a j) :=
        ENNReal.tsum_le_tsum fun j ↦ measure_inter_preimage_chungFirst_le hν m a j
    _ = (2 : ℝ≥0∞)⁻¹ ^ m * ν (⋃ j, chungFirst ν m a j) := by
        rw [ENNReal.tsum_mul_left,
          measure_iUnion (pairwise_disjoint_chungFirst ν m a) (measurableSet_chungFirst ν m a)]
    _ ≤ (2 : ℝ≥0∞)⁻¹ ^ m * 1 := by gcongr; exact prob_le_one
    _ = (2 : ℝ≥0∞)⁻¹ ^ m := mul_one _

/-- Discrete layer cake: `t ≤ ∑_{m ∈ ℕ} 1[m < t]` for every `t ∈ [0, ∞]`. -/
private lemma chung_le_tsum_indicator (t : ℝ≥0∞) :
    t ≤ ∑' m : ℕ, if (m : ℝ≥0∞) < t then 1 else 0 := by
  have key : ∀ k : ℕ, (∀ m < k, (m : ℝ≥0∞) < t) →
      (k : ℝ≥0∞) ≤ ∑' m : ℕ, if (m : ℝ≥0∞) < t then 1 else 0 := by
    intro k hk
    refine le_trans ?_ (ENNReal.sum_le_tsum (Finset.range k))
    have h1 : ∀ m ∈ Finset.range k, (if (m : ℝ≥0∞) < t then (1 : ℝ≥0∞) else 0) = 1 :=
      fun m hm ↦ by simp [hk m (Finset.mem_range.1 hm)]
    rw [Finset.sum_congr rfl h1]
    simp
  rcases eq_or_ne t ⊤ with rfl | ht
  · have hall : ∀ m : ℕ, (if (m : ℝ≥0∞) < ⊤ then (1 : ℝ≥0∞) else 0) = 1 := fun m ↦
      by simp
    simp only [hall, ENNReal.tsum_const_eq_top_of_ne_zero one_ne_zero, le_refl]
  · refine le_trans ?_ (key ⌈t.toReal⌉₊ fun m hm ↦ ?_)
    · calc t = ENNReal.ofReal t.toReal := (ENNReal.ofReal_toReal ht).symm
        _ ≤ ENNReal.ofReal (⌈t.toReal⌉₊ : ℝ) := ENNReal.ofReal_le_ofReal (Nat.le_ceil _)
        _ = (⌈t.toReal⌉₊ : ℝ≥0∞) := ENNReal.ofReal_natCast _
    · exact (ENNReal.toReal_lt_toReal (ENNReal.natCast_ne_top m) ht).1
        (by simpa using Nat.lt_ceil.1 hm)

/-- Chung's lemma: `∫ sup_j condInfo ν j dν < ∞` for a shift-invariant probability measure.
Blueprint node `erg:hoyrup`. -/
theorem lintegral_iSup_condInfo_lt_top {ν : Measure (ℕ → Bool)} [IsProbabilityMeasure ν]
    (hν : MeasurePreserving shiftMap ν ν) : ∫⁻ x, ⨆ j, condInfo ν j x ∂ν < ⊤ := by
  set f : (ℕ → Bool) → ℝ≥0∞ := fun x ↦ ⨆ j, condInfo ν j x with hfdef
  have hf : Measurable f := Measurable.iSup fun j ↦ measurable_condInfo ν j
  have hm : ∀ m : ℕ, ν {x | (m : ℝ≥0∞) < f x} ≤ 2 * (2 : ℝ≥0∞)⁻¹ ^ m := by
    intro m
    calc ν {x | (m : ℝ≥0∞) < f x}
        ≤ ν ({x | x 0 = true ∧ (m : ℝ≥0∞) < f x} ∪ {x | x 0 = false ∧ (m : ℝ≥0∞) < f x}) :=
          measure_mono fun x hx ↦ by
            cases h : x 0
            · exact Or.inr ⟨h, hx⟩
            · exact Or.inl ⟨h, hx⟩
      _ ≤ ν {x | x 0 = true ∧ (m : ℝ≥0∞) < f x} + ν {x | x 0 = false ∧ (m : ℝ≥0∞) < f x} :=
          measure_union_le _ _
      _ ≤ (2 : ℝ≥0∞)⁻¹ ^ m + (2 : ℝ≥0∞)⁻¹ ^ m :=
          add_le_add (measure_fst_eq_lt_iSup_condInfo_le hν m true)
            (measure_fst_eq_lt_iSup_condInfo_le hν m false)
      _ = 2 * (2 : ℝ≥0∞)⁻¹ ^ m := (two_mul _).symm
  calc ∫⁻ x, f x ∂ν
      ≤ ∫⁻ x, ∑' m : ℕ, {x | (m : ℝ≥0∞) < f x}.indicator 1 x ∂ν := by
        refine lintegral_mono fun x ↦ ?_
        simpa only [Set.indicator_apply, mem_ofPred_eq, Pi.one_apply] using
          chung_le_tsum_indicator (f x)
    _ = ∑' m : ℕ, ν {x | (m : ℝ≥0∞) < f x} := by
        rw [lintegral_tsum fun m ↦ (measurable_one.indicator
          (measurableSet_lt measurable_const hf)).aemeasurable]
        exact tsum_congr fun m ↦ lintegral_indicator_one (measurableSet_lt measurable_const hf)
    _ ≤ ∑' m : ℕ, 2 * (2 : ℝ≥0∞)⁻¹ ^ m := ENNReal.tsum_le_tsum hm
    _ = 4 := by
        rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric, ENNReal.one_sub_inv_two, inv_inv]
        norm_num
    _ < ⊤ := by simp

end Kolmogorov.PointToSet
