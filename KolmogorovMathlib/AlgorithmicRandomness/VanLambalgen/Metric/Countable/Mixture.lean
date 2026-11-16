/-
Copyright (c) 2026 Emma Dinowitz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emma Dinowitz
-/
import KolmogorovMathlib.AlgorithmicRandomness.VanLambalgen.Metric.Countable.Basic
import KolmogorovMathlib.PointToSet.Measure.Computable

/-!
# Uniformly computable sequences of measures and their mixture

A member of a uniformly computable sequence of measures is computable
(`IsComputableMeasureFamilyIn.isComputableMeasureIn`), and a probability measure has computable
total mass (`isComputableRealFamilyIn_measure_univ`). The mixture `∑ᵢ 2^{-(i+1)} μ i` of
probability measures is a probability measure (`isProbabilityMeasure_mixMeasure`), computable when
the sequence is uniformly computable (`IsComputableMeasureFamilyIn.isComputableMeasureIn_mix`),
and an almost decidable basis of the mixture is one of every member, with the boundary covers
shifted by `i + 1` levels (`IsAlmostDecidableBasisIn.of_mixMeasure`).

## Main declarations

* `IsComputableMeasureFamilyIn.isComputableMeasureIn`, `isComputableRealFamilyIn_measure_univ`
  (blueprint node `vlm:measure-family`).
* `isProbabilityMeasure_mixMeasure`, `IsComputableMeasureFamilyIn.isComputableMeasureIn_mix`,
  `IsAlmostDecidableBasisIn.of_mixMeasure` (blueprint node `vlm:mix`).

Used by `Metric/Countable/MainResults.lean`.
-/

namespace Kolmogorov.PointToSet

open MeasureTheory
open scoped Computability ENNReal

attribute [local instance] PiCountable.metricSpace

variable {X : Type*} [MetricSpace X] {P : Presentation X} {A : Set ℕ}
  [MeasurableSpace X] {μ : ℕ → Measure X} {B : ℕ → Set X}

/-! ### Weighted partial sums of rational lower bounds -/

/-- The weighted partial sum `∑_{k < length} l[k] 2^{-(k+1)}` of a list of rationals. -/
private def mixPartialSum (l : List ℚ) : ℚ :=
  ∑ k ∈ Finset.range l.length, l.getD k 0 * (2 ^ (k + 1) : ℚ)⁻¹

private theorem natRec_add_eq_sum_range (N : ℕ) (f : ℕ → ℚ) :
    Nat.rec (motive := fun _ => ℚ) 0 (fun n acc => acc + f n) N =
      ∑ n ∈ Finset.range N, f n := by
  induction N with
  | zero => simp
  | succ N ih =>
      have hstep : Nat.rec (motive := fun _ => ℚ) 0 (fun n acc => acc + f n) (N + 1) =
          Nat.rec (motive := fun _ => ℚ) 0 (fun n acc => acc + f n) N + f N := rfl
      rw [hstep, Finset.sum_range_succ, ih]

private theorem computable_mixPartialSum : Computable mixPartialSum := by
  have hf := computable₂_ratMul.comp (Primrec.list_getD (0 : ℚ)).to_comp
    (computable_rat_inv_two_pow.comp (Computable.succ.comp Computable.snd))
  have hstep := (computable₂_ratAdd.comp (Computable.snd.comp Computable.snd)
    (hf.comp (Computable.pair Computable.fst (Computable.fst.comp Computable.snd)))).to₂
  refine (Computable.nat_rec Computable.list_length (Computable.const (0 : ℚ)) hstep).of_eq
    fun l => ?_
  exact natRec_add_eq_sum_range l.length fun k => l.getD k 0 * (2 ^ (k + 1) : ℚ)⁻¹

/-- A rational lies below `∑ᵢ 2^{-(i+1)} aᵢ` (with `0 ≤ aᵢ ≤ 1`) iff it lies below the weighted
partial sum of some finite list of rational strict lower bounds of the `aᵢ`. -/
private theorem lt_tsum_iff_exists_list {a : ℕ → ℝ} (ha0 : ∀ i, 0 ≤ a i) (ha1 : ∀ i, a i ≤ 1)
    (q : ℚ) :
    (q : ℝ) < ∑' i, (2⁻¹ : ℝ) ^ (i + 1) * a i ↔
      ∃ l : List ℚ, (∀ k (h : k < l.length), ((l.get ⟨k, h⟩ : ℚ) : ℝ) < a k) ∧
        q < mixPartialSum l := by
  have hw : Summable fun i : ℕ => (2⁻¹ : ℝ) ^ (i + 1) :=
    ((summable_geometric_of_lt_one (r := (2⁻¹ : ℝ)) (by norm_num) (by norm_num)).mul_left
      2⁻¹).congr fun i => (pow_succ' _ _).symm
  have hwt : ∑' i : ℕ, (2⁻¹ : ℝ) ^ (i + 1) = 1 := by
    simp_rw [pow_succ']
    rw [tsum_mul_left, tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
    norm_num
  have hwn : ∀ i : ℕ, 0 ≤ (2⁻¹ : ℝ) ^ (i + 1) := fun i => by positivity
  have hs : Summable fun i => (2⁻¹ : ℝ) ^ (i + 1) * a i :=
    Summable.of_nonneg_of_le (fun i => mul_nonneg (hwn i) (ha0 i))
      (fun i => mul_le_of_le_one_right (hwn i) (ha1 i)) hw
  have hcast : ∀ l : List ℚ, ((mixPartialSum l : ℚ) : ℝ) =
      ∑ k ∈ Finset.range l.length, ((l.getD k 0 : ℚ) : ℝ) * (2⁻¹ : ℝ) ^ (k + 1) := by
    intro l
    simp [mixPartialSum, inv_pow]
  constructor
  · intro hq
    have hlim : Filter.Tendsto
        (fun n => ∑ i ∈ Finset.range n, (2⁻¹ : ℝ) ^ (i + 1) * a i) Filter.atTop
        (nhds (∑' i, (2⁻¹ : ℝ) ^ (i + 1) * a i)) := hs.hasSum.tendsto_sum_nat
    obtain ⟨N, hN⟩ := ((tendsto_order.1 hlim).1
      ((∑' i, (2⁻¹ : ℝ) ^ (i + 1) * a i) - ((∑' i, (2⁻¹ : ℝ) ^ (i + 1) * a i) - q) / 2)
      (by linarith)).exists
    have hex : ∀ k, ∃ r : ℚ,
        a k - ((∑' i, (2⁻¹ : ℝ) ^ (i + 1) * a i) - q) / 2 < r ∧ (r : ℝ) < a k :=
      fun k => exists_rat_btwn (by linarith)
    choose g hg using hex
    refine ⟨(List.range N).map g, fun k hk => ?_, ?_⟩
    · simpa using (hg k).2
    · rw [← Rat.cast_lt (K := ℝ), hcast]
      set ε := (∑' i, (2⁻¹ : ℝ) ^ (i + 1) * a i) - q with hε
      have h1 : ∑ k ∈ Finset.range N, (2⁻¹ : ℝ) ^ (k + 1) ≤ 1 :=
        (hw.sum_le_tsum _ fun i _ => hwn i).trans_eq hwt
      have h2 : ∑ k ∈ Finset.range N, (a k - ε / 2) * (2⁻¹ : ℝ) ^ (k + 1) ≤
          ∑ k ∈ Finset.range ((List.range N).map g).length,
            ((((List.range N).map g).getD k 0 : ℚ) : ℝ) * (2⁻¹ : ℝ) ^ (k + 1) := by
        rw [List.length_map, List.length_range]
        refine Finset.sum_le_sum fun k hk => ?_
        have hk' : k < ((List.range N).map g).length := by simpa using hk
        rw [List.getD_eq_getElem _ _ hk']
        simp only [List.getElem_map, List.getElem_range]
        exact mul_le_mul_of_nonneg_right (hg k).1.le (hwn k)
      have h3 : ∑ k ∈ Finset.range N, (a k - ε / 2) * (2⁻¹ : ℝ) ^ (k + 1) =
          ∑ k ∈ Finset.range N, (2⁻¹ : ℝ) ^ (k + 1) * a k -
            ε / 2 * ∑ k ∈ Finset.range N, (2⁻¹ : ℝ) ^ (k + 1) := by
        rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun k _ => by ring
      have h4 : ε / 2 * ∑ k ∈ Finset.range N, (2⁻¹ : ℝ) ^ (k + 1) ≤ ε / 2 :=
        mul_le_of_le_one_right (by linarith) h1
      linarith
  · rintro ⟨l, hl, hq⟩
    rw [← Rat.cast_lt (K := ℝ), hcast] at hq
    refine hq.trans_le (le_trans ?_ (hs.sum_le_tsum (Finset.range l.length)
      fun i _ => mul_nonneg (hwn i) (ha0 i)))
    refine Finset.sum_le_sum fun k hk => ?_
    have hk' : k < l.length := Finset.mem_range.1 hk
    rw [List.getD_eq_getElem _ _ hk', mul_comm]
    exact mul_le_mul_of_nonneg_left (by simpa using (hl k hk').le) (hwn k)

omit [MetricSpace X] in
/-- The mixture's measure of a set, as a real number, is the weighted sum of the members'. -/
private theorem mixMeasure_apply_toReal [∀ i, IsProbabilityMeasure (μ i)] (s : Set X) :
    (mixMeasure μ s).toReal = ∑' i, (2⁻¹ : ℝ) ^ (i + 1) * (μ i s).toReal := by
  rw [mixMeasure, Measure.sum_apply_of_countable, ENNReal.tsum_toReal_eq]
  · simp [ENNReal.toReal_mul]
  · intro i
    rw [Measure.smul_apply, smul_eq_mul]
    exact ENNReal.mul_ne_top (ENNReal.pow_ne_top (ENNReal.inv_ne_top.2 two_ne_zero))
      (measure_ne_top _ _)

/-! ### Main results -/

/-- A member of a uniformly computable sequence of measures is computable.
Blueprint node `vlm:measure-family`. -/
theorem IsComputableMeasureFamilyIn.isComputableMeasureIn (hμ : IsComputableMeasureFamilyIn P A μ)
    (i : ℕ) : IsComputableMeasureIn P A (μ i) :=
  IsREIn.comp hμ (f := fun w : List (ℕ × ℚ) × ℚ => ((i, w.1), w.2))
    (Computable.pair (Computable.pair (Computable.const i) Computable.fst)
      Computable.snd).computableIn

omit [MetricSpace X] in
/-- The total mass of a probability measure is computable relative to every oracle.
Blueprint node `vlm:measure-family`. -/
theorem isComputableRealFamilyIn_measure_univ (ν : Measure X) [IsProbabilityMeasure ν] :
    IsComputableRealFamilyIn A fun _ : Unit => (ν Set.univ).toReal := by
  refine ⟨fun _ => 1, (Computable.const (1 : ℚ)).computableIn, fun _ p => ?_⟩
  simp only [measure_univ, ENNReal.toReal_one, Rat.cast_one, sub_self, abs_zero]
  positivity

/-- The mixture of probability measures is a probability measure. Blueprint node `vlm:mix`. -/
instance isProbabilityMeasure_mixMeasure [∀ i, IsProbabilityMeasure (μ i)] :
    IsProbabilityMeasure (mixMeasure μ) := by
  constructor
  rw [mixMeasure, Measure.sum_apply_of_countable]
  simp only [Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
  simp_rw [pow_succ']
  rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric, ENNReal.one_sub_inv_two, inv_inv,
    ENNReal.inv_mul_cancel two_ne_zero ENNReal.ofNat_ne_top]

/-- The mixture of a uniformly computable sequence of probability measures is computable.
Blueprint node `vlm:mix`. -/
theorem IsComputableMeasureFamilyIn.isComputableMeasureIn_mix [∀ i, IsProbabilityMeasure (μ i)]
    (hμ : IsComputableMeasureFamilyIn P A μ) : IsComputableMeasureIn P A (mixMeasure μ) := by
  have hF : IsREIn A fun d : List (ℕ × ℚ) × ℕ × ℚ =>
      (d.2.2 : ℝ) < (μ d.2.1 (ballUnion P d.1)).toReal :=
    IsREIn.comp hμ (f := fun d : List (ℕ × ℚ) × ℕ × ℚ => ((d.2.1, d.1), d.2.2))
      (Computable.pair (Computable.pair (Computable.fst.comp Computable.snd) Computable.fst)
        (Computable.snd.comp Computable.snd)).computableIn
  have hG := IsREIn.list_forall_get hF
  have hH : IsREIn A fun w : (List (ℕ × ℚ) × ℚ) × List ℚ =>
      (∀ k (h : k < w.2.length),
        ((w.2.get ⟨k, h⟩ : ℚ) : ℝ) < (μ k (ballUnion P w.1.1)).toReal) ∧
        w.1.2 < mixPartialSum w.2 :=
    IsREIn.and (IsREIn.comp hG (f := fun w : (List (ℕ × ℚ) × ℚ) × List ℚ => (w.1.1, w.2))
      (Computable.pair (Computable.fst.comp Computable.fst) Computable.snd).computableIn)
      (isREIn_of_computable_decide (computable₂_ratLt.comp
        (Computable.snd.comp Computable.fst) (computable_mixPartialSum.comp Computable.snd)))
  obtain ⟨f, hf, hdom⟩ := IsREIn.exists hH
  refine ⟨f, hf, fun w => ?_⟩
  rw [← hdom w]
  dsimp only
  rw [mixMeasure_apply_toReal]
  exact lt_tsum_iff_exists_list (fun _ => ENNReal.toReal_nonneg)
    (fun i => by
      simpa using ENNReal.toReal_mono ENNReal.one_ne_top
        (prob_le_one (μ := μ i) (s := ballUnion P w.1))) w.2

/-- An almost decidable basis of the mixture is an almost decidable basis of every member, with
the boundary covers shifted by `i + 1` levels. Blueprint node `vlm:mix`. -/
theorem IsAlmostDecidableBasisIn.of_mixMeasure (hB : IsAlmostDecidableBasisIn P A (mixMeasure μ) B)
    (i : ℕ) : IsAlmostDecidableBasisIn P A (μ i) B := by
  obtain ⟨D, W, hD, hW, h⟩ := hB.exists_exterior
  refine ⟨hB.isCeOpenFamilyIn, ⟨D, fun p => W (p.1, p.2 + (i + 1)), hD,
    IsCeOpenFamilyIn.comp hW (g := fun p : ℕ × ℕ => (p.1, p.2 + (i + 1)))
      (Computable.pair Computable.fst
        ((Primrec.nat_add.comp Primrec.snd (Primrec.const (i + 1))).to_comp)),
    fun k => ⟨(h k).1, fun n => ⟨((h k).2 (n + (i + 1))).1, ?_⟩⟩⟩, hB.generates⟩
  have hle := Measure.le_iff'.1 (le_two_pow_smul_mixMeasure μ i) (W (k, n + (i + 1)))
  rw [Measure.smul_apply, smul_eq_mul] at hle
  refine hle.trans ?_
  calc (2 : ℝ≥0∞) ^ (i + 1) * mixMeasure μ (W (k, n + (i + 1)))
      ≤ (2 : ℝ≥0∞) ^ (i + 1) * (2⁻¹ ^ n * 2⁻¹ ^ (i + 1)) := by
        rw [← pow_add]
        gcongr
        exact ((h k).2 (n + (i + 1))).2
    _ = 2⁻¹ ^ n := by
        rw [mul_left_comm, ← mul_pow, ENNReal.mul_inv_cancel two_ne_zero ENNReal.ofNat_ne_top,
          one_pow, mul_one]

end Kolmogorov.PointToSet
