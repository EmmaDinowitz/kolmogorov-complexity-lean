/-
Copyright (c) 2026 Emma Dinowitz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emma Dinowitz
-/
import KolmogorovMathlib.PointToSet.Measure.Ergodic.HoyrupChung
import KolmogorovMathlib.PointToSet.Measure.Ergodic.HoyrupMartingale
import KolmogorovMathlib.PointToSet.Measure.Ergodic.SymbolicLowerBoundAux

/-!
# The integral of the limit of the conditional information is the entropy

For a shift-invariant probability measure `ν` on `ℕ → Bool`:

* `lintegral_condInfo`: `∫ condInfo ν j dν = H_ν(ξ^{j+1}) - H_ν(ξ^j)` (invariance:
  `∑_w ν[w] (-log₂ ν[w] + log₂ ν[w₁…w_j])`).
* `shiftEntropy_le_iSup_lintegral_min`: `h_ν(σ) ≤ ⨆_N ⨆_L ∫ min(⨅_{j≥N} condInfo ν j, L) dν`.
  Proof: `condInfo ν j → f` a.e. (`ae_exists_tendsto_condInfo`) with integrable supremum
  (`lintegral_iSup_condInfo_lt_top`), so `∫ condInfo ν j → ∫ f` (dominated convergence); the
  Cesàro means of `H_ν(ξ^{j+1}) - H_ν(ξ^j)` are `H_ν(ξ^n)/n`, so `H_ν(ξ^n)/n → ∫ f`
  (`Filter.Tendsto.cesaro`), and `h_ν(σ) = inf_n H_ν(ξ^n)/n ≤ ∫ f` (no subadditivity needed);
  with `f = liminf_j condInfo ν j = ⨆_N ⨅_{j ≥ N} condInfo ν j` a.e., monotone convergence in
  `N` and `L` identifies `∫ f` with the double supremum.

Blueprint node `erg:hoyrup`.
-/

namespace Kolmogorov.PointToSet

open Filter Set MeasureTheory
open scoped Topology ENNReal Computability

/-! ### Cylinder computations -/

/-- On the cylinder `[w]`, `|w| = j + 1`, the conditional information is the constant
`-log₂ (ν[w] / ν[w₁ … w_j])`. -/
private lemma condInfo_eq_of_mem (ν : Measure (ℕ → Bool)) {j : ℕ} {w : Fin (j + 1) → Bool}
    {x : ℕ → Bool} (hx : x ∈ wordCylinder w) :
    condInfo ν j x = infoBits (ν (wordCylinder w) / ν (wordCylinder (Fin.tail w))) := by
  have h1 : wordPrefix x (j + 1) = List.ofFn w := by
    simp only [wordPrefix]
    congr 1
    funext i
    exact hx i
  have h2 : wordPrefix (shiftMap x) j = List.ofFn (Fin.tail w) := by
    simp only [wordPrefix]
    congr 1
    funext i
    have := hx i.succ
    simp only [Fin.val_succ] at this
    simpa [shiftMap, Fin.tail] using this
  rw [condInfo, h1, h2, listCylinder_ofFn, listCylinder_ofFn]

/-- Invariance on cylinders: `ν[v] = ∑_b ν[b v]`. -/
private lemma measure_wordCylinder_eq_sum_cons {ν : Measure (ℕ → Bool)}
    (hν : MeasurePreserving shiftMap ν ν) {j : ℕ} (v : Fin j → Bool) :
    ν (wordCylinder v) = ∑ b : Bool, ν (wordCylinder (Fin.cons b v : Fin (j + 1) → Bool)) := by
  have hpre : shiftMap ⁻¹' wordCylinder v =
      ⋃ b : Bool, wordCylinder (Fin.cons b v : Fin (j + 1) → Bool) := by
    ext y
    simp only [mem_preimage, wordCylinder, mem_ofPred_eq, mem_iUnion]
    constructor
    · intro h
      refine ⟨y 0, fun i ↦ ?_⟩
      refine Fin.cases ?_ (fun i ↦ ?_) i
      · simp
      · simpa [shiftMap] using h i
    · rintro ⟨b, hb⟩ i
      simpa [shiftMap] using hb i.succ
  rw [← hν.measure_preimage (SymbolicLower.measurableSet_wordCylinder' v).nullMeasurableSet,
    hpre, measure_iUnion, tsum_fintype]
  · intro b c hbc
    refine Set.disjoint_left.2 fun y hb hc ↦ hbc ?_
    have h0b := hb 0
    have h0c := hc 0
    simp only [Fin.cons_zero] at h0b h0c
    rw [← h0b, ← h0c]
  · exact fun b ↦ SymbolicLower.measurableSet_wordCylinder' _

/-- A cylinder has at most the mass of its tail cylinder (invariance). -/
private lemma measure_wordCylinder_le_tail {ν : Measure (ℕ → Bool)}
    (hν : MeasurePreserving shiftMap ν ν) {j : ℕ} (w : Fin (j + 1) → Bool) :
    ν (wordCylinder w) ≤ ν (wordCylinder (Fin.tail w)) := by
  rw [measure_wordCylinder_eq_sum_cons hν (Fin.tail w)]
  conv_lhs => rw [← Fin.cons_self_tail w]
  exact Finset.single_le_sum (f := fun b ↦ ν (wordCylinder (Fin.cons b (Fin.tail w) :
    Fin (j + 1) → Bool))) (fun _ _ ↦ by simp) (Finset.mem_univ (w 0))

/-- The real contribution `ν[w] (log₂ ν[w₁…w_j] - log₂ ν[w])` of a word to `∫ condInfo ν j`. -/
private noncomputable def condInfoTerm (ν : Measure (ℕ → Bool)) {j : ℕ}
    (w : Fin (j + 1) → Bool) : ℝ :=
  (ν (wordCylinder w)).toReal *
    (Real.logb 2 (ν (wordCylinder (Fin.tail w))).toReal - Real.logb 2 (ν (wordCylinder w)).toReal)

/-- The contribution of a word is nonnegative. -/
private lemma condInfoTerm_nonneg {ν : Measure (ℕ → Bool)} [IsProbabilityMeasure ν]
    (hν : MeasurePreserving shiftMap ν ν) {j : ℕ} (w : Fin (j + 1) → Bool) :
    0 ≤ condInfoTerm ν w := by
  rcases eq_or_ne (ν (wordCylinder w)) 0 with h0 | h0
  · simp [condInfoTerm, h0]
  have hle := measure_wordCylinder_le_tail hν w
  have hpos : 0 < (ν (wordCylinder w)).toReal := ENNReal.toReal_pos h0 (measure_ne_top _ _)
  refine mul_nonneg ENNReal.toReal_nonneg (sub_nonneg.2 ?_)
  exact Real.logb_le_logb_of_le one_lt_two hpos (ENNReal.toReal_mono (measure_ne_top _ _) hle)

/-- `ν[w] · (-log₂ (ν[w] / ν[w₁…w_j])) = ofReal (condInfoTerm ν w)`. -/
private lemma mul_infoBits_eq_condInfoTerm {ν : Measure (ℕ → Bool)} [IsProbabilityMeasure ν]
    (hν : MeasurePreserving shiftMap ν ν) {j : ℕ} (w : Fin (j + 1) → Bool) :
    ν (wordCylinder w) * infoBits (ν (wordCylinder w) / ν (wordCylinder (Fin.tail w))) =
      ENNReal.ofReal (condInfoTerm ν w) := by
  rcases eq_or_ne (ν (wordCylinder w)) 0 with h0 | h0
  · simp [condInfoTerm, h0]
  have hle := measure_wordCylinder_le_tail hν w
  have ht0 : ν (wordCylinder (Fin.tail w)) ≠ 0 := (pos_iff_ne_zero.2 h0).trans_le hle |>.ne'
  have hq0 : ν (wordCylinder w) / ν (wordCylinder (Fin.tail w)) ≠ 0 := by
    simp [ENNReal.div_eq_zero_iff, h0, measure_ne_top]
  have hpos : 0 < (ν (wordCylinder w)).toReal := ENNReal.toReal_pos h0 (measure_ne_top _ _)
  have htpos : 0 < (ν (wordCylinder (Fin.tail w))).toReal :=
    ENNReal.toReal_pos ht0 (measure_ne_top _ _)
  rw [infoBits_of_ne hq0, ENNReal.toReal_div, Real.logb_div hpos.ne' htpos.ne', condInfoTerm,
    ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal (measure_ne_top _ _)]
  congr 2
  ring

/-- `∫ condInfo ν j dν = ∑_{|w| = j+1} ν[w] · (-log₂ (ν[w] / ν[w₁…w_j]))`. -/
private lemma lintegral_condInfo_eq_sum (ν : Measure (ℕ → Bool)) (j : ℕ) :
    ∫⁻ x, condInfo ν j x ∂ν = ∑ w : Fin (j + 1) → Bool,
      ν (wordCylinder w) * infoBits (ν (wordCylinder w) / ν (wordCylinder (Fin.tail w))) := by
  have hU : (⋃ w : Fin (j + 1) → Bool, wordCylinder w) = univ :=
    (SymbolicLower.isMeasurablePartition_wordCylinder (β := Bool) (j + 1)).iUnion_eq
  rw [← setLIntegral_univ, ← hU, lintegral_iUnion
    (fun w ↦ SymbolicLower.measurableSet_wordCylinder' w)
    (SymbolicLower.isMeasurablePartition_wordCylinder (β := Bool) (j + 1)).disjoint, tsum_fintype]
  refine Finset.sum_congr rfl fun w _ ↦ ?_
  rw [setLIntegral_congr_fun (SymbolicLower.measurableSet_wordCylinder' w)
    (fun x hx ↦ condInfo_eq_of_mem ν hx), setLIntegral_const, mul_comm]

/-- `∑_{|w| = j+1} condInfoTerm ν w = H_ν(ξ^{j+1}) - H_ν(ξ^j)`. -/
private lemma sum_condInfoTerm {ν : Measure (ℕ → Bool)} [IsProbabilityMeasure ν]
    (hν : MeasurePreserving shiftMap ν ν) (j : ℕ) :
    ∑ w : Fin (j + 1) → Bool, condInfoTerm ν w = blockEntropy ν (j + 1) - blockEntropy ν j := by
  have htail : ∑ w : Fin (j + 1) → Bool, (ν (wordCylinder w)).toReal *
      Real.logb 2 (ν (wordCylinder (Fin.tail w))).toReal = -blockEntropy ν j := by
    rw [← Fintype.sum_equiv (Fin.consEquiv fun _ ↦ Bool) (fun p ↦
      (ν (wordCylinder (Fin.cons p.1 p.2 : Fin (j + 1) → Bool))).toReal *
        Real.logb 2 (ν (wordCylinder p.2)).toReal) _ (fun p ↦ by simp [Fin.consEquiv]),
      Fintype.sum_prod_type, Finset.sum_comm, blockEntropy, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun v _ ↦ ?_
    dsimp only
    rw [← Finset.sum_mul, ← ENNReal.toReal_sum fun _ _ ↦ measure_ne_top _ _,
      ← measure_wordCylinder_eq_sum_cons hν v]
    ring
  have hH : blockEntropy ν (j + 1) = -∑ w : Fin (j + 1) → Bool,
      (ν (wordCylinder w)).toReal * Real.logb 2 (ν (wordCylinder w)).toReal := by
    rw [blockEntropy, ← Finset.sum_neg_distrib]
    simp only [neg_mul]
  simp only [condInfoTerm, mul_sub, Finset.sum_sub_distrib, htail, hH]
  ring

/-- The block entropy of length `0` vanishes. -/
private lemma blockEntropy_zero_bool (ν : Measure (ℕ → Bool)) [IsProbabilityMeasure ν] :
    blockEntropy ν 0 = 0 := by
  simp [blockEntropy, wordCylinder]

/-! ### The theorems -/

/-- `∫ condInfo ν j dν = H_ν(ξ^{j+1}) - H_ν(ξ^j)`. Blueprint node `erg:hoyrup`. -/
theorem lintegral_condInfo {ν : Measure (ℕ → Bool)} [IsProbabilityMeasure ν]
    (hν : MeasurePreserving shiftMap ν ν) (j : ℕ) :
    ∫⁻ x, condInfo ν j x ∂ν = ENNReal.ofReal (blockEntropy ν (j + 1) - blockEntropy ν j) := by
  rw [lintegral_condInfo_eq_sum, ← sum_condInfoTerm hν,
    ENNReal.ofReal_sum_of_nonneg fun w _ ↦ condInfoTerm_nonneg hν w]
  exact Finset.sum_congr rfl fun w _ ↦ mul_infoBits_eq_condInfoTerm hν w

/-- `h_ν(σ) ≤ ⨆_N ⨆_L ∫ min(⨅_{j≥N} condInfo ν j, L) dν`. Blueprint node `erg:hoyrup`. -/
theorem shiftEntropy_le_iSup_lintegral_min {ν : Measure (ℕ → Bool)} [IsProbabilityMeasure ν]
    (hν : MeasurePreserving shiftMap ν ν) :
    shiftEntropy ν ≤ ⨆ N : ℕ, ⨆ L : ℕ, ∫⁻ x, min (⨅ j ≥ N, condInfo ν j x) (L : ℝ≥0∞) ∂ν := by
  set g : ℕ → (ℕ → Bool) → ℝ≥0∞ := fun N x ↦ ⨅ j ≥ N, condInfo ν j x with hg
  have hgm : ∀ N, Measurable (g N) := fun N ↦
    Measurable.iInf fun j ↦ Measurable.iInf fun _ ↦ measurable_condInfo ν j
  have hgmono : Monotone g := fun N M h x ↦ biInf_mono fun j hj ↦ h.trans hj
  -- monotone convergence in `L`, then in `N`
  have hA : ∫⁻ x, ⨆ N, g N x ∂ν = ⨆ N : ℕ, ⨆ L : ℕ, ∫⁻ x, min (g N x) (L : ℝ≥0∞) ∂ν := by
    rw [lintegral_iSup hgm hgmono]
    refine iSup_congr fun N ↦ ?_
    have hL : ∀ x, g N x = ⨆ L : ℕ, min (g N x) (L : ℝ≥0∞) := fun x ↦ by
      rw [← inf_iSup_eq, ENNReal.iSup_natCast, inf_top_eq]
    rw [lintegral_congr hL]
    exact lintegral_iSup (fun L ↦ (hgm N).min measurable_const)
      fun L L' h x ↦ min_le_min_left _ (Nat.cast_le.2 h)
  simp only [hg] at hA
  rw [← hA]
  -- dominated convergence of `∫ condInfo ν j`
  have hlim : ∀ᵐ x ∂ν, Tendsto (fun j ↦ condInfo ν j x) atTop (𝓝 (⨆ N, g N x)) := by
    filter_upwards [ae_exists_tendsto_condInfo hν] with x ⟨l, hl⟩
    have h := hl.liminf_eq
    rw [liminf_eq_iSup_iInf_of_nat] at h
    simpa [hg, h] using hl
  have hdom := tendsto_lintegral_of_dominated_convergence (fun x ↦ ⨆ j, condInfo ν j x)
    (measurable_condInfo ν) (fun n ↦ Eventually.of_forall fun x ↦
      le_iSup (fun j ↦ condInfo ν j x) n) (lintegral_iSup_condInfo_lt_top hν).ne hlim
  set I := ∫⁻ x, ⨆ N, g N x ∂ν with hI
  have hItop : I ≠ ⊤ := by
    refine ne_top_of_le_ne_top (lintegral_iSup_condInfo_lt_top hν).ne (lintegral_mono fun x ↦ ?_)
    exact iSup_le fun N ↦ (iInf₂_le N le_rfl).trans (le_iSup (fun j ↦ condInfo ν j x) N)
  -- the increments `H_{j+1} - H_j` converge to `I`
  have hnn : ∀ j, 0 ≤ blockEntropy ν (j + 1) - blockEntropy ν j := fun j ↦
    sub_nonneg.2 (SymbolicLower.blockEntropy_mono ν (Nat.le_succ j))
  have ha : Tendsto (fun j ↦ blockEntropy ν (j + 1) - blockEntropy ν j) atTop (𝓝 I.toReal) := by
    simp_rw [lintegral_condInfo hν] at hdom
    have := (ENNReal.tendsto_toReal hItop).comp hdom
    simpa [Function.comp_def, ENNReal.toReal_ofReal (hnn _)] using this
  -- Cesàro: `H_n / n → I`
  have hc := ha.cesaro
  simp_rw [Finset.sum_range_sub (fun j ↦ blockEntropy ν j), blockEntropy_zero_bool, sub_zero]
    at hc
  have hc' : Tendsto (fun n : ℕ ↦ ENNReal.ofReal (blockEntropy ν n / n)) atTop (𝓝 I) := by
    rw [← ENNReal.ofReal_toReal hItop]
    refine ENNReal.tendsto_ofReal ?_
    simpa [div_eq_inv_mul] using hc
  refine ge_of_tendsto hc' (eventually_atTop.2 ⟨1, fun n hn ↦ ?_⟩)
  exact iInf₂_le n hn

end Kolmogorov.PointToSet
