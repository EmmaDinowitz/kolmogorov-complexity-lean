/-
Copyright (c) 2026 Emma Dinowitz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emma Dinowitz
-/
import KolmogorovMathlib.PointToSet.Measure.Ergodic.HoyrupCondInfo

/-!
# Almost everywhere convergence of the conditional information

Lemma 4.1 of Hoyrup (STACS 2012), classical form: for a shift-invariant probability measure `ν` on
`ℕ → Bool`, `condInfo ν j x` converges (in `[0, ∞]`) for `ν`-almost every `x`.

Proof. `d_j(x) = ν[x₁ … x_j] / ν[x₀ … x_j]` (real division, `0` on null cylinders) is adapted to
the natural filtration of the coordinates and is a nonnegative SUPERmartingale (not a martingale in
general: an extension `w b` with `ν[w b] = 0` but `ν[w' b] > 0` loses mass), with
`E d_j ≤ E d_0 ≤ 2`. Apply Mathlib's convergence theorem to `-d` (a submartingale bounded in `L¹`,
`Submartingale.ae_tendsto_limitProcess`); `condInfo ν j = log₂ d_j` on the full-measure set where
all cylinders along `x` have positive measure. (The proof only uses `E d_j ≤ E d_0`, from the
supermartingale inequality, as the `L¹` bound.) The private helpers live in the namespace
`HoyrupMartingale`: the prefix map `pfx`, the process `d`, the filtration `filt` (`ℱ k` is the
comap of `x ↦ x↾(k+1)`), the one-cylinder inequality `cyl_step`.

Blueprint node `erg:hoyrup`.
-/

namespace Kolmogorov.PointToSet

open Filter Set MeasureTheory ProbabilityTheory
open scoped Topology ENNReal Computability

namespace HoyrupMartingale

/-- The prefix `x↾k` of a binary sequence, as a tuple. -/
private def pfx (k : ℕ) (x : ℕ → Bool) : Fin k → Bool := fun i ↦ x i

/-- The prefix map is measurable. -/
private lemma measurable_pfx (k : ℕ) : Measurable (pfx k) :=
  Measurable.of_eval fun i ↦ measurable_pi_apply (i : ℕ)

/-- Membership in a cylinder is equality of the prefix. -/
private lemma mem_cyl {k : ℕ} (v : Fin k → Bool) (x : ℕ → Bool) :
    x ∈ wordCylinder v ↔ pfx k x = v := by
  simp only [wordCylinder, Set.mem_ofPred_eq, pfx, funext_iff]

/-- A cylinder is the preimage of a point under the prefix map. -/
private lemma wordCylinder_eq_preimage {k : ℕ} (v : Fin k → Bool) :
    wordCylinder v = pfx k ⁻¹' {v} := by
  ext x
  rw [mem_cyl]
  rfl

/-- Cylinders are measurable. -/
private lemma measurableSet_cyl {k : ℕ} (v : Fin k → Bool) : MeasurableSet (wordCylinder v) := by
  rw [wordCylinder_eq_preimage]
  exact measurable_pfx k (measurableSet_singleton v)

/-- Membership in the cylinder of a one-symbol extension. -/
private lemma mem_cyl_snoc {k : ℕ} (v : Fin k → Bool) (b : Bool) (y : ℕ → Bool) :
    y ∈ wordCylinder (Fin.snoc (α := fun _ ↦ Bool) v b) ↔ y ∈ wordCylinder v ∧ y k = b := by
  simp only [wordCylinder, Set.mem_ofPred_eq, Fin.forall_fin_succ', Fin.snoc_castSucc,
    Fin.snoc_last, Fin.val_castSucc, Fin.val_last]

/-- A cylinder splits into its two one-symbol extensions. -/
private lemma cyl_eq_union {k : ℕ} (v : Fin k → Bool) :
    wordCylinder v = wordCylinder (Fin.snoc (α := fun _ ↦ Bool) v true) ∪
      wordCylinder (Fin.snoc (α := fun _ ↦ Bool) v false) := by
  ext y
  simp only [Set.mem_union, mem_cyl_snoc]
  cases hb : y k <;> simp

/-- The two one-symbol extensions of a cylinder are disjoint. -/
private lemma disjoint_snoc {k : ℕ} (v : Fin k → Bool) :
    Disjoint (wordCylinder (Fin.snoc (α := fun _ ↦ Bool) v true))
      (wordCylinder (Fin.snoc (α := fun _ ↦ Bool) v false)) := by
  refine Set.disjoint_left.2 fun y h1 h2 ↦ ?_
  rw [mem_cyl_snoc] at h1 h2
  rw [h1.2] at h2
  exact Bool.noConfusion h2.2

/-- `tail` commutes with `snoc`. -/
private lemma tail_snoc {k : ℕ} (v : Fin (k + 1) → Bool) (b : Bool) :
    Fin.tail (Fin.snoc (α := fun _ ↦ Bool) v b) = Fin.snoc (α := fun _ ↦ Bool) (Fin.tail v) b := by
  funext i
  refine Fin.lastCases ?_ (fun j ↦ ?_) i
  · simp [Fin.tail, Fin.succ_last]
  · change Fin.snoc (α := fun _ ↦ Bool) v b j.castSucc.succ = _
    rw [Fin.succ_castSucc, Fin.snoc_castSucc, Fin.snoc_castSucc]
    rfl

variable (ν : Measure (ℕ → Bool))

/-- `D k v = ν[v₁ … v_k] / ν[v₀ … v_k]` (real division, `0` on null cylinders). -/
private noncomputable def D (k : ℕ) (v : Fin (k + 1) → Bool) : ℝ :=
  ν.real (wordCylinder (Fin.tail v)) / ν.real (wordCylinder v)

/-- The process `d k x = ν[x₁ … x_k] / ν[x₀ … x_k]`. -/
private noncomputable def d (k : ℕ) (x : ℕ → Bool) : ℝ := D ν k (pfx (k + 1) x)

/-- The filtration `ℱ k = σ(x₀, …, x_k)` of the coordinates. -/
private def filt : Filtration ℕ (MeasurableSpace.pi : MeasurableSpace (ℕ → Bool)) where
  seq k := MeasurableSpace.comap (pfx (k + 1)) inferInstance
  mono' i j hij := by
    have : pfx (i + 1) = (fun v : Fin (j + 1) → Bool ↦ fun l : Fin (i + 1) ↦
        v (Fin.castLE (Nat.add_le_add_right hij 1) l)) ∘ pfx (j + 1) := rfl
    simp only [this, ← MeasurableSpace.comap_comp]
    exact MeasurableSpace.comap_mono (measurable_of_finite _).comap_le
  le' k := (measurable_pfx (k + 1)).comap_le

/-- `d k` is `ℱ k`-measurable. -/
private lemma measurable_d (k : ℕ) : Measurable[filt k] (d ν k) :=
  (measurable_of_finite (D ν k)).comp (comap_measurable (pfx (k + 1)))

/-- `d k` is nonnegative. -/
private lemma d_nonneg (k : ℕ) (x : ℕ → Bool) : 0 ≤ d ν k x :=
  div_nonneg measureReal_nonneg measureReal_nonneg

/-- `d k` is integrable (it takes finitely many values). -/
private lemma integrable_d [IsFiniteMeasure ν] (k : ℕ) : Integrable (d ν k) ν := by
  refine Integrable.of_bound ((measurable_d ν k).mono ((filt).le k) le_rfl).aestronglyMeasurable
    (∑ v, |D ν k v|) (ae_of_all _ fun x ↦ ?_)
  rw [Real.norm_eq_abs]
  exact Finset.single_le_sum (f := fun v ↦ |D ν k v|) (fun v _ ↦ abs_nonneg _)
    (Finset.mem_univ _)

/-- The integral of `d k` over a cylinder of length `k + 1`. -/
private lemma setIntegral_d_cyl (k : ℕ) (v : Fin (k + 1) → Bool) :
    ∫ x in wordCylinder v, d ν k x ∂ν = ν.real (wordCylinder v) * D ν k v := by
  rw [setIntegral_congr_fun (measurableSet_cyl v) (g := fun _ ↦ D ν k v), setIntegral_const,
    smul_eq_mul]
  intro x hx
  simp only [d, (mem_cyl v x).1 hx]

/-- `ν[v] · D k v ≤ ν[v₁ … v_k]`. -/
private lemma mul_D_le (k : ℕ) (v : Fin (k + 1) → Bool) :
    ν.real (wordCylinder v) * D ν k v ≤ ν.real (wordCylinder (Fin.tail v)) := by
  by_cases h : ν.real (wordCylinder v) = 0
  · simp [h, measureReal_nonneg]
  · rw [D, mul_div_cancel₀ _ h]

/-- `ν[v] · D k v = ν[v₁ … v_k]` when `ν[v] ≠ 0`. -/
private lemma mul_D_of_ne (k : ℕ) (v : Fin (k + 1) → Bool) (h : ν.real (wordCylinder v) ≠ 0) :
    ν.real (wordCylinder v) * D ν k v = ν.real (wordCylinder (Fin.tail v)) := by
  rw [D, mul_div_cancel₀ _ h]

/-- The supermartingale inequality on one cylinder. -/
private lemma cyl_step [IsFiniteMeasure ν] (k : ℕ) (v : Fin (k + 1) → Bool) :
    ∫ x in wordCylinder v, d ν (k + 1) x ∂ν ≤ ∫ x in wordCylinder v, d ν k x ∂ν := by
  have hint := integrable_d ν (k + 1)
  have hsplit : ∫ x in wordCylinder v, d ν (k + 1) x ∂ν =
      ν.real (wordCylinder (Fin.snoc (α := fun _ ↦ Bool) v true)) *
          D ν (k + 1) (Fin.snoc (α := fun _ ↦ Bool) v true) +
        ν.real (wordCylinder (Fin.snoc (α := fun _ ↦ Bool) v false)) *
          D ν (k + 1) (Fin.snoc (α := fun _ ↦ Bool) v false) := by
    rw [cyl_eq_union v, setIntegral_union (disjoint_snoc v) (measurableSet_cyl _)
      hint.integrableOn hint.integrableOn, setIntegral_d_cyl, setIntegral_d_cyl]
  rw [hsplit, setIntegral_d_cyl]
  by_cases h : ν.real (wordCylinder v) = 0
  · have hz : ∀ b, ν.real (wordCylinder (Fin.snoc (α := fun _ ↦ Bool) v b)) = 0 := fun b ↦
      le_antisymm (h ▸ measureReal_mono fun y hy ↦ ((mem_cyl_snoc v b y).1 hy).1)
        measureReal_nonneg
    simp [h, hz]
  · rw [mul_D_of_ne ν k v h]
    calc _ ≤ ν.real (wordCylinder (Fin.tail (Fin.snoc (α := fun _ ↦ Bool) v true))) +
          ν.real (wordCylinder (Fin.tail (Fin.snoc (α := fun _ ↦ Bool) v false))) :=
          add_le_add (mul_D_le ν _ _) (mul_D_le ν _ _)
      _ = ν.real (wordCylinder (Fin.tail v)) := by
        rw [tail_snoc, tail_snoc, cyl_eq_union (Fin.tail v),
          measureReal_union (disjoint_snoc _) (measurableSet_cyl _)]

/-- The supermartingale inequality on an `ℱ k`-measurable set. -/
private lemma step [IsFiniteMeasure ν] (k : ℕ) (s : Set (ℕ → Bool)) (hs : MeasurableSet[filt k] s) :
    ∫ x in s, d ν (k + 1) x ∂ν ≤ ∫ x in s, d ν k x ∂ν := by
  classical
  obtain ⟨T, -, rfl⟩ := MeasurableSpace.measurableSet_comap.1 hs
  have hT : pfx (k + 1) ⁻¹' T = ⋃ v ∈ Finset.univ.filter (· ∈ T), wordCylinder v := by
    ext x
    simp [mem_cyl]
  have hdisj : (↑(Finset.univ.filter (· ∈ T)) : Set (Fin (k + 1) → Bool)).Pairwise
      (Function.onFun Disjoint fun v ↦ wordCylinder v) := fun v _ w _ hvw ↦ by
    simp only [Function.onFun, wordCylinder_eq_preimage]
    exact (Set.disjoint_singleton.2 hvw).preimage _
  rw [hT, integral_biUnion_finset _ (fun v _ ↦ measurableSet_cyl v) hdisj
      (fun v _ ↦ (integrable_d ν (k + 1)).integrableOn),
    integral_biUnion_finset _ (fun v _ ↦ measurableSet_cyl v) hdisj
      (fun v _ ↦ (integrable_d ν k).integrableOn)]
  exact Finset.sum_le_sum fun v _ ↦ cyl_step ν k v

/-- `d` is a supermartingale for the coordinate filtration. -/
private lemma supermartingale_d [IsFiniteMeasure ν] : Supermartingale (d ν) filt ν :=
  supermartingale_of_setIntegral_succ_le (fun k ↦ (measurable_d ν k).stronglyMeasurable)
    (integrable_d ν) (step ν)

/-- The expectations of `d k` decrease. -/
private lemma integral_d_le [IsFiniteMeasure ν] (k : ℕ) : ∫ x, d ν k x ∂ν ≤ ∫ x, d ν 0 x ∂ν := by
  have h : Antitone fun k ↦ ∫ x, d ν k x ∂ν := antitone_nat_of_succ_le fun k ↦ by
    simpa only [setIntegral_univ] using step ν k univ MeasurableSet.univ
  exact h (Nat.zero_le k)

/-- `d k` converges almost everywhere to a finite limit. -/
private lemma ae_tendsto_d [IsFiniteMeasure ν] :
    ∀ᵐ x ∂ν, ∃ l, Tendsto (fun k ↦ d ν k x) atTop (𝓝 l) := by
  have hbdd : ∀ k, eLpNorm ((-d ν) k) 1 ν ≤ (∫ x, d ν 0 x ∂ν).toNNReal := fun k ↦ by
    rw [Pi.neg_apply, eLpNorm_neg, eLpNorm_one_eq_lintegral_enorm
      (integrable_d ν k).aestronglyMeasurable]
    simp_rw [Real.enorm_of_nonneg (d_nonneg ν k _)]
    rw [← ofReal_integral_eq_lintegral_ofReal (integrable_d ν k)
      (ae_of_all _ (d_nonneg ν k))]
    exact ENNReal.ofReal_le_ofReal (integral_d_le ν k)
  filter_upwards [(supermartingale_d ν).neg.ae_tendsto_limitProcess hbdd] with x hx
  exact ⟨_, by simpa using hx.neg⟩

/-- Almost every sequence has all its prefixes of positive measure. -/
private lemma ae_pos : ∀ᵐ x ∂ν, ∀ n, ν (wordCylinder (pfx n x)) ≠ 0 := by
  rw [ae_all_iff]
  intro n
  rw [ae_iff]
  simp only [ne_eq, not_not]
  have : {x | ν (wordCylinder (pfx n x)) = 0} =
      ⋃ v ∈ {v : Fin n → Bool | ν (wordCylinder v) = 0}, wordCylinder v := by
    ext x
    simp [mem_cyl]
  rw [this, measure_biUnion_null_iff (Set.to_countable _)]
  exact fun v hv ↦ hv

/-- Where the cylinder `[x↾(j+1)]` has positive measure, `condInfo ν j x = log₂ d j x` and
`1 ≤ d j x`. -/
private lemma condInfo_eq [IsFiniteMeasure ν] (hν : MeasurePreserving shiftMap ν ν) (j : ℕ)
    (x : ℕ → Bool) (hx : ν (wordCylinder (pfx (j + 1) x)) ≠ 0) :
    condInfo ν j x = ENNReal.ofReal (Real.logb 2 (d ν j x)) ∧ 1 ≤ d ν j x := by
  set v := pfx (j + 1) x with hv
  have h1 : listCylinder (wordPrefix x (j + 1)) = wordCylinder v := listCylinder_ofFn _
  have h2 : listCylinder (wordPrefix (shiftMap x) j) = wordCylinder (Fin.tail v) :=
    listCylinder_ofFn _
  have hsub : wordCylinder v ⊆ shiftMap ⁻¹' wordCylinder (Fin.tail v) :=
    fun y hy i ↦ hy i.succ
  have hab : ν (wordCylinder v) ≤ ν (wordCylinder (Fin.tail v)) := by
    calc _ ≤ ν (shiftMap ⁻¹' wordCylinder (Fin.tail v)) := measure_mono hsub
      _ = _ := hν.measure_preimage (measurableSet_cyl _).nullMeasurableSet
  have ha : 0 < (ν (wordCylinder v)).toReal :=
    ENNReal.toReal_pos hx (measure_ne_top _ _)
  have hab' : (ν (wordCylinder v)).toReal ≤ (ν (wordCylinder (Fin.tail v))).toReal :=
    ENNReal.toReal_mono (measure_ne_top _ _) hab
  have hd : d ν j x = (ν (wordCylinder (Fin.tail v))).toReal / (ν (wordCylinder v)).toReal :=
    rfl
  refine ⟨?_, by rw [hd]; exact (one_le_div ha).2 hab'⟩
  have hne : ν (wordCylinder v) / ν (wordCylinder (Fin.tail v)) ≠ 0 :=
    (ENNReal.div_pos_iff.2 ⟨hx, measure_ne_top _ _⟩).ne'
  rw [condInfo, h1, h2, infoBits_of_ne hne, ENNReal.toReal_div, ← Real.logb_inv, inv_div, hd]

end HoyrupMartingale

open HoyrupMartingale in
/-- The conditional information converges almost everywhere. Blueprint node `erg:hoyrup`. -/
theorem ae_exists_tendsto_condInfo {ν : Measure (ℕ → Bool)} [IsProbabilityMeasure ν]
    (hν : MeasurePreserving shiftMap ν ν) :
    ∀ᵐ x ∂ν, ∃ l, Tendsto (fun j ↦ condInfo ν j x) atTop (𝓝 l) := by
  filter_upwards [ae_tendsto_d ν, ae_pos ν] with x ⟨l, hl⟩ hpos
  have hge : ∀ j, 1 ≤ d ν j x := fun j ↦ (condInfo_eq ν hν j x (hpos _)).2
  have hl1 : 1 ≤ l := ge_of_tendsto' hl hge
  refine ⟨ENNReal.ofReal (Real.logb 2 l), ?_⟩
  refine (ENNReal.tendsto_ofReal (hl.logb (by positivity))).congr fun j ↦ ?_
  exact (condInfo_eq ν hν j x (hpos _)).1.symm

end Kolmogorov.PointToSet
