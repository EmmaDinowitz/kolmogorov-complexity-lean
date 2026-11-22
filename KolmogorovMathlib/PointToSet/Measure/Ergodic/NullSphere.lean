/-
Copyright (c) 2026 Emma Dinowitz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emma Dinowitz
-/
import KolmogorovMathlib.PointToSet.Measure.EffectiveNull
import Mathlib.Topology.Algebra.Module.Cardinality

/-!
# Radii whose spheres are null

Input (I1) of the note *Orbit complexity of Martin-Löf random points equals entropy*
(Hoyrup–Rojas, *Computability of probability measures and Martin-Löf randomness over metric
spaces*, 2009; Galatolo–Hoyrup–Rojas 2010, §3.1): for an `A`-computable presentation and an
`A`-computable probability measure `μ` there is a uniformly `A`-computable sequence `(r_m)` of
positive reals, dense in `(0, ∞)`, such that every sphere `{y | d(y, x_i) = r_m}` about an ideal
point is `μ`-null.

* `isCeOpenFamilyIn_ball_of_computableRadius`, `isCeOpenFamilyIn_dist_gt_of_computableRadius`:
  the open balls `B(x_i, r_m)` and the sets `{y | d(y, x_i) > r_m}` are uniformly `A`-c.e. open
  when `(r_m)` is an `A`-computable real family.
* `exists_nullSphere_radii` (I1). Proof (effective Baire category): for a rational interval
  `I` and `k`, search for a rational subinterval `[a, b] ⊂ I` of length `< 2^{-k}` such that the
  closed annuli `{a ≤ d(·, x_i) ≤ b}`, `i ≤ k`, have measure `< 2^{-k}`; the measure of an
  `A`-effectively closed set is upper semicomputable (complement of (M1)), so the condition is
  semi-decidable, and such intervals exist since only countably many spheres about `x_i` carry
  mass. Iterating gives nested intervals whose intersection is `r`. The `m`-th radius is the
  limit of the nested intervals started at the rational interval coded by `m` (replaced by
  `(1, 2)` when that code is not an interval of positive rationals), which gives density; the
  midpoints of the intervals are the rational approximations.

Blueprint node `erg:null-sphere`.
-/

namespace Kolmogorov.PointToSet

open Filter Set MeasureTheory
open scoped Topology ENNReal Computability

variable {X : Type*} [MetricSpace X]

/-- Open balls about ideal points with radii from an `A`-computable real family are uniformly
`A`-c.e. open. Blueprint node `erg:null-sphere`. -/
theorem isCeOpenFamilyIn_ball_of_computableRadius (P : Presentation X) (A : Set ℕ)
    (hP : ComputablePresentationIn P A) {r : ℕ → ℝ} (hr : IsComputableRealFamilyIn A r) :
    IsCeOpenFamilyIn P A fun im : ℕ × ℕ ↦ Metric.ball (P.ι im.1) (r im.2) := by
  have hlt := birkhoff_computableIn_lt A _ hP
  have hgt := birkhoff_computableIn_gt A r hr
  -- a basic ball `(j, s)` is listed for `(i, m)` when `d(x_i, x_j) < t` and `t + s < r_m`
  let F : ((ℕ × ℕ) × (ℕ × ℚ)) × ℚ → Prop := fun w ↦ (0 : ℚ) < w.1.2.2 ∧
    (dist (P.ι w.1.1.1) (P.ι w.1.2.1) < (w.2 : ℝ) ∧ (((w.2 + w.1.2.2 : ℚ)) : ℝ) < r w.1.1.2)
  have hF : IsREIn A F := by
    refine (isREIn_of_computable_decide (computable₂_ratLt.comp (Computable.const 0)
      (Computable.snd.comp (Computable.snd.comp Computable.fst)))).and
      ((hlt.comp (f := fun w : ((ℕ × ℕ) × (ℕ × ℚ)) × ℚ ↦ ((w.1.1.1, w.1.2.1), w.2)) ?_).and
        (hgt.comp (f := fun w : ((ℕ × ℕ) × (ℕ × ℚ)) × ℚ ↦ (w.1.1.2, w.2 + w.1.2.2)) ?_))
    · exact (((Computable.fst.comp (Computable.fst.comp Computable.fst)).pair
        (Computable.fst.comp (Computable.snd.comp Computable.fst))).pair
        Computable.snd).computableIn
    · exact ((Computable.snd.comp (Computable.fst.comp Computable.fst)).pair
        (computable₂_ratAdd.comp Computable.snd
          (Computable.snd.comp (Computable.snd.comp Computable.fst)))).computableIn
  refine ⟨fun ib ↦ ∃ t, F (ib, t), hF.exists, fun im ↦ ?_⟩
  ext y
  constructor
  · intro hy
    have hy' : dist y (P.ι im.1) < r im.2 := hy
    set ρ : ℝ := r im.2 - dist y (P.ι im.1) with hρ
    have hρ0 : 0 < ρ := by linarith
    obtain ⟨k, hk⟩ := Metric.denseRange_iff.mp P.dense y (ρ / 4) (by positivity)
    obtain ⟨s, hs1, hs2⟩ := exists_rat_btwn (show ρ / 4 < ρ / 2 by linarith)
    have htri := dist_triangle (P.ι im.1) y (P.ι k)
    rw [dist_comm (P.ι im.1) y] at htri
    obtain ⟨t, ht1, ht2⟩ := exists_rat_btwn
      (show dist (P.ι im.1) (P.ι k) < dist y (P.ι im.1) + ρ / 4 by linarith)
    refine Set.mem_iUnion₂.mpr ⟨(k, s), ⟨t, ?_, ht1, ?_⟩, Metric.mem_ball.mpr (hk.trans hs1)⟩
    · exact_mod_cast (show (0 : ℝ) < ρ / 4 by positivity).trans hs1
    · push_cast
      linarith
  · intro hy
    obtain ⟨b, ⟨t, _, hb1, hb2⟩, hyb⟩ := Set.mem_iUnion₂.mp hy
    have hyb' : dist y (P.ι b.1) < b.2 := hyb
    push_cast at hb2
    change dist y (P.ι im.1) < r im.2
    have htri := dist_triangle y (P.ι b.1) (P.ι im.1)
    rw [dist_comm (P.ι b.1) (P.ι im.1)] at htri
    linarith

/-- The sets `{y | d(y, x_i) > r_m}` are uniformly `A`-c.e. open for an `A`-computable real
family `(r_m)`. Blueprint node `erg:null-sphere`. -/
theorem isCeOpenFamilyIn_dist_gt_of_computableRadius (P : Presentation X) (A : Set ℕ)
    (hP : ComputablePresentationIn P A) {r : ℕ → ℝ} (hr : IsComputableRealFamilyIn A r) :
    IsCeOpenFamilyIn P A fun im : ℕ × ℕ ↦ {y | r im.2 < dist y (P.ι im.1)} := by
  have hgt := birkhoff_computableIn_gt A _ hP
  have hlt := birkhoff_computableIn_lt A r hr
  -- a basic ball `(j, s)` is listed for `(i, m)` when `t < d(x_i, x_j)` and `r_m < t - s`
  let F : ((ℕ × ℕ) × (ℕ × ℚ)) × ℚ → Prop := fun w ↦ (0 : ℚ) < w.1.2.2 ∧
    ((w.2 : ℝ) < dist (P.ι w.1.1.1) (P.ι w.1.2.1) ∧ r w.1.1.2 < (((w.2 - w.1.2.2 : ℚ)) : ℝ))
  have hF : IsREIn A F := by
    refine (isREIn_of_computable_decide (computable₂_ratLt.comp (Computable.const 0)
      (Computable.snd.comp (Computable.snd.comp Computable.fst)))).and
      ((hgt.comp (f := fun w : ((ℕ × ℕ) × (ℕ × ℚ)) × ℚ ↦ ((w.1.1.1, w.1.2.1), w.2)) ?_).and
        (hlt.comp (f := fun w : ((ℕ × ℕ) × (ℕ × ℚ)) × ℚ ↦ (w.1.1.2, w.2 - w.1.2.2)) ?_))
    · exact (((Computable.fst.comp (Computable.fst.comp Computable.fst)).pair
        (Computable.fst.comp (Computable.snd.comp Computable.fst))).pair
        Computable.snd).computableIn
    · exact ((Computable.snd.comp (Computable.fst.comp Computable.fst)).pair
        (computable₂_ratSub.comp Computable.snd
          (Computable.snd.comp (Computable.snd.comp Computable.fst)))).computableIn
  refine ⟨fun ib ↦ ∃ t, F (ib, t), hF.exists, fun im ↦ ?_⟩
  ext y
  constructor
  · intro hy
    have hy' : r im.2 < dist y (P.ι im.1) := hy
    set ρ : ℝ := dist y (P.ι im.1) - r im.2 with hρ
    have hρ0 : 0 < ρ := by linarith
    obtain ⟨k, hk⟩ := Metric.denseRange_iff.mp P.dense y (ρ / 4) (by positivity)
    obtain ⟨s, hs1, hs2⟩ := exists_rat_btwn (show ρ / 4 < ρ / 2 by linarith)
    have htri := dist_triangle (P.ι im.1) (P.ι k) y
    rw [dist_comm (P.ι im.1) y, dist_comm (P.ι k) y] at htri
    obtain ⟨t, ht1, ht2⟩ := exists_rat_btwn
      (show dist y (P.ι im.1) - ρ / 4 < dist (P.ι im.1) (P.ι k) by linarith)
    refine Set.mem_iUnion₂.mpr ⟨(k, s), ⟨t, ?_, ht2, ?_⟩, Metric.mem_ball.mpr (hk.trans hs1)⟩
    · exact_mod_cast (show (0 : ℝ) < ρ / 4 by positivity).trans hs1
    · push_cast
      linarith
  · intro hy
    obtain ⟨b, ⟨t, _, hb1, hb2⟩, hyb⟩ := Set.mem_iUnion₂.mp hy
    have hyb' : dist y (P.ι b.1) < b.2 := hyb
    push_cast at hb2
    change r im.2 < dist y (P.ι im.1)
    have htri := dist_triangle (P.ι im.1) y (P.ι b.1)
    rw [dist_comm (P.ι im.1) y] at htri
    linarith

/-- The closed annulus `{a ≤ d(·, x_i) ≤ b}` about the ideal point `x_i`. -/
private def annulus (P : Presentation X) (i : ℕ) (a b : ℝ) : Set X :=
  {y | a ≤ dist y (P.ι i) ∧ dist y (P.ι i) ≤ b}

/-- The open complements of the closed annuli, intersected over a list of centres. -/
private def annulusCompl (P : Presentation X) (abL : (ℚ × ℚ) × List ℕ) : Set X :=
  ⋂ i ∈ abL.2, (Metric.ball (P.ι i) (abL.1.1 : ℝ) ∪ {y | (abL.1.2 : ℝ) < dist y (P.ι i)})

/-- The complement of `annulusCompl` is the union of the closed annuli. -/
private lemma compl_annulusCompl (P : Presentation X) (abL : (ℚ × ℚ) × List ℕ) :
    (annulusCompl P abL)ᶜ = ⋃ i ∈ abL.2, annulus P i abL.1.1 abL.1.2 := by
  ext y
  simp [annulusCompl, annulus, not_lt]

/-- The complements of closed annuli, intersected over a list of centres, form a c.e. open
family. -/
private lemma isCeOpenFamilyIn_annulusCompl (P : Presentation X) (A : Set ℕ)
    (hP : ComputablePresentationIn P A) : IsCeOpenFamilyIn P A (annulusCompl P) := by
  have hball : IsCeOpenFamilyIn P A fun w : (ℚ × ℚ) × ℕ ↦ Metric.ball (P.ι w.2) (w.1.1 : ℝ) :=
    (isCeOpenFamilyIn_ball P A hP).comp (g := fun w : (ℚ × ℚ) × ℕ ↦ (w.2, w.1.1))
      (Computable.snd.pair (Computable.fst.comp Computable.fst))
  have hgt : IsCeOpenFamilyIn P A fun w : (ℚ × ℚ) × ℕ ↦ {y | (w.1.2 : ℝ) < dist y (P.ι w.2)} :=
    (isCeOpenFamilyIn_lt_dist (κ := ℕ) hP (a := fun k _ ↦ k) (isCauchyName_const P)
      ComputableIn.fst).comp (g := fun w : (ℚ × ℚ) × ℕ ↦ (w.2, w.1.2))
      (Computable.snd.pair (Computable.snd.comp Computable.fst))
  exact (hball.union hgt).biInter_list hP

variable [MeasurableSpace X] [BorelSpace X]

/-- Closed annuli are measurable. -/
private lemma measurableSet_annulus (P : Presentation X) (i : ℕ) (a b : ℝ) :
    MeasurableSet (annulus P i a b) :=
  (measurableSet_le measurable_const (continuous_id.dist continuous_const).measurable).inter
    (measurableSet_le (continuous_id.dist continuous_const).measurable measurable_const)

/-- Effective Baire category step: inside every rational interval there is a rational
subinterval of length `< 2^{-k}` whose closed annuli about `x_0, …, x_k` have total measure
`< 2^{-k}`. -/
private lemma exists_small_annuli (P : Presentation X) (μ : Measure X) [IsFiniteMeasure μ]
    (k : ℕ) {lo hi : ℚ} (hlohi : lo < hi) :
    ∃ lo' hi' : ℚ, lo < lo' ∧ lo' < hi' ∧ hi' < hi ∧ hi' - lo' < (2 : ℚ)⁻¹ ^ k ∧
      (μ (annulusCompl P ((lo', hi'), List.range (k + 1)))ᶜ).toReal <
        (((2 : ℚ)⁻¹ ^ k : ℚ) : ℝ) := by
  set ε : ℝ := (2 : ℝ)⁻¹ ^ k with hε
  have hε0 : 0 < ε := by positivity
  -- radii carrying sphere mass about `x_0, …, x_k` are countably many
  have hbad : Set.Countable (⋃ i ∈ Finset.range (k + 1),
      {t : ℝ | 0 < μ {y | dist y (P.ι i) = t}}) :=
    (Finset.range (k + 1)).countable_toSet.biUnion fun i _ ↦
      Measure.countable_meas_level_set_pos (continuous_id.dist continuous_const).measurable
  obtain ⟨t, ht, htI⟩ := (hbad.dense_compl ℝ).exists_between
    (show ((lo : ℚ) : ℝ) < (hi : ℝ) by exact_mod_cast hlohi)
  have hnull : ∀ i ∈ Finset.range (k + 1), μ {y | dist y (P.ι i) = t} = 0 := by
    intro i hi
    by_contra h
    exact ht (mem_biUnion (Finset.mem_coe.mpr hi) (pos_iff_ne_zero.mpr h))
  -- continuity from above along the annuli `{t - 1/(n+1) ≤ d ≤ t + 1/(n+1)}`
  have hlim : ∀ i, Tendsto (fun n : ℕ ↦ μ (annulus P i (t - 1 / ((n : ℝ) + 1))
      (t + 1 / ((n : ℝ) + 1)))) atTop (𝓝 (μ {y | dist y (P.ι i) = t})) := by
    intro i
    have hanti : Antitone fun n : ℕ ↦ annulus P i (t - 1 / ((n : ℝ) + 1))
        (t + 1 / ((n : ℝ) + 1)) := by
      intro n n' hnn' y hy
      have h : 1 / ((n' : ℝ) + 1) ≤ 1 / ((n : ℝ) + 1) :=
        one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hnn' 1)
      exact ⟨by linarith [hy.1], by linarith [hy.2]⟩
    have hinter : (⋂ n : ℕ, annulus P i (t - 1 / ((n : ℝ) + 1)) (t + 1 / ((n : ℝ) + 1))) =
        {y | dist y (P.ι i) = t} := by
      ext y
      simp only [mem_iInter, annulus, mem_ofPred_eq]
      constructor
      · intro hy
        refine le_antisymm (le_of_forall_pos_lt_add fun δ hδ ↦ ?_)
          (le_of_forall_pos_lt_add fun δ hδ ↦ ?_)
        · obtain ⟨n, hn⟩ := exists_nat_one_div_lt hδ
          linarith [(hy n).2]
        · obtain ⟨n, hn⟩ := exists_nat_one_div_lt hδ
          linarith [(hy n).1]
      · intro hy n
        have h : 0 < 1 / ((n : ℝ) + 1) := by positivity
        exact ⟨by linarith, by linarith⟩
    have h := tendsto_measure_iInter_atTop (μ := μ)
      (fun n ↦ (measurableSet_annulus P i _ _).nullMeasurableSet) hanti
      ⟨0, measure_ne_top μ _⟩
    rwa [hinter] at h
  have hsum : Tendsto (fun n : ℕ ↦ ∑ i ∈ Finset.range (k + 1), μ (annulus P i
      (t - 1 / ((n : ℝ) + 1)) (t + 1 / ((n : ℝ) + 1)))) atTop (𝓝 0) := by
    have h := tendsto_finsetSum (Finset.range (k + 1)) fun i _ ↦ hlim i
    rwa [Finset.sum_eq_zero hnull] at h
  obtain ⟨N, hN⟩ := (hsum.eventually (gt_mem_nhds (ENNReal.ofReal_pos.mpr hε0))).exists
  -- choose rational endpoints close to `t`
  set δ : ℝ := min (1 / ((N : ℝ) + 1)) (ε / 2) with hδ
  have hδ0 : 0 < δ := lt_min (by positivity) (by positivity)
  obtain ⟨lo', hlo'1, hlo'2⟩ := exists_rat_btwn (show max (t - δ) (lo : ℝ) < t from
    max_lt (by linarith) htI.1)
  obtain ⟨hi', hhi'1, hhi'2⟩ := exists_rat_btwn (show t < min (t + δ) (hi : ℝ) from
    lt_min (by linarith) htI.2)
  have h1 := le_max_left (t - δ) (lo : ℝ)
  have h2 := le_max_right (t - δ) (lo : ℝ)
  have h3 := min_le_left (t + δ) (hi : ℝ)
  have h4 := min_le_right (t + δ) (hi : ℝ)
  have h5 := min_le_left (1 / ((N : ℝ) + 1)) (ε / 2)
  have h6 := min_le_right (1 / ((N : ℝ) + 1)) (ε / 2)
  refine ⟨lo', hi', by exact_mod_cast h2.trans_lt hlo'1, by exact_mod_cast hlo'2.trans hhi'1,
    by exact_mod_cast hhi'2.trans_le h4, ?_, ?_⟩
  · have : ((hi' - lo' : ℚ) : ℝ) < (((2 : ℚ)⁻¹ ^ k : ℚ) : ℝ) := by
      push_cast
      linarith
    exact_mod_cast this
  · push_cast
    refine ENNReal.toReal_lt_of_lt_ofReal (lt_of_le_of_lt ?_ hN)
    rw [compl_annulusCompl]
    refine (measure_mono ?_).trans (measure_biUnion_finset_le (Finset.range (k + 1)) _)
    intro y hy
    simp only [mem_iUnion, List.mem_range] at hy
    obtain ⟨i, hi, hy⟩ := hy
    simp only [mem_iUnion, Finset.mem_range]
    exact ⟨i, hi, by linarith [hy.1], by linarith [hy.2]⟩


/-- The search condition of one step of the nested-interval construction: either the input
interval is degenerate, or the output is a rational subinterval of length `< 2^{-k}` whose
closed annuli about `x_0, …, x_k` have total measure `< 2^{-k}`. -/
private def StepGood (P : Presentation X) (μ : Measure X) (w : (ℕ × (ℚ × ℚ)) × (ℚ × ℚ)) :
    Prop :=
  w.1.2.2 ≤ w.1.2.1 ∨ (w.1.2.1 < w.2.1 ∧ w.2.1 < w.2.2 ∧ w.2.2 < w.1.2.2 ∧
    w.2.2 - w.2.1 < (2 : ℚ)⁻¹ ^ w.1.1 ∧
    (μ (annulusCompl P (w.2, List.range (w.1.1 + 1)))ᶜ).toReal < (((2 : ℚ)⁻¹ ^ w.1.1 : ℚ) : ℝ))

/-- The step condition is relatively enumerable. -/
private lemma isREIn_stepGood (P : Presentation X) (A : Set ℕ) (μ : Measure X)
    [IsProbabilityMeasure μ] (hP : ComputablePresentationIn P A)
    (hμ : IsComputableMeasureIn P A μ) : IsREIn A (StepGood P μ) := by
  have hle : Computable fun w : (ℕ × (ℚ × ℚ)) × (ℚ × ℚ) ↦ decide (w.1.2.2 ≤ w.1.2.1) :=
    (Primrec.not.to_comp.comp (computable₂_ratLt.comp
      (Computable.fst.comp (Computable.snd.comp Computable.fst))
      (Computable.snd.comp (Computable.snd.comp Computable.fst)))).of_eq fun w ↦ by
        rw [← decide_not]
        simp only [not_lt]
  have hlt : ∀ {f g : (ℕ × (ℚ × ℚ)) × (ℚ × ℚ) → ℚ}, Computable f → Computable g →
      IsREIn A fun w ↦ f w < g w := fun hf hg ↦
    isREIn_of_computable_decide (computable₂_ratLt.comp hf hg)
  have hk : Computable fun w : (ℕ × (ℚ × ℚ)) × (ℚ × ℚ) ↦ w.1.1 :=
    Computable.fst.comp Computable.fst
  have hmeas := (hμ.isREIn_measure_compl_lt (isCeOpenFamilyIn_annulusCompl P A hP)).comp
    (f := fun w : (ℕ × (ℚ × ℚ)) × (ℚ × ℚ) ↦
      ((w.2, List.range (w.1.1 + 1)), (2 : ℚ)⁻¹ ^ w.1.1))
    ((Computable.snd.pair (Primrec.list_range.to_comp.comp (Computable.succ.comp hk))).pair
      (computable_inv_two_pow.comp hk)).computableIn
  exact (isREIn_of_computable_decide hle).or
    ((hlt (Computable.fst.comp (Computable.snd.comp Computable.fst))
      (Computable.fst.comp Computable.snd)).and
    ((hlt (Computable.fst.comp Computable.snd) (Computable.snd.comp Computable.snd)).and
    ((hlt (Computable.snd.comp Computable.snd)
      (Computable.snd.comp (Computable.snd.comp Computable.fst))).and
    ((hlt (computable₂_ratSub.comp (Computable.snd.comp Computable.snd)
      (Computable.fst.comp Computable.snd)) (computable_inv_two_pow.comp hk)).and hmeas))))

/-- A rational interval, replaced by `(1, 2)` when it is not a nonempty interval of positive
numbers. -/
private def validInterval (ab : ℚ × ℚ) : ℚ × ℚ :=
  cond (decide (0 < ab.1) && decide (ab.1 < ab.2)) ab (1, 2)

/-- The rational interval coded by `m`, replaced by `(1, 2)` when it is not a nonempty interval
of positive numbers. -/
private def startInterval (m : ℕ) : ℚ × ℚ :=
  validInterval ((@Encodable.decode (ℚ × ℚ) Primcodable.toEncodable m).getD (1, 2))

/-- The start interval is computable. -/
private lemma computable_startInterval : Computable startInterval := by
  have hv : Computable validInterval :=
    Computable.cond (Primrec.and.to_comp.comp
      (computable₂_ratLt.comp (Computable.const 0) Computable.fst)
      (computable₂_ratLt.comp Computable.fst Computable.snd)) Computable.id
      (Computable.const _)
  exact hv.comp (Computable.option_getD Computable.decode (Computable.const _))

/-- The corrected interval is a nonempty interval of positive numbers. -/
private lemma validInterval_valid (ab : ℚ × ℚ) :
    0 < (validInterval ab).1 ∧ (validInterval ab).1 < (validInterval ab).2 := by
  unfold validInterval
  by_cases h : 0 < ab.1 ∧ ab.1 < ab.2
  · simp [h.1, h.2]
  · rw [not_and_or] at h
    rcases h with h | h <;> simp [h]

/-- The start interval is a nonempty interval of positive numbers. -/
private lemma startInterval_valid (m : ℕ) :
    0 < (startInterval m).1 ∧ (startInterval m).1 < (startInterval m).2 :=
  validInterval_valid _

/-- The start interval of the code of a nonempty interval of positive rationals is itself. -/
private lemma startInterval_encode {a b : ℚ} (ha : 0 < a) (hab : a < b) :
    startInterval (@Encodable.encode (ℚ × ℚ) Primcodable.toEncodable (a, b)) = (a, b) := by
  rw [startInterval, @Encodable.encodek _ Primcodable.toEncodable, Option.getD_some,
    validInterval]
  simp [ha, hab]

/-- Input (I1): an `A`-computable sequence of positive radii, dense in `(0, ∞)`, all of whose
spheres about ideal points are `μ`-null. Blueprint node `erg:null-sphere`. -/
theorem exists_nullSphere_radii (P : Presentation X) (A : Set ℕ) (μ : Measure X)
    [IsProbabilityMeasure μ] (hP : ComputablePresentationIn P A)
    (hμ : IsComputableMeasureIn P A μ) :
    ∃ r : ℕ → ℝ, IsComputableRealFamilyIn A r ∧ (∀ m, 0 < r m) ∧
      (∀ a b : ℝ, 0 < a → a < b → ∃ m, r m ∈ Ioo a b) ∧
      ∀ i m, μ (Metric.sphere (P.ι i) (r m)) = 0 := by
  -- the search step
  have htot : ∀ x : ℕ × (ℚ × ℚ), ∃ y, StepGood P μ (x, y) := by
    rintro ⟨k, lo, hi⟩
    rcases le_or_gt hi lo with h | h
    · exact ⟨(0, 0), Or.inl h⟩
    · obtain ⟨lo', hi', h⟩ := exists_small_annuli P μ k h
      exact ⟨(lo', hi'), Or.inr h⟩
  obtain ⟨g, hg, hgood⟩ := (isREIn_stepGood P A μ hP hμ).exists_computableIn_choice htot
  -- the nested intervals
  obtain ⟨s, hs, hs0, hsucc⟩ : ∃ s : ℕ × ℕ → ℚ × ℚ, ComputableIn {charOracle A} s ∧
      (∀ m, s (m, 0) = startInterval m) ∧ ∀ m k, s (m, k + 1) = g (k, s (m, k)) :=
    ⟨fun mk ↦ Nat.rec (motive := fun _ ↦ ℚ × ℚ) (startInterval mk.1) (fun k ih ↦ g (k, ih)) mk.2,
      ComputableIn.nat_rec ComputableIn.snd
        (computable_startInterval.computableIn.comp ComputableIn.fst) (hg.comp ComputableIn.snd),
      fun _ ↦ rfl, fun _ _ ↦ rfl⟩
  have hstep : ∀ m k, 0 < (s (m, k)).1 ∧ (s (m, k)).1 < (s (m, k)).2 ∧
      ((s (m, k)).1 < (s (m, k + 1)).1 ∧ (s (m, k + 1)).1 < (s (m, k + 1)).2 ∧
        (s (m, k + 1)).2 < (s (m, k)).2 ∧
        (s (m, k + 1)).2 - (s (m, k + 1)).1 < (2 : ℚ)⁻¹ ^ k ∧
        (μ (annulusCompl P (s (m, k + 1), List.range (k + 1)))ᶜ).toReal <
          (((2 : ℚ)⁻¹ ^ k : ℚ) : ℝ)) := by
    intro m k
    have hvalid : ∀ k, 0 < (s (m, k)).1 ∧ (s (m, k)).1 < (s (m, k)).2 := by
      intro k
      induction k with
      | zero =>
        rw [hs0]
        exact startInterval_valid m
      | succ k ih =>
        rcases hgood (k, s (m, k)) with h | h
        · exact absurd h (not_le.mpr ih.2)
        · rw [hsucc]
          exact ⟨ih.1.trans h.1, h.2.1⟩
    refine ⟨(hvalid k).1, (hvalid k).2, ?_⟩
    rcases hgood (k, s (m, k)) with h | h
    · exact absurd h (not_le.mpr (hvalid k).2)
    · rw [hsucc]
      exact h
  -- the limit
  let r : ℕ → ℝ := fun m ↦ ⨆ k, ((s (m, k)).1 : ℝ)
  have hmono : ∀ m, Monotone fun k ↦ ((s (m, k)).1 : ℝ) := fun m ↦
    monotone_nat_of_le_succ fun k ↦ by exact_mod_cast (hstep m k).2.2.1.le
  have hanti : ∀ m, Antitone fun k ↦ ((s (m, k)).2 : ℝ) := fun m ↦
    antitone_nat_of_succ_le fun k ↦ by exact_mod_cast (hstep m k).2.2.2.2.1.le
  have hlohi : ∀ m k j, ((s (m, k)).1 : ℝ) ≤ (s (m, j)).2 := by
    intro m k j
    calc ((s (m, k)).1 : ℝ) ≤ (s (m, max k j)).1 := hmono m (le_max_left k j)
      _ ≤ (s (m, max k j)).2 := by exact_mod_cast (hstep m (max k j)).2.1.le
      _ ≤ (s (m, j)).2 := hanti m (le_max_right k j)
  have hbdd : ∀ m, BddAbove (range fun k ↦ ((s (m, k)).1 : ℝ)) := fun m ↦
    ⟨(s (m, 0)).2, by rintro _ ⟨k, rfl⟩; exact hlohi m k 0⟩
  have hr : ∀ m k, ((s (m, k)).1 : ℝ) < r m ∧ r m < (s (m, k)).2 := by
    intro m k
    constructor
    · calc ((s (m, k)).1 : ℝ) < (s (m, k + 1)).1 := by exact_mod_cast (hstep m k).2.2.1
        _ ≤ r m := le_ciSup (hbdd m) (k + 1)
    · calc r m ≤ (s (m, k + 1)).2 := ciSup_le fun j ↦ hlohi m j (k + 1)
        _ < (s (m, k)).2 := by exact_mod_cast (hstep m k).2.2.2.2.1
  refine ⟨r, ?_, fun m ↦ ?_, fun a b ha hab ↦ ?_, fun i m ↦ ?_⟩
  · -- midpoints of the intervals approximate the limit
    refine ⟨fun mp ↦ ((s (mp.1, mp.2 + 1)).1 + (s (mp.1, mp.2 + 1)).2) / 2, ?_, fun m p ↦ ?_⟩
    · have h1 : ComputableIn {charOracle A} fun mp : ℕ × ℕ ↦ s (mp.1, mp.2 + 1) :=
        hs.comp (ComputableIn.fst.pair (ComputableIn.succ.comp ComputableIn.snd))
      have h2 : Computable fun q : ℚ × ℚ ↦ (q.1 + q.2) / 2 :=
        computable_ratHalf.comp computable₂_ratAdd
      exact h2.computableIn.comp h1
    · have hw := (hstep m p).2.2.2.2.2.1
      have hw' := (Rat.cast_lt (K := ℝ)).mpr hw
      push_cast at hw'
      have h1 := hr m (p + 1)
      rw [abs_lt]
      push_cast
      constructor <;> linarith
  · exact (Rat.cast_pos.mpr (hstep m 0).1).trans (hr m 0).1
  · obtain ⟨a', ha'1, ha'2⟩ := exists_rat_btwn hab
    obtain ⟨b', hb'1, hb'2⟩ := exists_rat_btwn ha'2
    have ha' : (0 : ℚ) < a' := by exact_mod_cast ha.trans ha'1
    have hab' : a' < b' := by exact_mod_cast hb'1
    refine ⟨@Encodable.encode (ℚ × ℚ) Primcodable.toEncodable (a', b'), ?_, ?_⟩
    · have h := (hr (@Encodable.encode (ℚ × ℚ) Primcodable.toEncodable (a', b')) 0).1
      rw [hs0, startInterval_encode ha' hab'] at h
      exact ha'1.trans h
    · have h := (hr (@Encodable.encode (ℚ × ℚ) Primcodable.toEncodable (a', b')) 0).2
      rw [hs0, startInterval_encode ha' hab'] at h
      exact h.trans hb'2
  · -- the sphere lies in the small annuli of all stages `k ≥ i`
    have hsmall : ∀ k, i ≤ k → (μ (Metric.sphere (P.ι i) (r m))).toReal < (2 : ℝ)⁻¹ ^ k := by
      intro k hik
      have h := (hstep m k).2.2.2.2.2.2
      push_cast at h
      refine lt_of_le_of_lt (ENNReal.toReal_mono (measure_ne_top μ _) (measure_mono ?_)) h
      rw [compl_annulusCompl]
      intro y hy
      have hy' : dist y (P.ι i) = r m := hy
      have h1 := hr m (k + 1)
      simp only [mem_iUnion, List.mem_range]
      exact ⟨i, Nat.lt_succ_of_le hik, by rw [hy']; exact h1.1.le, by rw [hy']; exact h1.2.le⟩
    by_contra hne
    have hpos : 0 < (μ (Metric.sphere (P.ι i) (r m))).toReal :=
      ENNReal.toReal_pos hne (measure_ne_top μ _)
    obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one hpos (show (2 : ℝ)⁻¹ < 1 by norm_num)
    have h := hsmall (k + i) (Nat.le_add_left i k)
    have hle : (2 : ℝ)⁻¹ ^ (k + i) ≤ (2 : ℝ)⁻¹ ^ k :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) (Nat.le_add_right k i)
    linarith

end Kolmogorov.PointToSet
