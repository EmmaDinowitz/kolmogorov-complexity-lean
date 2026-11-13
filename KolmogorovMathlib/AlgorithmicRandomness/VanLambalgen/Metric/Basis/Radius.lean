/-
Copyright (c) 2026 Emma Dinowitz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emma Dinowitz
-/
import KolmogorovMathlib.AlgorithmicRandomness.VanLambalgen.Metric.Defs
import KolmogorovMathlib.Oracle.Search
import Mathlib.Topology.Algebra.Module.Cardinality

/-!
# Radii with null spheres: the nested-interval search

For a finite measure `μ` computable relative to `A`, with total mass computable relative to `A`,
on a presentation whose metric table is computable relative to `A`, every ideal point `ι i` and
every dyadic interval `(2^{-(p+1)}, 2^{-p})` carry a nested sequence of rational intervals
`(lo n, hi n)`, computable relative to `A` uniformly in `(i, p, n)`, whose widths tend to `0` and
whose open annuli `{lo n < dist (·, ι i) < hi n}` have measure at most `2^{-(n-1)}`
(`exists_nestedRadii`). The common limit of the intervals is a radius whose sphere is `μ`-null.

The search: the measure of the closed annulus `{a ≤ dist (·, ι i) ≤ b}` is upper semicomputable
relative to `A`, as the total mass minus the measure of the c.e. open set
`{dist < a} ∪ {dist > b}` (by (M1), `IsComputableMeasureIn.lowerSemicomputable_ceOpen`). Inside
every rational interval some short closed annulus has small measure: only countably many spheres
about `ι i` have positive measure, and the closed annuli about a null sphere shrink to it. So a
relative search (`IsREIn.exists_computableIn_choice`) finds the next interval.

## Main declarations

* `exists_nestedRadii` (blueprint node `vlm:ad-basis-exists`): the nested intervals.

Used by `AlgorithmicRandomness/VanLambalgen/Metric/Basis.lean`.
-/

namespace Kolmogorov.PointToSet

open MeasureTheory Set Filter
open scoped ENNReal Topology

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] {P : Presentation X} {A : Set ℕ}
  {μ : Measure X}

/-- The closed annulus `{a ≤ dist (·, c) ≤ b}`. -/
private def closedAnnulus (c : X) (a b : ℚ) : Set X :=
  {y | (a : ℝ) ≤ dist y c ∧ dist y c ≤ b}

/-- The complement of the closed annulus `{a ≤ dist (·, c) ≤ b}`, an open set. -/
private def annulusCompl (c : X) (a b : ℚ) : Set X :=
  {y | dist y c < a} ∪ {y | (b : ℝ) < dist y c}

omit [MeasurableSpace X] in
private lemma compl_annulusCompl (c : X) (a b : ℚ) :
    (annulusCompl c a b)ᶜ = closedAnnulus c a b := by
  ext y
  simp [annulusCompl, closedAnnulus, not_lt]

omit [MeasurableSpace X] in
private lemma isOpen_annulusCompl (c : X) (a b : ℚ) : IsOpen (annulusCompl c a b) :=
  (isOpen_lt (continuous_id.dist continuous_const) continuous_const).union
    (isOpen_lt continuous_const (continuous_id.dist continuous_const))

omit [MeasurableSpace X] in
/-- The complements of the closed annuli about the ideal points are c.e. open, uniformly in the
centre index and the two rational radii. -/
private lemma isCeOpenFamilyIn_annulusCompl (hP : ComputablePresentationIn P A) :
    IsCeOpenFamilyIn P A fun w : ℕ × (ℚ × ℚ) ↦ annulusCompl (P.ι w.1) w.2.1 w.2.2 := by
  have hn : ∀ i, IsCauchyName P (P.ι i) fun _ ↦ i := isCauchyName_const P
  have hc : ComputableIn {charOracle A} fun ip : ℕ × ℕ ↦ ip.1 := ComputableIn.fst
  have h1 := (isCeOpenFamilyIn_dist_lt hP hn hc).comp
    (Computable.fst.pair (Computable.fst.comp Computable.snd) :
      Computable fun w : ℕ × (ℚ × ℚ) ↦ (w.1, w.2.1))
  have h2 := (isCeOpenFamilyIn_lt_dist hP hn hc).comp
    (Computable.fst.pair (Computable.snd.comp Computable.snd) :
      Computable fun w : ℕ × (ℚ × ℚ) ↦ (w.1, w.2.2))
  exact h1.union h2

/-- The measure of a closed annulus about an ideal point is upper semicomputable relative to `A`,
uniformly in the centre index and the radii: total mass minus a lower semicomputable measure. -/
private lemma isREIn_measure_closedAnnulus_lt [BorelSpace X] [IsFiniteMeasure μ]
    (hP : ComputablePresentationIn P A) (hμ : IsComputableMeasureIn P A μ)
    (hmass : IsComputableRealFamilyIn A fun _ : Unit ↦ (μ Set.univ).toReal) :
    IsREIn A fun w : (ℕ × (ℚ × ℚ)) × ℚ ↦
      (μ (closedAnnulus (P.ι w.1.1) w.1.2.1 w.1.2.2)).toReal < (w.2 : ℝ) := by
  have hlow := hμ.lowerSemicomputable_ceOpen (isCeOpenFamilyIn_annulusCompl hP)
  have hm := birkhoff_computableIn_lt A _ hmass
  have h1 : IsREIn A fun v : ((ℕ × (ℚ × ℚ)) × ℚ) × ℚ ↦ (μ Set.univ).toReal < (v.2 : ℝ) :=
    hm.comp ((Computable.const ()).pair Computable.snd).computableIn
  have h2 : IsREIn A fun v : ((ℕ × (ℚ × ℚ)) × ℚ) × ℚ ↦
      (((v.2 - v.1.2 : ℚ)) : ℝ) < (μ (annulusCompl (P.ι v.1.1.1) v.1.1.2.1 v.1.1.2.2)).toReal :=
    hlow.comp ((Computable.fst.comp Computable.fst).pair
      (computable₂_ratSub.comp Computable.snd (Computable.snd.comp Computable.fst))).computableIn
  have heq : (fun w : (ℕ × (ℚ × ℚ)) × ℚ ↦
      (μ (closedAnnulus (P.ι w.1.1) w.1.2.1 w.1.2.2)).toReal < (w.2 : ℝ)) = fun w ↦
      ∃ t : ℚ, (μ Set.univ).toReal < (t : ℝ) ∧
        (((t - w.2 : ℚ)) : ℝ) < (μ (annulusCompl (P.ι w.1.1) w.1.2.1 w.1.2.2)).toReal := by
    funext w
    have hU := isOpen_annulusCompl (P.ι w.1.1) w.1.2.1 w.1.2.2
    have hcomp : (μ (closedAnnulus (P.ι w.1.1) w.1.2.1 w.1.2.2)).toReal =
        (μ Set.univ).toReal - (μ (annulusCompl (P.ι w.1.1) w.1.2.1 w.1.2.2)).toReal := by
      rw [← compl_annulusCompl, measure_compl hU.measurableSet (measure_ne_top _ _),
        ENNReal.toReal_sub_of_le (measure_mono (Set.subset_univ _)) (measure_ne_top _ _)]
    rw [hcomp]
    apply propext
    constructor
    · intro h
      obtain ⟨t, ht1, ht2⟩ := exists_rat_btwn (show (μ Set.univ).toReal <
          (μ (annulusCompl (P.ι w.1.1) w.1.2.1 w.1.2.2)).toReal + w.2 by linarith)
      refine ⟨t, ht1, ?_⟩
      push_cast
      linarith
    · rintro ⟨t, ht1, ht2⟩
      push_cast at ht2
      linarith
  rw [heq]
  exact (h1.and h2).exists

/-- Inside every rational interval there is a closed annulus about `c` of arbitrarily small
width and measure: only countably many spheres about `c` have positive measure, and the closed
annuli about a null sphere shrink to it. -/
private lemma exists_closedAnnulus_lt [BorelSpace X] [IsFiniteMeasure μ] (c : X) {a b : ℚ}
    (hab : a < b) {ε : ℝ} (hε : 0 < ε) {δ : ℚ} (hδ : 0 < δ) :
    ∃ a' b' : ℚ, a < a' ∧ a' < b' ∧ b' < b ∧ b' - a' < δ ∧
      (μ (closedAnnulus c a' b')).toReal < ε := by
  have hg : Measurable fun y : X ↦ dist y c := (continuous_id.dist continuous_const).measurable
  have hS := Measure.countable_meas_level_set_pos (μ := μ) hg
  obtain ⟨s, hs, hsab⟩ := (hS.dense_compl ℝ).exists_between
    (show (a : ℝ) < b by exact_mod_cast hab)
  have hs0 : μ {y | dist y c = s} = 0 := by
    simpa using hs
  -- closed annuli of width `2 / (j + 1)` about the null sphere shrink to it
  let K : ℕ → Set X := fun j ↦ {y | |dist y c - s| ≤ 1 / ((j : ℝ) + 1)}
  have hKanti : Antitone K := by
    intro j k hjk y hy
    simp only [K, Set.mem_ofPred_eq] at hy ⊢
    refine hy.trans ?_
    gcongr
  have hKmeas : ∀ j, NullMeasurableSet (K j) μ := fun j ↦
    (isClosed_le (by fun_prop) continuous_const).measurableSet.nullMeasurableSet
  have hKinter : ⋂ j, K j = {y | dist y c = s} := by
    ext y
    simp only [K, Set.mem_iInter, Set.mem_ofPred_eq]
    constructor
    · intro h
      by_contra hne
      have hpos : 0 < |dist y c - s| := abs_pos.mpr (sub_ne_zero.mpr hne)
      obtain ⟨j, hj⟩ := exists_nat_one_div_lt hpos
      linarith [h j]
    · intro h j
      rw [h, sub_self, abs_zero]
      positivity
  have hlim := tendsto_measure_iInter_atTop hKmeas hKanti ⟨0, measure_ne_top μ _⟩
  rw [hKinter, hs0] at hlim
  obtain ⟨j, hj⟩ := (hlim.eventually (gt_mem_nhds (ENNReal.ofReal_pos.mpr hε))).exists
  set η : ℝ := min (1 / ((j : ℝ) + 1)) ((δ : ℝ) / 2) with hη
  have hδ' : (0 : ℝ) < δ := by exact_mod_cast hδ
  have hη0 : 0 < η := lt_min (by positivity) (by positivity)
  have hηj : η ≤ 1 / ((j : ℝ) + 1) := min_le_left _ _
  have hηδ : η ≤ δ / 2 := min_le_right _ _
  obtain ⟨a', ha'1, ha'2⟩ :=
    exists_rat_btwn (show max (a : ℝ) (s - η) < s from max_lt hsab.1 (by linarith))
  obtain ⟨b', hb'1, hb'2⟩ :=
    exists_rat_btwn (show s < min (b : ℝ) (s + η) from lt_min hsab.2 (by linarith))
  have ha'a : (a : ℝ) < a' := (le_max_left _ _).trans_lt ha'1
  have ha's : s - η < a' := (le_max_right _ _).trans_lt ha'1
  have hb'b : (b' : ℝ) < b := hb'2.trans_le (min_le_left _ _)
  have hb's : (b' : ℝ) < s + η := hb'2.trans_le (min_le_right _ _)
  refine ⟨a', b', by exact_mod_cast ha'a, by exact_mod_cast ha'2.trans hb'1,
    by exact_mod_cast hb'b, ?_, ?_⟩
  · have h : ((b' - a' : ℚ) : ℝ) < δ := by
      push_cast
      linarith
    exact_mod_cast h
  · have hsub : closedAnnulus c a' b' ⊆ K j := by
      intro y hy
      simp only [closedAnnulus, K, Set.mem_ofPred_eq] at hy ⊢
      rw [abs_le]
      constructor <;> linarith [hy.1, hy.2]
    exact ENNReal.toReal_lt_of_lt_ofReal ((measure_mono hsub).trans_lt hj)

/-- The search step relation: from the interval `(a, b)` about the centre `ι i` at level `n`,
a subinterval `(a', b')` of width below `2^{-(n+1)}` whose closed annulus has measure below
`2^{-n}` (any pair is accepted from an empty interval). -/
private def StepRel (P : Presentation X) (μ : Measure X)
    (v : ((ℕ × (ℚ × ℚ)) × ℕ) × (ℚ × ℚ)) : Prop :=
  ¬ v.1.1.2.1 < v.1.1.2.2 ∨
    (v.1.1.2.1 < v.2.1 ∧ v.2.1 < v.2.2 ∧ v.2.2 < v.1.1.2.2 ∧
      v.2.2 - v.2.1 < (2 : ℚ)⁻¹ ^ (v.1.2 + 1) ∧
      (μ (closedAnnulus (P.ι v.1.1.1) v.2.1 v.2.2)).toReal < (((2 : ℚ)⁻¹ ^ v.1.2 : ℚ) : ℝ))

/-- Strict comparisons of computable rational functions are enumerable. -/
private lemma isREIn_rat_lt {α : Type*} [Primcodable α] {f g : α → ℚ} (hf : Computable f)
    (hg : Computable g) : IsREIn A fun x ↦ f x < g x :=
  isREIn_of_computable_decide (computable₂_ratLt.comp hf hg)

private lemma isREIn_stepRel [BorelSpace X] [IsFiniteMeasure μ]
    (hP : ComputablePresentationIn P A) (hμ : IsComputableMeasureIn P A μ)
    (hmass : IsComputableRealFamilyIn A fun _ : Unit ↦ (μ Set.univ).toReal) :
    IsREIn A (StepRel P μ) := by
  have ha : Computable fun v : ((ℕ × (ℚ × ℚ)) × ℕ) × (ℚ × ℚ) ↦ v.1.1.2.1 :=
    Computable.fst.comp (Computable.snd.comp (Computable.fst.comp Computable.fst))
  have hb : Computable fun v : ((ℕ × (ℚ × ℚ)) × ℕ) × (ℚ × ℚ) ↦ v.1.1.2.2 :=
    Computable.snd.comp (Computable.snd.comp (Computable.fst.comp Computable.fst))
  have ha' : Computable fun v : ((ℕ × (ℚ × ℚ)) × ℕ) × (ℚ × ℚ) ↦ v.2.1 :=
    Computable.fst.comp Computable.snd
  have hb' : Computable fun v : ((ℕ × (ℚ × ℚ)) × ℕ) × (ℚ × ℚ) ↦ v.2.2 :=
    Computable.snd.comp Computable.snd
  have hn : Computable fun v : ((ℕ × (ℚ × ℚ)) × ℕ) × (ℚ × ℚ) ↦ v.1.2 :=
    Computable.snd.comp Computable.fst
  have hnot : IsREIn A fun v : ((ℕ × (ℚ × ℚ)) × ℕ) × (ℚ × ℚ) ↦ ¬ v.1.1.2.1 < v.1.1.2.2 :=
    isREIn_of_computable_decide
      ((Primrec.not.to_comp.comp (computable₂_ratLt.comp ha hb)).of_eq
        fun _ ↦ decide_not.symm)
  have hwidth : IsREIn A fun v : ((ℕ × (ℚ × ℚ)) × ℕ) × (ℚ × ℚ) ↦
      v.2.2 - v.2.1 < (2 : ℚ)⁻¹ ^ (v.1.2 + 1) :=
    isREIn_rat_lt (computable₂_ratSub.comp hb' ha')
      (computable_inv_two_pow.comp (Computable.succ.comp hn))
  have hmeas : IsREIn A fun v : ((ℕ × (ℚ × ℚ)) × ℕ) × (ℚ × ℚ) ↦
      (μ (closedAnnulus (P.ι v.1.1.1) v.2.1 v.2.2)).toReal < (((2 : ℚ)⁻¹ ^ v.1.2 : ℚ) : ℝ) :=
    (isREIn_measure_closedAnnulus_lt hP hμ hmass).comp
      (((Computable.fst.comp (Computable.fst.comp Computable.fst)).pair
        (ha'.pair hb')).pair (computable_inv_two_pow.comp hn)).computableIn
  exact hnot.or ((isREIn_rat_lt ha ha').and ((isREIn_rat_lt ha' hb').and
    ((isREIn_rat_lt hb' hb).and (hwidth.and hmeas))))

/-- **Nested intervals with null-sphere limits.** For every centre index `i` and dyadic level
`p` there are rational intervals `(lo n, hi n)`, computable relative to `A` uniformly in
`((i, p), n)`, starting at `(2^{-(p+1)}, 2^{-p})`, strictly nested, of width below `2^{-n}` from
stage `1` on, whose open annuli about `ι i` at stage `n + 1` have measure at most `2^{-n}`.
Blueprint node `vlm:ad-basis-exists`. -/
theorem exists_nestedRadii [BorelSpace X] [IsFiniteMeasure μ]
    (hP : ComputablePresentationIn P A) (hμ : IsComputableMeasureIn P A μ)
    (hmass : IsComputableRealFamilyIn A fun _ : Unit ↦ (μ Set.univ).toReal) :
    ∃ lo hi : (ℕ × ℕ) × ℕ → ℚ, ComputableIn {charOracle A} lo ∧
      ComputableIn {charOracle A} hi ∧
      ∀ x : ℕ × ℕ, lo (x, 0) = (2 : ℚ)⁻¹ ^ (x.2 + 1) ∧ hi (x, 0) = (2 : ℚ)⁻¹ ^ x.2 ∧
        ∀ n, lo (x, n) < lo (x, n + 1) ∧ lo (x, n + 1) < hi (x, n + 1) ∧
          hi (x, n + 1) < hi (x, n) ∧ hi (x, n + 1) - lo (x, n + 1) < (2 : ℚ)⁻¹ ^ (n + 1) ∧
          μ {y | (lo (x, n + 1) : ℝ) < dist y (P.ι x.1) ∧ dist y (P.ι x.1) < hi (x, n + 1)} ≤
            (2 : ℝ≥0∞)⁻¹ ^ n := by
  -- the search step is total
  have htot : ∀ v : (ℕ × (ℚ × ℚ)) × ℕ, ∃ w : ℚ × ℚ, StepRel P μ (v, w) := by
    rintro ⟨⟨i, a, b⟩, n⟩
    by_cases hab : a < b
    · obtain ⟨a', b', h1, h2, h3, h4, h5⟩ := exists_closedAnnulus_lt (μ := μ) (P.ι i) hab
        (show (0 : ℝ) < (((2 : ℚ)⁻¹ ^ n : ℚ) : ℝ) by positivity)
        (show (0 : ℚ) < (2 : ℚ)⁻¹ ^ (n + 1) by positivity)
      exact ⟨(a', b'), Or.inr ⟨h1, h2, h3, h4, h5⟩⟩
    · exact ⟨(0, 0), Or.inl hab⟩
  obtain ⟨step, hstep, hspec⟩ := (isREIn_stepRel hP hμ hmass).exists_computableIn_choice htot
  -- the nested intervals, by recursion on the stage
  let st : (ℕ × ℕ) × ℕ → ℚ × ℚ := fun x ↦
    @Nat.rec (fun _ ↦ ℚ × ℚ) ((2 : ℚ)⁻¹ ^ (x.1.2 + 1), (2 : ℚ)⁻¹ ^ x.1.2)
      (fun y ih ↦ step ((x.1.1, ih), y)) x.2
  have hst : ComputableIn {charOracle A} st := by
    have hg : ComputableIn {charOracle A} fun x : (ℕ × ℕ) × ℕ ↦
        ((2 : ℚ)⁻¹ ^ (x.1.2 + 1), (2 : ℚ)⁻¹ ^ x.1.2) :=
      ((computable_inv_two_pow.comp (Computable.succ.comp (Computable.snd.comp
        Computable.fst))).pair (computable_inv_two_pow.comp (Computable.snd.comp
          Computable.fst))).computableIn
    have hh : ComputableIn₂ {charOracle A} fun (x : (ℕ × ℕ) × ℕ) (yi : ℕ × (ℚ × ℚ)) ↦
        step ((x.1.1, yi.2), yi.1) :=
      hstep.comp (((ComputableIn.fst.comp (ComputableIn.fst.comp ComputableIn.fst)).pair
        (ComputableIn.snd.comp ComputableIn.snd)).pair (ComputableIn.fst.comp ComputableIn.snd))
    exact ComputableIn.nat_rec (f := fun x : (ℕ × ℕ) × ℕ ↦ x.2)
      (g := fun x : (ℕ × ℕ) × ℕ ↦ ((2 : ℚ)⁻¹ ^ (x.1.2 + 1), (2 : ℚ)⁻¹ ^ x.1.2))
      (h := fun (x : (ℕ × ℕ) × ℕ) (yi : ℕ × (ℚ × ℚ)) ↦ step ((x.1.1, yi.2), yi.1))
      ComputableIn.snd hg hh
  have hst0 : ∀ x : ℕ × ℕ, st (x, 0) = ((2 : ℚ)⁻¹ ^ (x.2 + 1), (2 : ℚ)⁻¹ ^ x.2) :=
    fun _ ↦ rfl
  have hstS : ∀ (x : ℕ × ℕ) n, st (x, n + 1) = step ((x.1, st (x, n)), n) := fun _ _ ↦ rfl
  have hlt : ∀ (x : ℕ × ℕ) n, (st (x, n)).1 < (st (x, n)).2 := by
    intro x n
    induction n with
    | zero =>
      rw [hst0]
      exact pow_lt_pow_right_of_lt_one₀ (by norm_num) (by norm_num) (Nat.lt_succ_self _)
    | succ n ih =>
      rw [hstS]
      rcases hspec ((x.1, st (x, n)), n) with h | h
      · exact (h ih).elim
      · exact h.2.1
  refine ⟨fun x ↦ (st x).1, fun x ↦ (st x).2, ComputableIn.fst.comp hst,
    ComputableIn.snd.comp hst,
    fun x ↦ ⟨congrArg Prod.fst (hst0 x), congrArg Prod.snd (hst0 x), fun n ↦ ?_⟩⟩
  have hs := hspec ((x.1, st (x, n)), n)
  rw [← hstS] at hs
  rcases hs with h | ⟨h1, h2, h3, h4, h5⟩
  · exact (h (hlt x n)).elim
  refine ⟨h1, h2, h3, h4, ?_⟩
  have hsub : {y | ((st (x, n + 1)).1 : ℝ) < dist y (P.ι x.1) ∧
      dist y (P.ι x.1) < (st (x, n + 1)).2} ⊆ closedAnnulus (P.ι x.1) (st (x, n + 1)).1
        (st (x, n + 1)).2 := fun y hy ↦ ⟨hy.1.le, hy.2.le⟩
  refine (measure_mono hsub).trans ?_
  rw [← ENNReal.ofReal_toReal (measure_ne_top μ _)]
  refine (ENNReal.ofReal_le_ofReal h5.le).trans_eq ?_
  rw [Rat.cast_pow, Rat.cast_inv, Rat.cast_ofNat, ENNReal.ofReal_pow (by norm_num),
    ENNReal.ofReal_inv_of_pos (by norm_num), ENNReal.ofReal_ofNat]

end Kolmogorov.PointToSet
