/-
Copyright (c) 2026 Emma Dinowitz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emma Dinowitz
-/
import KolmogorovMathlib.AlgorithmicRandomness.VanLambalgen.Halves
import KolmogorovMathlib.AlgorithmicRandomness.VanLambalgen.Metric.Defs
import KolmogorovMathlib.PointToSet.ComputableMetric.Represented
import KolmogorovMathlib.Interface.ComputableReals.Part01

/-!
# Products of presented spaces and of almost decidable bases

The product presentation `P.prod Q` of `X × Y` (sup metric) is separable, so `X × Y` is second
countable and its product σ-algebra is Borel. For almost decidable bases `B` of `μ` and `C` of `ν`,
the interleaved family `prodBasis B C` is an almost decidable basis of `μ.prod ν`
(`IsAlmostDecidableBasisIn.prod`); its itinerary at `(x, y)` is the interleaving of the
itineraries (`itinerary_prodBasis`), so it carries `μ.prod ν` to `joinMeasure` of the two image
measures (`map_prod_itinerary_prodBasis`).

## Conventions

A sup-metric ball in `X × Y` is the product of the balls of the same radius. The boundary cover of
`B k × Y` is `W × Y` for a boundary cover `W` of `B k`, at a level shifted by a constant bounding
`ν(Y)`.

## Main declarations

* `Presentation.secondCountableTopology` (blueprint node `vlm:prod-presentation`).
* `itinerary_prodBasis`, `map_prod_itinerary_prodBasis` (blueprint node `vlm:prod-basis`).
* `IsAlmostDecidableBasisIn.prod` (blueprint node `vlm:prod-basis`).

Used by `AlgorithmicRandomness/VanLambalgen/Metric/MainResults.lean`.
-/

namespace Kolmogorov.PointToSet

open MeasureTheory
open scoped ENNReal

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]

/-- A presented space is second countable: the ideal points are dense.
Blueprint node `vlm:prod-presentation`. -/
theorem Presentation.secondCountableTopology (P : Presentation X) :
    SecondCountableTopology X := by
  have := P.dense.separableSpace'
  exact UniformSpace.secondCountable_of_separable X

/-- The product presentation has a metric table computable relative to `A` when both factors have:
the sup distance is the maximum of the two coordinate distances, and the maximum of two
approximations within `2^{-p}` is within `2^{-p}`. Blueprint node `vlm:prod-presentation`. -/
theorem Presentation.computablePresentationIn_prod {A : Set ℕ} {P : Presentation X}
    {Q : Presentation Y} (hP : ComputablePresentationIn P A) (hQ : ComputablePresentationIn Q A) :
    ComputablePresentationIn (P.prod Q) A := by
  obtain ⟨qP, hqP, hP'⟩ := hP
  obtain ⟨qQ, hqQ, hQ'⟩ := hQ
  have hu1 : Computable fun w : (ℕ × ℕ) × ℕ =>
      (((Nat.unpair w.1.1).1, (Nat.unpair w.1.2).1), w.2) :=
    (((Primrec.fst.comp (Primrec.unpair.comp (Primrec.fst.comp Primrec.fst))).pair
      (Primrec.fst.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.fst)))).pair
        Primrec.snd).to_comp
  have hu2 : Computable fun w : (ℕ × ℕ) × ℕ =>
      (((Nat.unpair w.1.1).2, (Nat.unpair w.1.2).2), w.2) :=
    (((Primrec.snd.comp (Primrec.unpair.comp (Primrec.fst.comp Primrec.fst))).pair
      (Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.fst)))).pair
        Primrec.snd).to_comp
  refine ⟨fun w => max (qP (((Nat.unpair w.1.1).1, (Nat.unpair w.1.2).1), w.2))
    (qQ (((Nat.unpair w.1.1).2, (Nat.unpair w.1.2).2), w.2)), ?_, fun ij p => ?_⟩
  · exact (ComputableIn₂.comp ComputableReals.primrec_ratMax.to_comp.computableIn₂
      (hqP.comp hu1.computableIn) (hqQ.comp hu2.computableIn)).of_eq fun _ => rfl
  · have h1 := hP' ((Nat.unpair ij.1).1, (Nat.unpair ij.2).1) p
    have h2 := hQ' ((Nat.unpair ij.1).2, (Nat.unpair ij.2).2) p
    change |((max _ _ : ℚ) : ℝ) - max _ _| < _
    push_cast
    exact (abs_max_sub_max_le_max _ _ _ _).trans_lt (max_lt h1 h2)

omit [MetricSpace X] [MetricSpace Y] in
/-- The itinerary of a pair in the interleaved product family is the interleaving of the
itineraries. Blueprint node `vlm:prod-basis`. -/
theorem itinerary_prodBasis (B : ℕ → Set X) (C : ℕ → Set Y) (x : X) (y : Y) :
    itinerary (prodBasis B C) (x, y) = cantorJoin (itinerary B x) (itinerary C y) := by
  funext n
  unfold itinerary prodBasis cantorJoin
  split_ifs with h <;> simp [h]

variable [MeasurableSpace X] [MeasurableSpace Y]

omit [MetricSpace X] [MetricSpace Y] in
/-- The image of a product measure under the itinerary of the interleaved product family is the
joined product of the image measures. Blueprint node `vlm:prod-basis`. -/
theorem map_prod_itinerary_prodBasis {B : ℕ → Set X} {C : ℕ → Set Y} (μ : Measure X)
    (ν : Measure Y) [SFinite ν] (hB : Measurable (itinerary B)) (hC : Measurable (itinerary C)) :
    (μ.prod ν).map (itinerary (prodBasis B C)) =
      joinMeasure (μ.map (itinerary B)) (ν.map (itinerary C)) := by
  unfold joinMeasure
  rw [Measure.map_prod_map μ ν hB hC, Measure.map_map measurable_cantorJoin (hB.prodMap hC)]
  congr 1
  funext p
  exact itinerary_prodBasis B C p.1 p.2

section ceOpen

variable {P : Presentation X} {Q : Presentation Y} {A : Set ℕ}

omit [MeasurableSpace X] [MeasurableSpace Y]

/-- A sup-metric basic ball of the product presentation is the product of the basic balls of the
same radius. -/
private lemma basicBall_prod (n : ℕ) (q : ℚ) :
    basicBall (P.prod Q) (n, q) =
      basicBall P ((Nat.unpair n).1, q) ×ˢ basicBall Q ((Nat.unpair n).2, q) :=
  (ball_prod_same _ _ _).symm

/-- The ideal point of the product presentation at `pair k₁ k₂`. -/
private lemma prod_ι_pair (k₁ k₂ : ℕ) :
    (P.prod Q).ι (Nat.pair k₁ k₂) = (P.ι k₁, Q.ι k₂) := by
  simp only [Presentation.prod, Nat.unpair_pair]

/-- The first projection is represented from the product presentation, above an oracle computing
the metric table of the first factor: a sup-ball is listed into a ball of `X` when a rational
certificate `dist + radius < radius'` holds. -/
private lemma isRepresentedFamilyIn_fst (hP : ComputablePresentationIn P A) :
    IsRepresentedFamilyIn (P.prod Q) P A fun (_ : Unit) (p : X × Y) ↦ p.1 := by
  have hlt := birkhoff_computableIn_lt A _ hP
  refine ⟨fun w ↦ (0 : ℚ) < w.2.1.2 ∧
    dist (P.ι (Nat.unpair w.2.1.1).1) (P.ι w.2.2.1) < ((w.2.2.2 - w.2.1.2 : ℚ) : ℝ),
    ?_, ?_, ?_⟩
  · have h1 : IsREIn A fun w : Unit × (ℕ × ℚ) × (ℕ × ℚ) ↦ (0 : ℚ) < w.2.1.2 :=
      isREIn_of_computable_decide (computable₂_ratLt.comp (Computable.const 0)
        (Computable.snd.comp (Computable.fst.comp Computable.snd)))
    have h2 : IsREIn A fun w : Unit × (ℕ × ℚ) × (ℕ × ℚ) ↦
        dist (P.ι (Nat.unpair w.2.1.1).1) (P.ι w.2.2.1) < ((w.2.2.2 - w.2.1.2 : ℚ) : ℝ) :=
      hlt.comp (((Computable.fst.comp (Primrec.unpair.to_comp.comp
        (Computable.fst.comp (Computable.fst.comp Computable.snd)))).pair
        (Computable.fst.comp (Computable.snd.comp Computable.snd))).pair
        (computable₂_ratSub.comp (Computable.snd.comp (Computable.snd.comp Computable.snd))
          (Computable.snd.comp (Computable.fst.comp Computable.snd)))).computableIn
    exact h1.and h2
  · intro _ b c ⟨hs, hd⟩
    have hd' : dist (P.ι (Nat.unpair b.1).1) (P.ι c.1) < (c.2 : ℝ) - b.2 := by
      push_cast at hd
      exact hd
    have hs' : (0 : ℝ) < b.2 := by exact_mod_cast hs
    refine ⟨hs, ?_, ?_⟩
    · have : (0 : ℝ) < c.2 := by linarith [dist_nonneg (x := P.ι (Nat.unpair b.1).1) (y := P.ι c.1)]
      exact_mod_cast this
    · rintro _ ⟨⟨x, y⟩, hxy, rfl⟩
      rw [show b = (b.1, b.2) from rfl, basicBall_prod] at hxy
      have hx : dist x (P.ι (Nat.unpair b.1).1) < b.2 := hxy.1
      change dist x (P.ι c.1) < c.2
      linarith [dist_triangle x (P.ι (Nat.unpair b.1).1) (P.ι c.1)]
  · intro _ ⟨x, y⟩ c hc
    have hc' : dist x (P.ι c.1) < c.2 := hc
    obtain ⟨t, ht0, ht⟩ := exists_rat_btwn
      (show (0 : ℝ) < ((c.2 : ℝ) - dist x (P.ι c.1)) / 2 by linarith)
    obtain ⟨k₁, hk₁⟩ := Metric.denseRange_iff.mp P.dense x t ht0
    obtain ⟨k₂, hk₂⟩ := Metric.denseRange_iff.mp Q.dense y t ht0
    refine ⟨(Nat.pair k₁ k₂, t), ⟨by exact_mod_cast ht0, ?_⟩, ?_⟩
    · rw [Nat.unpair_pair]
      push_cast
      linarith [dist_triangle (P.ι k₁) x (P.ι c.1), dist_comm (P.ι k₁) x]
    · change dist (x, y) ((P.prod Q).ι (Nat.pair k₁ k₂)) < t
      rw [prod_ι_pair, Prod.dist_eq]
      exact max_lt hk₁ hk₂

/-- The second projection is represented from the product presentation, above an oracle
computing the metric table of the second factor. -/
private lemma isRepresentedFamilyIn_snd (hQ : ComputablePresentationIn Q A) :
    IsRepresentedFamilyIn (P.prod Q) Q A fun (_ : Unit) (p : X × Y) ↦ p.2 := by
  have hlt := birkhoff_computableIn_lt A _ hQ
  refine ⟨fun w ↦ (0 : ℚ) < w.2.1.2 ∧
    dist (Q.ι (Nat.unpair w.2.1.1).2) (Q.ι w.2.2.1) < ((w.2.2.2 - w.2.1.2 : ℚ) : ℝ),
    ?_, ?_, ?_⟩
  · have h1 : IsREIn A fun w : Unit × (ℕ × ℚ) × (ℕ × ℚ) ↦ (0 : ℚ) < w.2.1.2 :=
      isREIn_of_computable_decide (computable₂_ratLt.comp (Computable.const 0)
        (Computable.snd.comp (Computable.fst.comp Computable.snd)))
    have h2 : IsREIn A fun w : Unit × (ℕ × ℚ) × (ℕ × ℚ) ↦
        dist (Q.ι (Nat.unpair w.2.1.1).2) (Q.ι w.2.2.1) < ((w.2.2.2 - w.2.1.2 : ℚ) : ℝ) :=
      hlt.comp (((Computable.snd.comp (Primrec.unpair.to_comp.comp
        (Computable.fst.comp (Computable.fst.comp Computable.snd)))).pair
        (Computable.fst.comp (Computable.snd.comp Computable.snd))).pair
        (computable₂_ratSub.comp (Computable.snd.comp (Computable.snd.comp Computable.snd))
          (Computable.snd.comp (Computable.fst.comp Computable.snd)))).computableIn
    exact h1.and h2
  · intro _ b c ⟨hs, hd⟩
    have hd' : dist (Q.ι (Nat.unpair b.1).2) (Q.ι c.1) < (c.2 : ℝ) - b.2 := by
      push_cast at hd
      exact hd
    have hs' : (0 : ℝ) < b.2 := by exact_mod_cast hs
    refine ⟨hs, ?_, ?_⟩
    · have : (0 : ℝ) < c.2 := by linarith [dist_nonneg (x := Q.ι (Nat.unpair b.1).2) (y := Q.ι c.1)]
      exact_mod_cast this
    · rintro _ ⟨⟨x, y⟩, hxy, rfl⟩
      rw [show b = (b.1, b.2) from rfl, basicBall_prod] at hxy
      have hy : dist y (Q.ι (Nat.unpair b.1).2) < b.2 := hxy.2
      change dist y (Q.ι c.1) < c.2
      linarith [dist_triangle y (Q.ι (Nat.unpair b.1).2) (Q.ι c.1)]
  · intro _ ⟨x, y⟩ c hc
    have hc' : dist y (Q.ι c.1) < c.2 := hc
    obtain ⟨t, ht0, ht⟩ := exists_rat_btwn
      (show (0 : ℝ) < ((c.2 : ℝ) - dist y (Q.ι c.1)) / 2 by linarith)
    obtain ⟨k₁, hk₁⟩ := Metric.denseRange_iff.mp P.dense x t ht0
    obtain ⟨k₂, hk₂⟩ := Metric.denseRange_iff.mp Q.dense y t ht0
    refine ⟨(Nat.pair k₁ k₂, t), ⟨by exact_mod_cast ht0, ?_⟩, ?_⟩
    · rw [Nat.unpair_pair]
      push_cast
      linarith [dist_triangle (Q.ι k₂) y (Q.ι c.1), dist_comm (Q.ι k₂) y]
    · change dist (x, y) ((P.prod Q).ι (Nat.pair k₁ k₂)) < t
      rw [prod_ι_pair, Prod.dist_eq]
      exact max_lt hk₁ hk₂

/-- Products `U i × Y` of a c.e. open family with the whole second factor are c.e. open in the
product presentation, uniformly. -/
private lemma IsCeOpenFamilyIn.prod_univ (hP : ComputablePresentationIn P A) {ι : Type*}
    [Primcodable ι] {U : ι → Set X} (hU : IsCeOpenFamilyIn P A U) :
    IsCeOpenFamilyIn (P.prod Q) A fun i ↦ U i ×ˢ (Set.univ : Set Y) := by
  have h := ((isRepresentedFamilyIn_fst (Q := Q) hP).preimage_ceOpen hU).comp
    (g := fun i : ι ↦ ((), i)) ((Computable.const ()).pair Computable.id)
  simpa only [Set.prod_univ] using h

/-- Products `X × V i` of the whole first factor with a c.e. open family are c.e. open in the
product presentation, uniformly. -/
private lemma IsCeOpenFamilyIn.univ_prod (hQ : ComputablePresentationIn Q A) {ι : Type*}
    [Primcodable ι] {V : ι → Set Y} (hV : IsCeOpenFamilyIn Q A V) :
    IsCeOpenFamilyIn (P.prod Q) A fun i ↦ (Set.univ : Set X) ×ˢ V i := by
  have h := ((isRepresentedFamilyIn_snd (P := P) hQ).preimage_ceOpen hV).comp
    (g := fun i : ι ↦ ((), i)) ((Computable.const ()).pair Computable.id)
  simpa only [Set.univ_prod] using h

/-- A computably decided choice between two c.e. open families is a c.e. open family. -/
private lemma IsCeOpenFamilyIn.ite' {Z : Type*} [MetricSpace Z] {R : Presentation Z}
    {ι : Type*} [Primcodable ι] {U V : ι → Set Z} (hU : IsCeOpenFamilyIn R A U)
    (hV : IsCeOpenFamilyIn R A V) {p : ι → Prop} [DecidablePred p]
    (hp : Computable fun i ↦ decide (p i)) :
    IsCeOpenFamilyIn R A fun i ↦ if p i then U i else V i := by
  have hnp : Computable fun i ↦ decide (¬ p i) :=
    (Primrec.not.to_comp.comp hp).of_eq fun i ↦ by simp
  have h := (hU.ite hp).union (hV.ite hnp)
  refine (funext fun i ↦ ?_ : (fun i ↦ (if p i then U i else ∅) ∪
    (if ¬ p i then V i else ∅)) = fun i ↦ if p i then U i else V i) ▸ h
  by_cases hi : p i <;> simp [hi]

/-- Interleaving: the family which is `U (k / 2, i) × Y` at even `k` and `X × V (k / 2, i)` at
odd `k` is c.e. open in the product presentation, uniformly in `(k, i)`. -/
private lemma IsCeOpenFamilyIn.interleave (hP : ComputablePresentationIn P A)
    (hQ : ComputablePresentationIn Q A) {ι : Type*} [Primcodable ι] {U : ℕ × ι → Set X}
    {V : ℕ × ι → Set Y} (hU : IsCeOpenFamilyIn P A U) (hV : IsCeOpenFamilyIn Q A V) :
    IsCeOpenFamilyIn (P.prod Q) A fun w : ℕ × ι ↦
      if w.1 % 2 = 0 then U (w.1 / 2, w.2) ×ˢ Set.univ else Set.univ ×ˢ V (w.1 / 2, w.2) := by
  have hg : Computable fun w : ℕ × ι ↦ (w.1 / 2, w.2) :=
    (Primrec.nat_div.comp Primrec.fst (Primrec.const 2)).to_comp.pair Computable.snd
  have hp : Computable fun w : ℕ × ι ↦ decide (w.1 % 2 = 0) :=
    (Primrec.eq.comp (Primrec.nat_mod.comp Primrec.fst (Primrec.const 2))
      (Primrec.const 0)).decide.to_comp
  exact ((hU.comp hg).prod_univ hP).ite' ((hV.comp hg).univ_prod hQ) hp

/-- The interleaved product of c.e. open families is c.e. open in the product presentation. -/
private lemma IsCeOpenFamilyIn.prodBasis (hP : ComputablePresentationIn P A)
    (hQ : ComputablePresentationIn Q A) {U : ℕ → Set X} {V : ℕ → Set Y}
    (hU : IsCeOpenFamilyIn P A U) (hV : IsCeOpenFamilyIn Q A V) :
    IsCeOpenFamilyIn (P.prod Q) A (prodBasis U V) := by
  have h := (IsCeOpenFamilyIn.interleave (ι := Unit) hP hQ
    (hU.comp (g := fun w : ℕ × Unit ↦ w.1) Computable.fst)
    (hV.comp (g := fun w : ℕ × Unit ↦ w.1) Computable.fst)).comp
    (g := fun k : ℕ ↦ (k, ())) (Computable.id.pair (Computable.const ()))
  exact h

end ceOpen

omit [MetricSpace X] [MetricSpace Y] [MeasurableSpace X] [MeasurableSpace Y] in
/-- A point lies in the intersection of the product family over the interleaved list of indices
exactly when its coordinates lie in the two intersections. -/
private lemma mem_biInter_prodBasis {B : ℕ → Set X} {C : ℕ → Set Y} (L₁ L₂ : List ℕ)
    (x : X) (y : Y) :
    (x, y) ∈ ⋂ k ∈ L₁.map (2 * ·) ++ L₂.map (2 * · + 1), prodBasis B C k ↔
      x ∈ (⋂ k ∈ L₁, B k) ∧ y ∈ ⋂ k ∈ L₂, C k := by
  simp only [Set.mem_iInter, List.mem_append, List.mem_map]
  constructor
  · intro h
    refine ⟨fun k hk ↦ ?_, fun k hk ↦ ?_⟩
    · have := h (2 * k) (Or.inl ⟨k, hk, rfl⟩)
      simpa [prodBasis] using this
    · have := h (2 * k + 1) (Or.inr ⟨k, hk, rfl⟩)
      simp only [prodBasis, Nat.mul_add_mod_self_left] at this
      simpa [Nat.mul_add_div] using this
  · rintro ⟨h₁, h₂⟩ k (⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩)
    · simpa [prodBasis] using h₁ j hj
    · simp only [prodBasis, Nat.mul_add_mod_self_left]
      simpa [Nat.mul_add_div] using h₂ j hj

/-- An integer power of two bounding a finite measure. -/
private lemma exists_measure_univ_le_two_pow {Z : Type*} [MeasurableSpace Z] (ρ : Measure Z)
    [IsFiniteMeasure ρ] : ∃ c : ℕ, ρ Set.univ ≤ (2 : ℝ≥0∞) ^ c := by
  obtain ⟨c, hc⟩ := ENNReal.exists_nat_gt (measure_ne_top ρ Set.univ)
  refine ⟨c, hc.le.trans ?_⟩
  exact_mod_cast (Nat.lt_two_pow_self).le

/-- Shifting the level by `c` absorbs a factor `2 ^ c`. -/
private lemma inv_two_pow_add_mul_le {a b : ℝ≥0∞} {n c : ℕ} (ha : a ≤ (2 : ℝ≥0∞)⁻¹ ^ (n + c))
    (hb : b ≤ (2 : ℝ≥0∞) ^ c) : a * b ≤ (2 : ℝ≥0∞)⁻¹ ^ n := by
  calc a * b ≤ (2 : ℝ≥0∞)⁻¹ ^ (n + c) * 2 ^ c := mul_le_mul' ha hb
    _ = (2 : ℝ≥0∞)⁻¹ ^ n := by
      rw [pow_add, mul_assoc, ← mul_pow, ENNReal.inv_mul_cancel two_ne_zero ENNReal.ofNat_ne_top,
        one_pow, mul_one]

/-- The interleaved product of almost decidable bases for `μ` and `ν` is an almost decidable basis
for `μ.prod ν` in the product presentation. Blueprint node `vlm:prod-basis`. -/
theorem IsAlmostDecidableBasisIn.prod [OpensMeasurableSpace X] [OpensMeasurableSpace Y]
    {P : Presentation X} {Q : Presentation Y} {A : Set ℕ} {μ : Measure X} {ν : Measure Y}
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] {B : ℕ → Set X} {C : ℕ → Set Y}
    (hP : ComputablePresentationIn P A) (hQ : ComputablePresentationIn Q A)
    (hB : IsAlmostDecidableBasisIn P A μ B) (hC : IsAlmostDecidableBasisIn Q A ν C) :
    IsAlmostDecidableBasisIn (P.prod Q) A (μ.prod ν) (prodBasis B C) := by
  obtain ⟨D, W, hD, hW, hBDW⟩ := hB.exists_exterior
  obtain ⟨D', W', hD', hW', hCDW⟩ := hC.exists_exterior
  obtain ⟨c, hc⟩ := exists_measure_univ_le_two_pow ν
  obtain ⟨c', hc'⟩ := exists_measure_univ_le_two_pow μ
  refine ⟨IsCeOpenFamilyIn.prodBasis hP hQ hB.isCeOpenFamilyIn hC.isCeOpenFamilyIn,
    ⟨prodBasis D D', fun w : ℕ × ℕ ↦ if w.1 % 2 = 0 then W (w.1 / 2, w.2 + c) ×ˢ Set.univ
      else Set.univ ×ˢ W' (w.1 / 2, w.2 + c'), IsCeOpenFamilyIn.prodBasis hP hQ hD hD',
      IsCeOpenFamilyIn.interleave (ι := ℕ) hP hQ
        (hW.comp (g := fun w : ℕ × ℕ ↦ (w.1, w.2 + c))
          (Computable.fst.pair (Primrec.nat_add.comp Primrec.snd (Primrec.const c)).to_comp))
        (hW'.comp (g := fun w : ℕ × ℕ ↦ (w.1, w.2 + c'))
          (Computable.fst.pair (Primrec.nat_add.comp Primrec.snd (Primrec.const c')).to_comp)),
      fun k ↦ ?_⟩, ?_⟩
  · by_cases hk : k % 2 = 0
    · simp only [prodBasis, hk, ↓reduceIte]
      refine ⟨Set.disjoint_prod.mpr (Or.inl (hBDW (k / 2)).1), fun n ↦ ⟨?_, ?_⟩⟩
      · rintro ⟨x, y⟩ hxy
        refine ⟨((hBDW (k / 2)).2 (n + c)).1 fun hx ↦ hxy ?_, trivial⟩
        rcases hx with hx | hx
        · exact Or.inl ⟨hx, trivial⟩
        · exact Or.inr ⟨hx, trivial⟩
      · rw [Measure.prod_prod]
        exact inv_two_pow_add_mul_le ((hBDW (k / 2)).2 (n + c)).2 hc
    · simp only [prodBasis, hk, ↓reduceIte]
      refine ⟨Set.disjoint_prod.mpr (Or.inr (hCDW (k / 2)).1), fun n ↦ ⟨?_, ?_⟩⟩
      · rintro ⟨x, y⟩ hxy
        refine ⟨trivial, ((hCDW (k / 2)).2 (n + c')).1 fun hy ↦ hxy ?_⟩
        rcases hy with hy | hy
        · exact Or.inl ⟨trivial, hy⟩
        · exact Or.inr ⟨trivial, hy⟩
      · rw [Measure.prod_prod, mul_comm]
        exact inv_two_pow_add_mul_le ((hCDW (k / 2)).2 (n + c')).2 hc'
  · obtain ⟨E₁, hE₁, hgen₁⟩ := hB.generates
    obtain ⟨E₂, hE₂, hgen₂⟩ := hC.generates
    refine ⟨fun w : (ℕ × ℚ) × List ℕ ↦ ∃ L : List ℕ × List ℕ,
      E₁ (((Nat.unpair w.1.1).1, w.1.2), L.1) ∧ E₂ (((Nat.unpair w.1.1).2, w.1.2), L.2) ∧
        w.2 = L.1.map (2 * ·) ++ L.2.map (2 * · + 1), ?_, fun b ↦ ?_⟩
    · have hu : Computable fun w : ((ℕ × ℚ) × List ℕ) × (List ℕ × List ℕ) ↦
          Nat.unpair w.1.1.1 :=
        Primrec.unpair.to_comp.comp (Computable.fst.comp (Computable.fst.comp Computable.fst))
      have hq : Computable fun w : ((ℕ × ℚ) × List ℕ) × (List ℕ × List ℕ) ↦ w.1.1.2 :=
        Computable.snd.comp (Computable.fst.comp Computable.fst)
      have h₁ : IsREIn A fun w : ((ℕ × ℚ) × List ℕ) × (List ℕ × List ℕ) ↦
          E₁ (((Nat.unpair w.1.1.1).1, w.1.1.2), w.2.1) :=
        hE₁.comp (((Computable.fst.comp hu).pair hq).pair
          (Computable.fst.comp Computable.snd)).computableIn
      have h₂ : IsREIn A fun w : ((ℕ × ℚ) × List ℕ) × (List ℕ × List ℕ) ↦
          E₂ (((Nat.unpair w.1.1.1).2, w.1.1.2), w.2.2) :=
        hE₂.comp (((Computable.snd.comp hu).pair hq).pair
          (Computable.snd.comp Computable.snd)).computableIn
      have h₃ : IsREIn A fun w : ((ℕ × ℚ) × List ℕ) × (List ℕ × List ℕ) ↦
          w.1.2 = w.2.1.map (2 * ·) ++ w.2.2.map (2 * · + 1) := by
        have hm₁ : Primrec fun w : ((ℕ × ℚ) × List ℕ) × (List ℕ × List ℕ) ↦
            w.2.1.map (2 * ·) :=
          Primrec.list_map (Primrec.fst.comp Primrec.snd)
            (Primrec.nat_mul.comp (Primrec.const 2) Primrec.snd).to₂
        have hm₂ : Primrec fun w : ((ℕ × ℚ) × List ℕ) × (List ℕ × List ℕ) ↦
            w.2.2.map (2 * · + 1) :=
          Primrec.list_map (Primrec.snd.comp Primrec.snd)
            (Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 2) Primrec.snd)
              (Primrec.const 1)).to₂
        exact isREIn_of_computable_decide
          (Primrec.eq.comp (Primrec.snd.comp Primrec.fst)
            (Primrec.list_append.comp hm₁ hm₂)).decide.to_comp
      exact (h₁.and (h₂.and h₃)).exists
    · obtain ⟨n, q⟩ := b
      ext ⟨x, y⟩
      rw [basicBall_prod, Set.mem_prod, hgen₁, hgen₂]
      simp only [Set.mem_iUnion, Set.mem_ofPred_eq, exists_prop]
      constructor
      · rintro ⟨⟨L₁, hL₁, hx⟩, ⟨L₂, hL₂, hy⟩⟩
        exact ⟨_, ⟨(L₁, L₂), hL₁, hL₂, rfl⟩, (mem_biInter_prodBasis L₁ L₂ x y).mpr ⟨hx, hy⟩⟩
      · rintro ⟨_, ⟨⟨L₁, L₂⟩, hL₁, hL₂, rfl⟩, hxy⟩
        obtain ⟨hx, hy⟩ := (mem_biInter_prodBasis L₁ L₂ x y).mp hxy
        exact ⟨⟨L₁, hL₁, hx⟩, ⟨L₂, hL₂, hy⟩⟩

end Kolmogorov.PointToSet
