/-
Copyright (c) 2026 Emma Dinowitz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emma Dinowitz
-/
import KolmogorovMathlib.PointToSet.Measure.Randomness
import KolmogorovMathlib.Oracle.Search

/-!
# Null sets avoided by random points

Two ways in which a null set is disjoint from the random points (E. Dinowitz, *Entropy of
non-invariant measures and orbit complexity of random points*, sketch of Theorem 4.3).

* `IsCeOpenFamilyIn.biInter_list`: intersections of a c.e. open family over the members of a
  list are c.e. open, uniformly in the list.
* `randomPoints_subset_of_isCeOpenIn`: a `μ`-null `A`-effectively closed set contains no point
  that is random relative to an oracle `A` admissible for the measure. Shrinking by `2^{-n}`
  the radii of the balls listed at stage `n` of an enumeration of the complement `U` gives
  finite unions of closed balls inside `U` containing open sets of measure more than
  `1 - 2^{-m}`; the complements of these finite unions of closed balls form a test.
* `exists_oracle_randomPoints_disjoint`: every null set is disjoint from the random points
  relative to all oracles of an upper cone (outer regularity: the null set lies in a `G_δ` null
  set, which a sufficiently strong oracle enumerates).

Blueprint node `meas:effective-null`.
-/

namespace Kolmogorov.PointToSet

open Filter Set MeasureTheory
open scoped Topology ENNReal Computability

variable {X : Type*} [MetricSpace X]

/-- Intersections of a c.e. open family over the members of a list are c.e. open, uniformly in
the list, above an oracle computing the metric table. The empty list gives the whole space.
Blueprint node `meas:effective-null`. -/
theorem IsCeOpenFamilyIn.biInter_list {P : Presentation X} {A : Set ℕ}
    (hP : ComputablePresentationIn P A) {α κ : Type*} [Primcodable α] [Primcodable κ]
    {U : α × κ → Set X} (hU : IsCeOpenFamilyIn P A U) :
    IsCeOpenFamilyIn P A fun aL : α × List κ ↦ ⋂ k ∈ aL.2, U (aL.1, k) := by
  obtain ⟨E, hE, hU⟩ := hU
  have hlt := birkhoff_computableIn_lt A _ hP
  -- the ball `v.1.2` is certified inside a listed ball of `U (v.1.1, v.2.2)`
  let F : (α × (ℕ × ℚ)) × ℕ × κ → Prop := fun v ↦
    ∃ c : ℕ × ℚ, E ((v.1.1, v.2.2), c) ∧
      dist (P.ι v.1.2.1) (P.ι c.1) < ((c.2 - v.1.2.2 : ℚ) : ℝ)
  have hF : IsREIn A F := by
    have h1 : IsREIn A fun w : ((α × (ℕ × ℚ)) × ℕ × κ) × (ℕ × ℚ) ↦
        E ((w.1.1.1, w.1.2.2), w.2) :=
      hE.comp (((Computable.fst.comp (Computable.fst.comp Computable.fst)).pair
        (Computable.snd.comp (Computable.snd.comp Computable.fst))).pair
          Computable.snd).computableIn
    have h2 : IsREIn A fun w : ((α × (ℕ × ℚ)) × ℕ × κ) × (ℕ × ℚ) ↦
        dist (P.ι w.1.1.2.1) (P.ι w.2.1) < ((w.2.2 - w.1.1.2.2 : ℚ) : ℝ) :=
      hlt.comp (((Computable.fst.comp (Computable.snd.comp
        (Computable.fst.comp Computable.fst))).pair (Computable.fst.comp Computable.snd)).pair
        (computable₂_ratSub.comp (Computable.snd.comp Computable.snd)
          (Computable.snd.comp (Computable.snd.comp
            (Computable.fst.comp Computable.fst))))).computableIn
    exact (h1.and h2).exists
  let E2 : (α × List κ) × (ℕ × ℚ) → Prop := fun w ↦
    (0 : ℚ) < w.2.2 ∧ ∀ j (h : j < w.1.2.length), F ((w.1.1, w.2), j, w.1.2.get ⟨j, h⟩)
  have hE2 : IsREIn A E2 := by
    have h3 : IsREIn A fun w : (α × List κ) × (ℕ × ℚ) ↦ (0 : ℚ) < w.2.2 :=
      isREIn_of_computable_decide (computable₂_ratLt.comp (Computable.const 0)
        (Computable.snd.comp Computable.snd))
    have h4 : IsREIn A fun w : (α × List κ) × (ℕ × ℚ) ↦
        ∀ j (h : j < w.1.2.length), F ((w.1.1, w.2), j, w.1.2.get ⟨j, h⟩) :=
      hF.list_forall_get.comp (((Computable.fst.comp Computable.fst).pair
        Computable.snd).pair (Computable.snd.comp Computable.fst)).computableIn
    exact h3.and h4
  refine ⟨E2, hE2, fun aL ↦ ?_⟩
  obtain ⟨a, L⟩ := aL
  ext y
  constructor
  · intro hy
    have hy' : ∀ k ∈ L, y ∈ U (a, k) := fun k hk ↦ mem_iInter₂.mp hy k hk
    -- a common scale below which every basic ball about `y` is certified
    have key : ∀ l : List κ, (∀ k ∈ l, y ∈ U (a, k)) → ∃ δ : ℝ, 0 < δ ∧ ∀ k ∈ l,
        ∀ b : ℕ × ℚ, (b.2 : ℝ) < δ → y ∈ basicBall P b → ∃ c, E ((a, k), c) ∧
          dist (P.ι b.1) (P.ι c.1) < ((c.2 - b.2 : ℚ) : ℝ) := by
      intro l
      induction l with
      | nil => exact fun _ ↦ ⟨1, one_pos, fun k hk ↦ absurd hk List.not_mem_nil⟩
      | cons k l ih =>
        intro hl
        obtain ⟨δ, hδ, hδl⟩ := ih fun k' hk' ↦ hl k' (List.mem_cons_of_mem _ hk')
        have hyk := hl k List.mem_cons_self
        rw [hU] at hyk
        obtain ⟨c, hc, hyc⟩ := mem_iUnion₂.mp hyk
        have hyc' : dist y (P.ι c.1) < c.2 := hyc
        refine ⟨min δ ((c.2 - dist y (P.ι c.1)) / 2), lt_min hδ (by linarith),
          fun k' hk' b hb hyb ↦ ?_⟩
        rcases List.mem_cons.mp hk' with rfl | hk'
        · refine ⟨c, hc, ?_⟩
          have h1 : dist y (P.ι b.1) < b.2 := hyb
          have h2 := hb.trans_le (min_le_right _ _)
          push_cast
          linarith [dist_triangle (P.ι b.1) y (P.ι c.1), dist_comm y (P.ι b.1)]
        · exact hδl k' hk' b (hb.trans_le (min_le_left _ _)) hyb
    obtain ⟨δ, hδ, hδL⟩ := key L hy'
    obtain ⟨b, hb0, hbδ, hyb⟩ := bowenChain_exists_small_ball P y hδ
    exact mem_iUnion₂.mpr ⟨b, ⟨hb0, fun j hj ↦ hδL _ (List.get_mem _ _) b hbδ hyb⟩, hyb⟩
  · intro hy
    obtain ⟨b, ⟨-, hb⟩, hyb⟩ := mem_iUnion₂.mp hy
    refine mem_iInter₂.mpr fun k hk ↦ ?_
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hk
    obtain ⟨c, hc, hbc⟩ := hb j hj
    have hyb' : dist y (P.ι b.1) < b.2 := hyb
    rw [hU]
    refine mem_iUnion₂.mpr ⟨c, hc, ?_⟩
    change dist y (P.ι c.1) < c.2
    push_cast at hbc
    linarith [dist_triangle y (P.ι b.1) (P.ι c.1)]

variable [MeasurableSpace X] [BorelSpace X]

/-- A `μ`-null `A`-effectively closed set contains no random point: if `U` is `A`-c.e. open
with `μ`-null complement and `A` computes the metric table and the probability measure `μ`,
then every point that is `μ`-random relative to `A` lies in `U`.
Blueprint node `meas:effective-null`. -/
theorem randomPoints_subset_of_isCeOpenIn (P : Presentation X) (A : Set ℕ) (μ : Measure X)
    [IsProbabilityMeasure μ] (hP : ComputablePresentationIn P A)
    (hμ : IsComputableMeasureIn P A μ) {U : Set X} (hU : IsCeOpenIn P A U) (hnull : μ Uᶜ = 0) :
    randomPoints P A μ ⊆ U := by
  obtain ⟨E, hE, rfl⟩ := hU
  have hE' : IsREIn A fun w : Unit × (ℕ × ℚ) ↦ E w.2 := hE.comp Computable.snd.computableIn
  obtain ⟨L, hL, hsound, hmono, hexh, -⟩ := hE'.exists_prefixList
  -- the lists of stage `n`, with radii shrunk by `2^{-n}`
  let sh : ℕ × List (ℕ × ℚ) → List (ℕ × ℚ) := fun p ↦
    p.2.map fun b ↦ (b.1, b.2 - (2 ^ p.1 : ℚ)⁻¹)
  have hsh : Computable sh := by
    have h : Computable₂ fun (p : ℕ × List (ℕ × ℚ)) (b : ℕ × ℚ) ↦
        ((b.1, b.2 - (2 ^ p.1 : ℚ)⁻¹) : ℕ × ℚ) :=
      ((Computable.fst.comp Computable.snd).pair (computable₂_ratSub.comp
        (Computable.snd.comp Computable.snd)
        (computable_rat_inv_two_pow.comp (Computable.fst.comp Computable.fst)))).to₂
    exact Computable.list_map Computable.snd h
  let W : ℕ → List (ℕ × ℚ) := fun n ↦ sh (n, L ((), n))
  have hW : ComputableIn {charOracle A} W :=
    hsh.computableIn.comp (ComputableIn.id.pair
      (hL.comp ((Computable.const ()).pair Computable.id).computableIn))
  have hmemW : ∀ n y, y ∈ ballUnion P (W n) ↔
      ∃ b ∈ L ((), n), dist y (P.ι b.1) < ((b.2 - (2 ^ n : ℚ)⁻¹ : ℚ) : ℝ) := by
    intro n y
    simp only [ballUnion, mem_iUnion, exists_prop, W, sh, List.mem_map, basicBall,
      Metric.mem_ball]
    constructor
    · rintro ⟨_, ⟨b, hb, rfl⟩, hy⟩
      exact ⟨b, hb, hy⟩
    · rintro ⟨b, hb, hy⟩
      exact ⟨_, ⟨b, hb, rfl⟩, hy⟩
  have hWmono : Monotone fun n ↦ ballUnion P (W n) := by
    intro n n' hnn' y hy
    rw [hmemW] at hy ⊢
    obtain ⟨b, hb, hyb⟩ := hy
    refine ⟨b, hmono () n n' hnn' b hb, hyb.trans_le ?_⟩
    have h : ((2 : ℚ) ^ n')⁻¹ ≤ ((2 : ℚ) ^ n)⁻¹ :=
      inv_anti₀ (by positivity) (pow_le_pow_right₀ one_le_two hnn')
    exact Rat.cast_le.mpr (sub_le_sub_left h _)
  have hcover : (⋃ b ∈ {b | E b}, basicBall P b) ⊆ ⋃ n, ballUnion P (W n) := by
    intro y hy
    obtain ⟨b, hb, hyb⟩ := mem_iUnion₂.mp hy
    have hyb' : dist y (P.ι b.1) < b.2 := hyb
    obtain ⟨t, ht⟩ := hexh () b hb
    obtain ⟨n₀, hn₀⟩ := exists_pow_lt_of_lt_one (sub_pos.mpr hyb') (show (2 : ℝ)⁻¹ < 1 by norm_num)
    refine mem_iUnion.mpr ⟨max t n₀, (hmemW _ y).mpr ⟨b, hmono () t _ (le_max_left _ _) b ht, ?_⟩⟩
    have h1 : ((2 : ℝ) ^ max t n₀)⁻¹ ≤ ((2 : ℝ) ^ n₀)⁻¹ :=
      inv_anti₀ (by positivity) (pow_le_pow_right₀ one_le_two (le_max_right _ _))
    rw [inv_pow] at hn₀
    push_cast
    linarith
  have hopen : ∀ M : List (ℕ × ℚ), MeasurableSet (ballUnion P M) := fun M ↦
    (isOpen_biUnion fun _ _ ↦ Metric.isOpen_ball).measurableSet
  have hU1 : μ (⋃ b ∈ {b | E b}, basicBall P b) = 1 :=
    (prob_compl_eq_zero_iff (isOpen_biUnion fun _ _ ↦ Metric.isOpen_ball).measurableSet).mp hnull
  have hW1 : ⨆ n, μ (ballUnion P (W n)) = 1 := by
    rw [← hWmono.measure_iUnion]
    exact le_antisymm prob_le_one (hU1 ▸ measure_mono hcover)
  -- choice of a stage of measure more than `1 - 2^{-m}`
  have hG : IsREIn A fun mn : ℕ × ℕ ↦
      (((1 - (2 ^ mn.1 : ℚ)⁻¹ : ℚ)) : ℝ) < (μ (ballUnion P (W mn.2))).toReal := by
    have hmap : ComputableIn {charOracle A} fun mn : ℕ × ℕ ↦ (W mn.2, 1 - (2 ^ mn.1 : ℚ)⁻¹) :=
      (hW.comp ComputableIn.snd).pair (computable₂_ratSub.comp (Computable.const 1)
        (computable_rat_inv_two_pow.comp Computable.fst)).computableIn
    exact hμ.comp hmap
  have htot : ∀ m : ℕ, ∃ n : ℕ,
      (((1 - (2 ^ m : ℚ)⁻¹ : ℚ)) : ℝ) < (μ (ballUnion P (W n))).toReal := by
    intro m
    have hq0 : (0 : ℝ) ≤ ((1 - (2 ^ m : ℚ)⁻¹ : ℚ) : ℝ) := by
      push_cast
      have : ((2 : ℝ) ^ m)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ one_le_two)
      linarith
    have hq1 : ENNReal.ofReal ((1 - (2 ^ m : ℚ)⁻¹ : ℚ) : ℝ) < ⨆ n, μ (ballUnion P (W n)) := by
      rw [hW1, ENNReal.ofReal_lt_one]
      push_cast
      have : (0 : ℝ) < ((2 : ℝ) ^ m)⁻¹ := by positivity
      linarith
    obtain ⟨n, hn⟩ := lt_iSup_iff.mp hq1
    exact ⟨n, (ENNReal.ofReal_lt_iff_lt_toReal hq0 (measure_ne_top _ _)).mp hn⟩
  obtain ⟨g, hg, hgG⟩ := hG.exists_computableIn_choice htot
  -- the test: complements of the closed balls with the shrunk radii
  have hball : IsCeOpenFamilyIn P A fun d : ℕ × ℚ ↦ {w | (d.2 : ℝ) < dist w (P.ι d.1)} :=
    isCeOpenFamilyIn_lt_dist hP (a := fun k _ ↦ k) (fun k ↦ isCauchyName_const P k)
      Computable.fst.computableIn
  have hball' : IsCeOpenFamilyIn P A fun ud : Unit × (ℕ × ℚ) ↦
      {w | (ud.2.2 : ℝ) < dist w (P.ι ud.2.1)} := hball.comp Computable.snd
  let V : ℕ → Set X := fun m ↦ ⋂ k ∈ W (g m), {w | (k.2 : ℝ) < dist w (P.ι k.1)}
  have hV : IsCeOpenFamilyIn P A V :=
    (hball'.biInter_list hP).compIn (g := fun m ↦ ((), W (g m)))
      ((ComputableIn.const ()).pair (hW.comp hg))
  have hUV : ∀ m, (⋃ b ∈ {b | E b}, basicBall P b)ᶜ ⊆ V m := by
    intro m y hy
    refine mem_iInter₂.mpr fun k hk ↦ ?_
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hk
    have hyb : ¬ dist y (P.ι b.1) < b.2 := fun h ↦ hy (mem_iUnion₂.mpr ⟨b, hsound () _ b hb, h⟩)
    change (((b.2 - (2 ^ g m : ℚ)⁻¹ : ℚ)) : ℝ) < dist y (P.ι b.1)
    have : (0 : ℝ) < ((2 : ℝ) ^ g m)⁻¹ := by positivity
    push_cast
    linarith [not_lt.mp hyb]
  have hVW : ∀ m, V m ⊆ (ballUnion P (W (g m)))ᶜ := by
    intro m y hy hyW
    obtain ⟨b, hb, hyb⟩ := mem_iUnion₂.mp hyW
    have h1 : dist y (P.ι b.1) < b.2 := hyb
    have h2 : (b.2 : ℝ) < dist y (P.ι b.1) := mem_iInter₂.mp hy b hb
    exact (lt_asymm h1 h2).elim
  have hμV : ∀ m, μ (V m) ≤ (2 : ℝ≥0∞)⁻¹ ^ m := by
    intro m
    refine (measure_mono (hVW m)).trans ?_
    have h1 := hgG m
    have h2 : (μ (ballUnion P (W (g m)))ᶜ).toReal = 1 - (μ (ballUnion P (W (g m)))).toReal := by
      rw [prob_compl_eq_one_sub (hopen _), ENNReal.toReal_sub_of_le prob_le_one ENNReal.one_ne_top,
        ENNReal.toReal_one]
    refine (ENNReal.toReal_le_toReal (measure_ne_top _ _) (by simp)).mp ?_
    rw [h2, ENNReal.toReal_pow, ENNReal.toReal_inv, ENNReal.toReal_ofNat, inv_pow]
    push_cast at h1
    linarith
  intro x hx
  obtain ⟨m, hm⟩ := hx V ⟨hV, hμV⟩
  by_contra hxU
  exact hm (hUV m hxU)

/-- Every null set is disjoint from the random points relative to all oracles of an upper
cone. Blueprint node `meas:effective-null`. -/
theorem exists_oracle_randomPoints_disjoint (P : Presentation X) (μ : Measure X)
    [IsFiniteMeasure μ] {N : Set X} (hN : μ N = 0) :
    ∃ C : Set ℕ, ∀ B : Set ℕ, charOracle C ≤ᵀ charOracle B →
      Disjoint (randomPoints P B μ) N := by
  have hU : ∀ m : ℕ, ∃ U : Set X, U ⊇ N ∧ IsOpen U ∧ μ U < (2 : ℝ≥0∞)⁻¹ ^ m := fun m ↦
    Set.exists_isOpen_lt_of_lt N _ (by
      rw [hN]
      exact ENNReal.pow_pos (ENNReal.inv_pos.mpr ENNReal.ofNat_ne_top) m)
  choose U hNU hUo hUμ using hU
  obtain ⟨C, hC⟩ := exists_oracle_isREIn fun mb : ℕ × (ℕ × ℚ) ↦ basicBall P mb.2 ⊆ U mb.1
  refine ⟨C, fun B hB ↦ Set.disjoint_left.mpr fun x hx hxN ↦ ?_⟩
  have htest : IsMeasureTestIn P B μ U :=
    ⟨⟨_, hC B hB, fun m ↦ isOpen_eq_biUnion_basicBall (hUo m)⟩, fun m ↦ (hUμ m).le⟩
  obtain ⟨m, hm⟩ := hx U htest
  exact hm (hNU m hxN)

end Kolmogorov.PointToSet
