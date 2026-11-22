/-
Copyright (c) 2026 Emma Dinowitz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emma Dinowitz
-/
import KolmogorovMathlib.PointToSet.Measure.Ergodic.TypicalPoints

/-!
# Random points of a presented shift

For a one-sided shift with a first-difference metric `d(x, y) = β^{firstDiff x y}`, a presentation
`P` computable relative to `B` whose ideal points have `B`-computable symbols:

* `isCeOpenFamilyIn_listCylinder`: the cylinders `[w]` are uniformly `B`-c.e. open. Note that `β`
  need not be computable: `[w]` is the union of the basic balls `B(x_n, q)` with `x_n ∈ [w]` and
  `q < d(x_a, x_b)` for two ideal points `x_a, x_b ∈ [w]` (an r.e. condition, since membership of
  ideal points in cylinders is decided from their symbols and the ideal distances are
  `B`-computable). Such a distance is at most `β^{|w|}`, and `d(y, x_n) < β^{|w|}` forces
  `y ∈ [w]`; conversely, when `|α| ≥ 2`, density gives `x_a, x_b ∈ [w]` close to `y` that differ
  at `|w|`, so `d(x_a, x_b) ≥ β^{|w|} > d(y, x_a)`. When `|α| ≤ 1` every cylinder is the whole
  space.
* `mem_wordRandomPoints_of_mem_randomPoints`: presentation randomness implies randomness for
  cylinder tests (every cylinder test is a presentation test).
* `isComputableWordMeasureIn_of_isComputableMeasureIn`: an `A`-computable probability measure in
  the sense of the presentation has `A`-computable cylinder measures (lower bounds from (M1), upper
  bounds by complement over the words of the same length).
* `isGenericPoint_of_mem_randomPoints`: for an ergodic `ν` and an oracle `B` admissible for `ν`,
  every `ν`-random point relative to `B` is generic (`typical_eventually_lt_visitFrequency` on the
  cylinders, and the sum-to-one argument of `isGenericPoint_symbolicCode`).

Blueprint node `erg:prop710`.
-/

namespace Kolmogorov.PointToSet

open Filter Set MeasureTheory
open scoped Topology ENNReal Computability

variable {α : Type*} [Fintype α] [Primcodable α] [MetricSpace (ℕ → α)] [MeasurableSpace (ℕ → α)]
  [BorelSpace (ℕ → α)] {β : ℝ}

omit [Fintype α] [Primcodable α] [MeasurableSpace (ℕ → α)] [BorelSpace (ℕ → α)] in
/-- Two sequences that agree below `k` are at distance at most `β^k`. -/
private lemma shiftRand_dist_le_pow (hβ : 0 < β) (hβ₁ : β < 1)
    (hd : ∀ x y : ℕ → α, x ≠ y → dist x y = β ^ PiNat.firstDiff x y) {x y : ℕ → α} {k : ℕ}
    (h : ∀ i < k, x i = y i) : dist x y ≤ β ^ k := by
  by_cases hxy : x = y
  · rw [hxy, dist_self]
    positivity
  rw [hd x y hxy]
  refine pow_le_pow_of_le_one hβ.le hβ₁.le (le_of_not_gt fun hlt ↦ ?_)
  exact PiNat.apply_firstDiff_ne hxy (h _ hlt)

omit [Fintype α] [Primcodable α] [MeasurableSpace (ℕ → α)] [BorelSpace (ℕ → α)] in
/-- Two sequences that differ at `k` are at distance at least `β^k`. -/
private lemma shiftRand_pow_le_dist (hβ : 0 < β) (hβ₁ : β < 1)
    (hd : ∀ x y : ℕ → α, x ≠ y → dist x y = β ^ PiNat.firstDiff x y) {x y : ℕ → α} {k : ℕ}
    (h : x k ≠ y k) : β ^ k ≤ dist x y := by
  have hxy : x ≠ y := fun hxy ↦ h (hxy ▸ rfl)
  rw [hd x y hxy]
  exact pow_le_pow_of_le_one hβ.le hβ₁.le
    (le_of_not_gt fun hlt ↦ h (PiNat.apply_eq_of_lt_firstDiff hlt))

omit [Fintype α] [MetricSpace (ℕ → α)] [MeasurableSpace (ℕ → α)] [BorelSpace (ℕ → α)] in
/-- Membership of an ideal point in a cylinder is `B`-r.e. (in fact decidable) when the
symbols of the ideal points are `B`-computable. -/
private lemma shiftRand_isREIn_mem {B : Set ℕ} {ι : ℕ → ℕ → α}
    (hP : ComputableIn {charOracle B} fun q : ℕ × ℕ ↦ ι q.1 q.2) :
    IsREIn B fun d : ℕ × List α ↦ ι d.1 ∈ listCylinder d.2 := by
  classical
  have hF : IsREIn B fun d : ℕ × ℕ × α ↦ ι d.1 d.2.1 = d.2.2 := by
    refine isREIn_of_computableIn_decide B _ ?_
    have h1 : ComputableIn {charOracle B} fun d : ℕ × ℕ × α ↦ ι d.1 d.2.1 :=
      hP.comp (ComputableIn.fst.pair (ComputableIn.fst.comp ComputableIn.snd))
    have h2 : ComputableIn {charOracle B} fun d : ℕ × ℕ × α ↦ d.2.2 :=
      ComputableIn.snd.comp ComputableIn.snd
    exact (Primrec.eq.decide.to_comp.computableIn).comp (h1.pair h2)
  have h := hF.list_forall_get
  convert h using 2 with d
  simp [listCylinder]

omit [Fintype α] [MeasurableSpace (ℕ → α)] [BorelSpace (ℕ → α)] in
/-- The cylinders of a presented shift are uniformly c.e. open. Blueprint node `erg:prop710`. -/
theorem isCeOpenFamilyIn_listCylinder (hβ : 0 < β) (hβ₁ : β < 1)
    (hd : ∀ x y : ℕ → α, x ≠ y → dist x y = β ^ PiNat.firstDiff x y)
    (P : Presentation (ℕ → α)) (B : Set ℕ) (hPc : ComputablePresentationIn P B)
    (hP : ComputableIn {charOracle B} fun q : ℕ × ℕ ↦ P.ι q.1 q.2) :
    IsCeOpenFamilyIn P B (listCylinder : List α → Set (ℕ → α)) := by
  have hM := shiftRand_isREIn_mem hP
  by_cases hα : Subsingleton α
  · -- every cylinder is the whole space, the union of all basic balls
    refine ⟨fun _ ↦ True, isREIn_of_computable_decide (Computable.const true), fun w ↦ ?_⟩
    ext y
    have hy : y = P.ι 0 := funext fun i ↦ Subsingleton.elim _ _
    simp only [mem_iUnion, mem_ofPred_eq, exists_prop, true_and]
    refine ⟨fun _ ↦ ⟨(0, 1), ?_⟩, fun _ i hi ↦ Subsingleton.elim _ _⟩
    simp [basicBall, hy]
  rw [not_subsingleton_iff_nontrivial] at hα
  -- a basic ball `B(ι n, q)` is listed for `[w]` when `ι n ∈ [w]` and `q < d(ι a, ι b)` for two
  -- ideal points `ι a, ι b ∈ [w]`; such a distance is at most `β^{|w|}`
  let E : List α × (ℕ × ℚ) → Prop := fun z ↦ P.ι z.2.1 ∈ listCylinder z.1 ∧
    ∃ ab : ℕ × ℕ, (P.ι ab.1 ∈ listCylinder z.1 ∧ P.ι ab.2 ∈ listCylinder z.1) ∧
      ((z.2.2 : ℚ) : ℝ) < dist (P.ι ab.1) (P.ι ab.2)
  have hE : IsREIn B E := by
    have h1 : IsREIn B fun z : List α × (ℕ × ℚ) ↦ P.ι z.2.1 ∈ listCylinder z.1 :=
      hM.comp ((Computable.fst.comp Computable.snd).pair Computable.fst).computableIn
    have hdist := birkhoff_computableIn_gt B _ hPc
    have h2 : IsREIn B fun y : (List α × (ℕ × ℚ)) × (ℕ × ℕ) ↦
        (P.ι y.2.1 ∈ listCylinder y.1.1 ∧ P.ι y.2.2 ∈ listCylinder y.1.1) ∧
          ((y.1.2.2 : ℚ) : ℝ) < dist (P.ι y.2.1) (P.ι y.2.2) := by
      refine (IsREIn.and ?_ ?_).and ?_
      · exact hM.comp ((Computable.fst.comp Computable.snd).pair
          (Computable.fst.comp Computable.fst)).computableIn
      · exact hM.comp ((Computable.snd.comp Computable.snd).pair
          (Computable.fst.comp Computable.fst)).computableIn
      · exact hdist.comp (Computable.snd.pair
          (Computable.snd.comp (Computable.snd.comp Computable.fst))).computableIn
    exact h1.and h2.exists
  refine ⟨E, hE, fun w ↦ ?_⟩
  ext y
  simp only [mem_iUnion, mem_ofPred_eq, exists_prop]
  constructor
  · intro hy
    -- `y` and a point `y'` that agree below `k` and differ at `k`
    obtain ⟨c, hc⟩ := exists_ne (y w.length)
    let y' : ℕ → α := Function.update y w.length c
    have hy'k : y' w.length = c := Function.update_self _ _ _
    have hpos : 0 < β ^ w.length := pow_pos hβ _
    obtain ⟨a, ha⟩ := P.dense.exists_dist_lt y hpos
    obtain ⟨b, hb⟩ := P.dense.exists_dist_lt y' hpos
    rw [dist_lt_pow_iff_of_firstDiff hβ hβ₁ hd] at ha hb
    have hya : ∀ i (hi : i < w.length), P.ι a i = w[i] := fun i hi ↦
      (ha i hi.le).symm.trans (hy i hi)
    have hyb : ∀ i (hi : i < w.length), P.ι b i = w[i] := fun i hi ↦ by
      rw [← hb i hi.le]
      exact (Function.update_of_ne hi.ne _ _).trans (hy i hi)
    have hab : P.ι a w.length ≠ P.ι b w.length := by
      rw [← ha _ le_rfl, ← hb _ le_rfl, hy'k]
      exact hc.symm
    have h1 : dist y (P.ι a) < dist (P.ι a) (P.ι b) := by
      refine lt_of_lt_of_le ?_ (shiftRand_pow_le_dist hβ hβ₁ hd hab)
      exact (dist_lt_pow_iff_of_firstDiff hβ hβ₁ hd).2 fun i hi ↦ ha i hi
    obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn h1
    exact ⟨(a, q), ⟨fun i hi ↦ hya i hi, (a, b), ⟨fun i hi ↦ hya i hi, fun i hi ↦ hyb i hi⟩, hq2⟩,
      hq1⟩
  · rintro ⟨⟨n, q⟩, ⟨hn, ⟨a, b⟩, ⟨ha, hb⟩, hq⟩, hy⟩ i hi
    change dist y (P.ι n) < q at hy
    have hab : dist (P.ι a) (P.ι b) ≤ β ^ w.length :=
      shiftRand_dist_le_pow hβ hβ₁ hd fun j hj ↦ (ha j hj).trans (hb j hj).symm
    have hyn := (dist_lt_pow_iff_of_firstDiff hβ hβ₁ hd).1 (hy.trans (hq.trans_le hab)) i hi.le
    exact hyn.trans (hn i hi)

omit [Fintype α] [BorelSpace (ℕ → α)] in
/-- Presentation randomness implies randomness for cylinder tests. Blueprint node `erg:prop710`. -/
theorem mem_wordRandomPoints_of_mem_randomPoints (hβ : 0 < β) (hβ₁ : β < 1)
    (hd : ∀ x y : ℕ → α, x ≠ y → dist x y = β ^ PiNat.firstDiff x y)
    (P : Presentation (ℕ → α)) (B : Set ℕ) (hPc : ComputablePresentationIn P B)
    (hP : ComputableIn {charOracle B} fun q : ℕ × ℕ ↦ P.ι q.1 q.2) (ν : Measure (ℕ → α))
    {x : ℕ → α} (hx : x ∈ randomPoints P B ν) : x ∈ wordRandomPoints B ν := by
  rintro V ⟨E, hE, hVE, hνV⟩
  have hU := (isCeOpenFamilyIn_listCylinder hβ hβ₁ hd P B hPc hP).iUnion_of_isREIn hE
  have hV : V = fun m ↦ ⋃ w ∈ {w | E (m, w)}, listCylinder w := funext hVE
  exact hx V ⟨hV ▸ hU, hνV⟩

/-- A real family with relatively enumerable strict lower and upper rational cuts is a
relatively computable real family: search for a rational interval of length `< 2^{-n}` around
the value. -/
private lemma shiftRand_isComputableRealFamilyIn_of_cuts {ι : Type*} [Primcodable ι]
    {A : Set ℕ} {v : ι → ℝ} (hlo : IsREIn A fun w : ι × ℚ ↦ (w.2 : ℝ) < v w.1)
    (hup : IsREIn A fun w : ι × ℚ ↦ v w.1 < (w.2 : ℝ)) : IsComputableRealFamilyIn A v := by
  let G : (ι × ℕ) × (ℚ × ℚ) → Prop := fun z ↦
    ((z.2.1 : ℝ) < v z.1.1 ∧ v z.1.1 < (z.2.2 : ℝ)) ∧ z.2.2 - z.2.1 < (2 ^ z.1.2 : ℚ)⁻¹
  have hG : IsREIn A G := by
    have h1 : IsREIn A fun z : (ι × ℕ) × (ℚ × ℚ) ↦ ((z.2.1 : ℚ) : ℝ) < v z.1.1 :=
      hlo.comp ((Computable.fst.comp Computable.fst).pair
        (Computable.fst.comp Computable.snd)).computableIn
    have h2 : IsREIn A fun z : (ι × ℕ) × (ℚ × ℚ) ↦ v z.1.1 < ((z.2.2 : ℚ) : ℝ) :=
      hup.comp ((Computable.fst.comp Computable.fst).pair
        (Computable.snd.comp Computable.snd)).computableIn
    have h3 : IsREIn A fun z : (ι × ℕ) × (ℚ × ℚ) ↦ z.2.2 - z.2.1 < (2 ^ z.1.2 : ℚ)⁻¹ :=
      isREIn_of_computable_decide (computable₂_ratLt.comp
        (computable₂_ratSub.comp (Computable.snd.comp Computable.snd)
          (Computable.fst.comp Computable.snd))
        (computable_rat_inv_two_pow.comp (Computable.snd.comp Computable.fst)))
    exact (h1.and h2).and h3
  have htot : ∀ a : ι × ℕ, ∃ b : ℚ × ℚ, G (a, b) := by
    rintro ⟨i, n⟩
    have hε : (0 : ℝ) < (((2 ^ n : ℚ)⁻¹ : ℚ) : ℝ) := by positivity
    obtain ⟨a, ha1, ha2⟩ :=
      exists_rat_btwn (show v i - (((2 ^ n : ℚ)⁻¹ : ℚ) : ℝ) / 2 < v i by linarith)
    obtain ⟨b, hb1, hb2⟩ :=
      exists_rat_btwn (show v i < v i + (((2 ^ n : ℚ)⁻¹ : ℚ) : ℝ) / 2 by linarith)
    refine ⟨(a, b), ⟨ha2, hb1⟩, ?_⟩
    have h : ((b - a : ℚ) : ℝ) < (((2 ^ n : ℚ)⁻¹ : ℚ) : ℝ) := by
      push_cast at ha1 hb2 ⊢
      linarith
    exact_mod_cast h
  obtain ⟨g, hg, hgG⟩ := hG.exists_computableIn_choice htot
  refine ⟨fun z ↦ (g z).1, (Computable.fst (α := ℚ) (β := ℚ)).computableIn.comp hg, fun i n ↦ ?_⟩
  obtain ⟨⟨h1, h2⟩, h3⟩ := hgG (i, n)
  have h3' : (((g (i, n)).2 : ℚ) : ℝ) - (((g (i, n)).1 : ℚ) : ℝ) < (2 : ℝ)⁻¹ ^ n := by
    have h4 : ((((g (i, n)).2 - (g (i, n)).1 : ℚ)) : ℝ) < (((2 ^ n : ℚ)⁻¹ : ℚ) : ℝ) :=
      Rat.cast_lt.mpr h3
    push_cast at h4
    rwa [inv_pow]
  rw [abs_sub_lt_iff]
  constructor <;> linarith

omit [Fintype α] in
/-- A presentation-computable probability measure has computable cylinder measures.
Blueprint node `erg:prop710`. -/
theorem isComputableWordMeasureIn_of_isComputableMeasureIn (hβ : 0 < β) (hβ₁ : β < 1)
    (hd : ∀ x y : ℕ → α, x ≠ y → dist x y = β ^ PiNat.firstDiff x y)
    (P : Presentation (ℕ → α)) (B : Set ℕ) (hPc : ComputablePresentationIn P B)
    (hP : ComputableIn {charOracle B} fun q : ℕ × ℕ ↦ P.ι q.1 q.2) (ν : Measure (ℕ → α))
    [IsProbabilityMeasure ν] (hν : IsComputableMeasureIn P B ν) :
    IsComputableWordMeasureIn B ν := by
  classical
  have hcyl := isCeOpenFamilyIn_listCylinder hβ hβ₁ hd P B hPc hP
  have hlo := hν.lowerSemicomputable_ceOpen hcyl
  have hC : IsREIn B fun d : List α × List α ↦ d.2.length = d.1.length ∧ d.2 ≠ d.1 :=
    isREIn_of_computable_decide (PrimrecPred.and
      (Primrec.eq.comp (Primrec.list_length.comp Primrec.snd)
        (Primrec.list_length.comp Primrec.fst))
      (PrimrecPred.not (Primrec.eq.comp Primrec.snd Primrec.fst))).decide.to_comp
  have hup := hν.isREIn_measure_compl_lt (hcyl.iUnion_of_isREIn hC)
  simp only [iUnion_listCylinder_ne_eq_compl, compl_compl] at hup
  exact shiftRand_isComputableRealFamilyIn_of_cuts hlo hup

omit [Fintype α] in
/-- Random points of an ergodic measure, relative to an admissible oracle that computes the
symbols of the ideal points, are generic. Blueprint node `erg:prop710`. -/
theorem isGenericPoint_of_mem_randomPoints [Finite α] (hβ : 0 < β) (hβ₁ : β < 1)
    (hd : ∀ x y : ℕ → α, x ≠ y → dist x y = β ^ PiNat.firstDiff x y)
    (P : Presentation (ℕ → α)) (ν : Measure (ℕ → α)) [IsProbabilityMeasure ν]
    (hν : Ergodic shiftMap ν) {B : Set ℕ} (hB : IsMeasureAdmissible P shiftMap ν B)
    (hP : ComputableIn {charOracle B} fun q : ℕ × ℕ ↦ P.ι q.1 q.2) {x : ℕ → α}
    (hx : x ∈ randomPoints P B ν) : IsGenericPoint ν x := by
  classical
  have : Fintype α := Fintype.ofFinite α
  intro k w
  have hcyl := isCeOpenFamilyIn_listCylinder hβ hβ₁ hd P B hB.1 hP
  set O : (Fin k → α) → Set (ℕ → α) := wordCylinder with hO_def
  -- the cylinders are effectively open
  have hOce : ∀ w', IsCeOpenIn P B (O w') := fun w' ↦ by
    rw [hO_def, ← listCylinder_ofFn]
    exact isCeOpenIn_of_isCeOpenFamilyIn_typical hcyl _
  have hO_meas : ∀ w', MeasurableSet (O w') := by
    intro w'
    obtain ⟨E, -, hE⟩ := hOce w'
    rw [hE]
    exact (isOpen_biUnion fun b _ ↦ Metric.isOpen_ball).measurableSet
  -- the cylinders of length `k` partition the space
  have hdisj : Pairwise (Function.onFun Disjoint O) := by
    intro w₁ w₂ hne
    rw [Function.onFun, Set.disjoint_left]
    intro y hy₁ hy₂
    exact hne (funext fun i ↦ (hy₁ i).symm.trans (hy₂ i))
  have hsum1 : ∑ w', (ν (O w')).toReal = 1 := by
    have hcover : (⋃ w', O w') = univ :=
      eq_univ_of_forall fun y ↦ mem_iUnion.mpr ⟨fun i ↦ y i, fun _ ↦ rfl⟩
    have h1 : ν (⋃ w', O w') = 1 := by rw [hcover, measure_univ]
    rw [measure_iUnion hdisj hO_meas, tsum_fintype] at h1
    rw [← ENNReal.toReal_sum fun w' _ ↦ measure_ne_top ν (O w'), h1, ENNReal.toReal_one]
  -- word counts are visit counts
  set c : ℕ → Fin k → α := fun j i ↦ x (j + i) with hc_def
  set f : (Fin k → α) → ℕ → ℝ := fun w' n ↦
    (({j | j < n ∧ ∀ i : Fin k, x (j + i) = w' i} : Set ℕ).ncard : ℝ) / n with hf_def
  have hfin : ∀ w' n, ({j | j < n ∧ ∀ i : Fin k, x (j + i) = w' i} :
      Set ℕ) = ↑((Finset.range n).filter fun j ↦ c j = w') := by
    intro w' n
    ext j
    simp only [mem_ofPred_eq, Finset.coe_filter, Finset.mem_range, hc_def, funext_iff]
  have hvisit : ∀ w' n, ({j | j < n ∧ ∀ i : Fin k, x (j + i) = w' i} : Set ℕ) =
      {j | j < n ∧ shiftMap^[j] x ∈ O w'} := by
    intro w' n
    ext j
    simp only [mem_ofPred_eq, hO_def, wordCylinder, iterate_shiftMap, add_comm]
  have hsumf : ∀ n, 1 ≤ n → ∑ w', f w' n = 1 := by
    intro n hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    simp only [hf_def, hfin, Set.ncard_coe_finset]
    rw [← Finset.sum_div, div_eq_one_iff_eq hn0.ne']
    have := Finset.card_eq_sum_card_fiberwise (f := c) (s := Finset.range n)
      (t := Finset.univ) (fun _ _ ↦ Finset.mem_coe.mpr (Finset.mem_univ _))
    rw [Finset.card_range] at this
    exact_mod_cast this.symm
  have hlow : ∀ w', ∀ ε > 0, ∀ᶠ n : ℕ in atTop, (ν (O w')).toReal - ε < f w' n := by
    intro w' ε hε
    filter_upwards [typical_eventually_lt_visitFrequency P shiftMap B ν hB hν (hOce w') hx hε]
      with n hn
    change _ < ((({j | j < n ∧ ∀ i : Fin k, x (j + i) = w' i} : Set ℕ).ncard : ℝ) / n)
    rwa [hvisit, ncard_eq_typicalVisitCount]
  rw [tendsto_order]
  constructor
  · intro a' ha'
    filter_upwards [hlow w _ (sub_pos.mpr ha')] with n hn
    simpa [hf_def] using hn
  · intro b' hb'
    have hK : (0 : ℝ) < Fintype.card (Fin k → α) := by
      have : Nonempty α := ⟨P.ι 0 0⟩
      exact_mod_cast Fintype.card_pos
    set ε := (b' - (ν (O w)).toReal) / Fintype.card (Fin k → α) with hε_def
    have hε : 0 < ε := div_pos (sub_pos.mpr hb') hK
    have hall : ∀ᶠ n : ℕ in atTop, ∀ w', (ν (O w')).toReal - ε < f w' n :=
      eventually_all.mpr fun w' ↦ hlow w' ε hε
    filter_upwards [hall, eventually_ge_atTop 1] with n hn hn1
    have hsum : ∑ w', (f w' n - ((ν (O w')).toReal - ε)) =
        Fintype.card (Fin k → α) * ε := by
      rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, hsumf n hn1, hsum1]
      simp
    have hsingle := Finset.single_le_sum (s := Finset.univ)
      (f := fun w' ↦ f w' n - ((ν (O w')).toReal - ε)) (fun w' _ ↦ (sub_pos.mpr (hn w')).le)
      (Finset.mem_univ w)
    rw [hsum] at hsingle
    have hKε : (Fintype.card (Fin k → α) : ℝ) * ε = b' - (ν (O w)).toReal := by
      rw [hε_def]
      field_simp
    change f w n < b'
    nlinarith

end Kolmogorov.PointToSet
