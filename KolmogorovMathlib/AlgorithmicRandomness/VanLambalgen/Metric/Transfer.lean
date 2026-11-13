/-
Copyright (c) 2026 Emma Dinowitz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emma Dinowitz
-/
import KolmogorovMathlib.AlgorithmicRandomness.VanLambalgen.Metric.Defs
import KolmogorovMathlib.AlgorithmicRandomness.Relative.Basic
import KolmogorovMathlib.AlgorithmicRandomness.Relative.Pullback
import KolmogorovMathlib.Oracle.Search
import KolmogorovMathlib.PointToSet.Measure.EffectiveNull

/-!
# Transfer of randomness along the itinerary map

For an almost decidable basis `B` relative to `A` for `μ`, the itinerary map `φ = itinerary B`
sends a point to the sequence of bits `x ∈ B k`. This module proves that `φ` is measurable, that
it preserves randomness in both directions, relative to every oracle above `A`
(`IsAlmostDecidableBasisIn.mem_randomPoints_iff`), and that the image measure is computable on
Cantor space relative to `A` when `μ` is
(`IsAlmostDecidableBasisIn.isComputableCantorMeasureIn_map`).

## Conventions

Randomness on the presented space is `randomPoints P A μ`; on Cantor space it is
`IsMartinLofRandomIn A`. Measures are in `ℝ≥0∞`. A test on Cantor space pulls back along `φ` to a
union of finite intersections of the members `B k` and the exteriors `D k`, which differs from the
exact preimage by the boundary sets `(B k ∪ D k)ᶜ`; a random point avoids these. Those finite
intersections are c.e. open only when `A` computes the metric table
(`ComputablePresentationIn P A`), which the transfer therefore assumes.

## Main declarations

* `IsAlmostDecidableBasisIn.measurable_itinerary` (blueprint node `vlm:itinerary`).
* `IsAlmostDecidableBasisIn.mem_randomPoints_iff` (blueprint node `vlm:transfer`).
* `IsAlmostDecidableBasisIn.isComputableCantorMeasureIn_map` (blueprint node
  `vlm:itinerary-measure`).

Used by `AlgorithmicRandomness/VanLambalgen/Metric/MainResults.lean`.
-/

namespace Kolmogorov.PointToSet

open MeasureTheory
open scoped Computability ENNReal

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] {P : Presentation X} {A : Set ℕ}
  {μ : Measure X} {B : ℕ → Set X}

/-! ### Auxiliary facts -/

omit [MeasurableSpace X] in
/-- The members of a c.e. open family are open. -/
private lemma isOpen_of_isCeOpenFamilyIn {ι : Type*} [Primcodable ι] {U : ι → Set X}
    (hU : IsCeOpenFamilyIn P A U) (i : ι) : IsOpen (U i) := by
  obtain ⟨E, -, hE⟩ := hU
  rw [hE i]
  exact isOpen_biUnion fun b _ ↦ Metric.isOpen_ball

/-- The test bound `2^{-n}` of Cantor space, as a power of `2⁻¹`. -/
private lemma dyadicValue_one (n : ℕ) : dyadicValue 1 n = (2 : ℝ≥0∞)⁻¹ ^ n := by
  rw [dyadicValue, Nat.cast_one, one_div, ENNReal.inv_pow]

/-- The union of the cylinders of an `A`-enumerable predicate on levels and strings is uniformly
effectively open relative to `A`. -/
private lemma isUniformlyEffectiveOpenIn_of_isREIn {R : ℕ × BitString → Prop}
    (hR : IsREIn A R) :
    IsUniformlyEffectiveOpenIn A fun n ↦ ⋃ σ ∈ {σ | R (n, σ)}, cantorCylinder σ := by
  obtain ⟨e, he, henum⟩ := (relative_enumeration A R).mp hR
  refine ⟨fun n i ↦ (e i).bind fun w ↦ if w.1 = n then some w.2 else none, ?_, fun n ↦ ?_⟩
  · have hpost : Computable fun p : ℕ × Option (ℕ × BitString) ↦
        p.2.bind fun w ↦ if w.1 = p.1 then some w.2 else none := by
      refine Computable.option_bind Computable.snd ?_
      have hc : Primrec fun pw : (ℕ × Option (ℕ × BitString)) × (ℕ × BitString) ↦
          if pw.2.1 = pw.1.1 then some pw.2.2 else none :=
        Primrec.ite (Primrec.eq.comp (Primrec.fst.comp Primrec.snd)
            (Primrec.fst.comp Primrec.fst))
          (Primrec.option_some.comp (Primrec.snd.comp Primrec.snd)) (Primrec.const none)
      exact hc.to_comp
    exact ComputableIn₂.mk
      (hpost.computableIn.comp (ComputableIn.fst.pair (he.comp ComputableIn.snd)))
  · ext z
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq, exists_prop]
    constructor
    · rintro ⟨σ, hσ, hz⟩
      obtain ⟨t, ht⟩ := (henum (n, σ)).mp hσ
      exact ⟨t, by simpa [ht] using hz⟩
    · rintro ⟨t, hz⟩
      cases ht : e t with
      | none => simp [ht] at hz
      | some w =>
        simp only [ht, Option.bind_some] at hz
        split_ifs at hz with hw
        · subst hw
          exact ⟨w.2, (henum w).mpr ⟨t, ht⟩, by simpa using hz⟩
        · simp at hz

/-- A sequence in the cylinder of `σ` has bit `true` wherever `σ` has (reading `σ` with default
`false`). -/
private lemma eq_true_of_getD {σ : BitString} {z : CantorSeq} (hz : z ∈ cantorCylinder σ)
    {k : ℕ} (hk : σ.getD k false = true) : z k = true := by
  have hlt : k < σ.length := by
    by_contra h
    push Not at h
    rw [List.getD_eq_default _ _ h] at hk
    exact Bool.false_ne_true hk
  rw [hz k hlt, ← List.getD_eq_getElem _ false hlt]
  exact hk

/-! ### Measurability -/

/-- The itinerary map of an almost decidable basis is measurable: each bit is the indicator of an
open set. Blueprint node `vlm:itinerary`. -/
theorem IsAlmostDecidableBasisIn.measurable_itinerary [OpensMeasurableSpace X]
    (hB : IsAlmostDecidableBasisIn P A μ B) : Measurable (itinerary B) := by
  refine Measurable.of_eval fun k ↦ measurable_to_bool ?_
  have h : (fun x ↦ itinerary B x k) ⁻¹' {true} = B k := by
    ext x
    simp [itinerary]
  rw [h]
  exact (isOpen_of_isCeOpenFamilyIn hB.isCeOpenFamilyIn k).measurableSet

/-! ### Transfer of randomness -/

/-- Pulling back tests: a test on the presented space is the preimage of a test on Cantor space
(each basic ball is a union of finite intersections of members), so a point whose itinerary is
random is random. -/
private lemma mem_randomPoints_of_isMartinLofRandomIn [OpensMeasurableSpace X]
    (hB : IsAlmostDecidableBasisIn P A μ B) {A' : Set ℕ}
    (hAA' : charOracle A ≤ᵀ charOracle A') {x : X}
    (hx : IsMartinLofRandomIn A' (μ.map (itinerary B)) (itinerary B x)) :
    x ∈ randomPoints P A' μ := by
  intro U hU
  by_contra hxU
  push Not at hxU
  obtain ⟨EU, hEU, hUE⟩ := hU.1
  obtain ⟨EG, hEG, hgen⟩ := hB.generates
  have hEG' := hEG.mono_oracle hAA'
  -- the strings forcing `true` on a list `L` of members whose intersection lies in a listed ball
  let R : ℕ × BitString → Prop := fun w ↦ ∃ bL : (ℕ × ℚ) × List ℕ,
    (EU (w.1, bL.1) ∧ EG bL) ∧
      ∀ k (h : k < bL.2.length), w.2.getD (bL.2.get ⟨k, h⟩) false = true
  have hR : IsREIn A' R := by
    have h1 : IsREIn A' fun v : (ℕ × BitString) × ((ℕ × ℚ) × List ℕ) ↦ EU (v.1.1, v.2.1) :=
      hEU.comp ((Computable.fst.comp Computable.fst).pair
        (Computable.fst.comp Computable.snd)).computableIn
    have h2 : IsREIn A' fun v : (ℕ × BitString) × ((ℕ × ℚ) × List ℕ) ↦ EG v.2 :=
      hEG'.comp Computable.snd.computableIn
    have hF : IsREIn A' fun v : BitString × ℕ × ℕ ↦ v.1.getD v.2.2 false = true :=
      isREIn_of_computable_decide (Primrec.eq.comp ((Primrec.list_getD false).comp Primrec.fst
        (Primrec.snd.comp Primrec.snd)) (Primrec.const true)).decide.to_comp
    have h3 : IsREIn A' fun v : (ℕ × BitString) × ((ℕ × ℚ) × List ℕ) ↦
        ∀ k (h : k < v.2.2.length), v.1.2.getD (v.2.2.get ⟨k, h⟩) false = true :=
      (IsREIn.list_forall_get hF).comp ((Computable.snd.comp Computable.fst).pair
        (Computable.snd.comp Computable.snd)).computableIn
    exact ((h1.and h2).and h3).exists
  have hVo := isUniformlyEffectiveOpenIn_of_isREIn hR
  have hmeas := hB.measurable_itinerary
  have hpre : ∀ n, itinerary B ⁻¹' (⋃ σ ∈ {σ | R (n, σ)}, cantorCylinder σ) = U n := by
    intro n
    ext y
    rw [hUE n]
    simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_ofPred_eq, exists_prop]
    constructor
    · rintro ⟨σ, ⟨⟨b, L⟩, ⟨hb, hbL⟩, hL⟩, hyσ⟩
      refine ⟨b, hb, ?_⟩
      rw [hgen b]
      simp only [Set.mem_iUnion, Set.mem_ofPred_eq, exists_prop, Set.mem_iInter]
      refine ⟨L, hbL, fun k hk ↦ ?_⟩
      obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hk
      have h := eq_true_of_getD hyσ (hL i hi)
      simpa [itinerary] using h
    · rintro ⟨b, hb, hyb⟩
      rw [hgen b] at hyb
      simp only [Set.mem_iUnion, Set.mem_ofPred_eq, exists_prop, Set.mem_iInter] at hyb
      obtain ⟨L, hbL, hyL⟩ := hyb
      refine ⟨cantorPrefix (itinerary B y) (L.sum + 1), ⟨(b, L), ⟨hb, hbL⟩, fun i hi ↦ ?_⟩,
        (isCantorPrefix_iff_cantorPrefix_eq _ _).mpr (by rw [cantorPrefix_length])⟩
      have hmem : L.get ⟨i, hi⟩ ∈ L := List.get_mem L ⟨i, hi⟩
      have hle : L.get ⟨i, hi⟩ < (cantorPrefix (itinerary B y) (L.sum + 1)).length := by
        rw [cantorPrefix_length]
        exact Nat.lt_succ_of_le (List.le_sum_of_mem hmem)
      rw [List.getD_eq_getElem _ _ hle, cantorPrefix_getElem]
      simpa [itinerary] using hyL _ hmem
  refine hx _ ⟨hVo, fun n ↦ ?_⟩ ?_
  · rw [Measure.map_apply hmeas (IsUniformlyEffectiveOpenIn.measurableSet hVo n), hpre n,
      dyadicValue_one]
    exact hU.2 n
  · refine Set.mem_iInter.mpr fun n ↦ ?_
    rw [← Set.mem_preimage, hpre n]
    exact hxU n

omit [MeasurableSpace X] in
/-- Choosing, at a position `k`, the set `F k` or `G k` according to bit `k` of a string gives a
c.e. open family in the string and the position. -/
private lemma isCeOpenFamilyIn_ite {F G : ℕ → Set X} (hFo : IsCeOpenFamilyIn P A F)
    (hGo : IsCeOpenFamilyIn P A G) :
    IsCeOpenFamilyIn P A fun p : BitString × ℕ ↦
      if p.1.getD p.2 false = true then F p.2 else G p.2 := by
  obtain ⟨EG, hEG, hGE⟩ := hGo
  obtain ⟨EF, hEF, hFE⟩ := hFo
  refine ⟨fun w ↦ (w.1.1.getD w.1.2 false = true ∧ EF (w.1.2, w.2)) ∨
    (w.1.1.getD w.1.2 false = false ∧ EG (w.1.2, w.2)), ?_, fun p ↦ ?_⟩
  · have hc : Primrec fun w : (BitString × ℕ) × (ℕ × ℚ) ↦ w.1.1.getD w.1.2 false :=
      (Primrec.list_getD false).comp (Primrec.fst.comp Primrec.fst)
        (Primrec.snd.comp Primrec.fst)
    have ht : IsREIn A fun w : (BitString × ℕ) × (ℕ × ℚ) ↦ w.1.1.getD w.1.2 false = true :=
      isREIn_of_computable_decide (Primrec.eq.comp hc (Primrec.const true)).decide.to_comp
    have hf : IsREIn A fun w : (BitString × ℕ) × (ℕ × ℚ) ↦ w.1.1.getD w.1.2 false = false :=
      isREIn_of_computable_decide (Primrec.eq.comp hc (Primrec.const false)).decide.to_comp
    have hd : IsREIn A fun w : (BitString × ℕ) × (ℕ × ℚ) ↦ EF (w.1.2, w.2) :=
      hEF.comp ((Computable.snd.comp Computable.fst).pair Computable.snd).computableIn
    have hb : IsREIn A fun w : (BitString × ℕ) × (ℕ × ℚ) ↦ EG (w.1.2, w.2) :=
      hEG.comp ((Computable.snd.comp Computable.fst).pair Computable.snd).computableIn
    exact (ht.and hd).or (hf.and hb)
  · dsimp only
    by_cases h : p.1.getD p.2 false = true
    · simp only [h, ↓reduceIte]
      rw [hFE p.2]
      ext y
      simp
    · simp only [h]
      rw [hGE p.2]
      ext y
      simp

omit [MeasurableSpace X] in
/-- The sets `⋃_{k < |σ|} (D k if σ_k else B k)` are c.e. open uniformly in `σ`: they are unions
over a list, and need no intersections. -/
private lemma isCeOpenFamilyIn_cylCompl {D : ℕ → Set X} (hBo : IsCeOpenFamilyIn P A B)
    (hDo : IsCeOpenFamilyIn P A D) :
    IsCeOpenFamilyIn P A fun σ : BitString ↦
      ⋃ k ∈ List.range σ.length, if σ.getD k false = true then D k else B k :=
  (isCeOpenFamilyIn_ite hDo hBo).biUnion_list.comp
    (g := fun σ : BitString ↦ (σ, List.range σ.length))
    (Computable.id.pair (Primrec.list_range.comp Primrec.list_length).to_comp)

/-- Pushing tests forward, above an oracle computing the metric table of `P`: the preimage of a
cylinder `[σ]` contains the c.e. open set `⋂_{k < |σ|} (B k if σ_k else D k)` with the same
measure, and a random point lies in it whenever its itinerary lies in `[σ]` (it avoids the
boundary sets). The hypothesis `hP` is needed for the finite intersections to be c.e. open; the
statement `mem_randomPoints_iff` lacks it (see the comment there). -/
private lemma isMartinLofRandomIn_of_mem_randomPoints [OpensMeasurableSpace X]
    (hB : IsAlmostDecidableBasisIn P A μ B) (hP : ComputablePresentationIn P A) {A' : Set ℕ}
    (hAA' : charOracle A ≤ᵀ charOracle A') {x : X} (hx : x ∈ randomPoints P A' μ) :
    IsMartinLofRandomIn A' (μ.map (itinerary B)) (itinerary B x) := by
  classical
  obtain ⟨D, W, hDo, hWo, hDW⟩ := hB.exists_exterior
  have hφ := hB.measurable_itinerary
  -- a random point avoids the boundary sets
  have hbd : ∀ k, x ∈ B k ∪ D k := by
    intro k
    have htest : IsMeasureTestIn P A' μ fun n ↦ W (k, n) :=
      ⟨isCeOpenFamilyIn_mono P A hAA' (hWo.comp (g := fun n : ℕ ↦ (k, n))
        ((Computable.const k).pair Computable.id)), fun n ↦ ((hDW k).2 n).2⟩
    obtain ⟨n, hn⟩ := hx _ htest
    by_contra h
    exact hn (((hDW k).2 n).1 h)
  -- the c.e. open inner approximations `O σ` of the preimages of the cylinders
  set O : BitString → Set X := fun σ ↦
    ⋂ k ∈ List.range σ.length, if σ.getD k false = true then B k else D k with hOdef
  have hOo : IsCeOpenFamilyIn P A' O :=
    isCeOpenFamilyIn_mono P A hAA' ((IsCeOpenFamilyIn.biInter_list hP
      (isCeOpenFamilyIn_ite hB.isCeOpenFamilyIn hDo)).comp
      (g := fun σ : BitString ↦ (σ, List.range σ.length))
      (Computable.id.pair (Primrec.list_range.comp Primrec.list_length).to_comp))
  have hOsub : ∀ σ, O σ ⊆ itinerary B ⁻¹' cantorCylinder σ := by
    intro σ y hy
    simp only [hOdef, Set.mem_iInter, List.mem_range] at hy
    change IsCantorPrefix σ (itinerary B y)
    intro i hi
    have hyi := hy i hi
    rw [← List.getD_eq_getElem σ false hi]
    by_cases hσi : σ.getD i false = true
    · simp only [hσi, ↓reduceIte] at hyi
      rw [hσi]
      simpa [itinerary] using hyi
    · simp only [hσi] at hyi
      rw [Bool.not_eq_true] at hσi
      rw [hσi]
      have hyB : y ∉ B i := fun h ↦ Set.disjoint_left.mp (hDW i).1 h hyi
      simpa [itinerary] using hyB
  have hOmem : ∀ σ, itinerary B x ∈ cantorCylinder σ → x ∈ O σ := by
    intro σ hσ
    simp only [hOdef, Set.mem_iInter, List.mem_range]
    intro i hi
    have hbit : itinerary B x i = σ.getD i false := by
      rw [List.getD_eq_getElem _ _ hi]
      exact hσ i hi
    by_cases hσi : σ.getD i false = true
    · simp only [hσi, ↓reduceIte]
      rw [hσi] at hbit
      simpa [itinerary] using hbit
    · simp only [hσi]
      rw [Bool.not_eq_true] at hσi
      rw [hσi] at hbit
      have hxB : x ∉ B i := by simpa [itinerary] using hbit
      exact (hbd i).resolve_left hxB
  intro V hV hxV
  obtain ⟨f, hf, hVf⟩ := hV.1
  obtain ⟨EO, hEO, hOE⟩ := hOo
  -- the test `U n = ⋃ {O σ | σ enumerated into V n}` on the presented space
  let EU : ℕ × (ℕ × ℚ) → Prop := fun w ↦
    ∃ iσ : ℕ × BitString, f w.1 iσ.1 = some iσ.2 ∧ EO (iσ.2, w.2)
  have hEU : IsREIn A' EU := by
    have h1 : IsREIn A' fun v : (ℕ × (ℕ × ℚ)) × (ℕ × BitString) ↦ f v.1.1 v.2.1 = some v.2.2 := by
      refine isREIn_of_computableIn_decide A' _ ?_
      have hfv : ComputableIn {charOracle A'} fun v : (ℕ × (ℕ × ℚ)) × (ℕ × BitString) ↦
          f v.1.1 v.2.1 :=
        hf.comp (ComputableIn.fst.comp ComputableIn.fst) (ComputableIn.fst.comp ComputableIn.snd)
      have hs : ComputableIn {charOracle A'} fun v : (ℕ × (ℕ × ℚ)) × (ℕ × BitString) ↦
          (some v.2.2 : Option BitString) :=
        (Primrec.option_some.comp (Primrec.snd.comp Primrec.snd)).to_comp.computableIn
      exact (((Primrec.eq (α := Option BitString)).decide.to_comp.computableIn₂
        (O := {charOracle A'})).comp hfv hs).of_eq fun v ↦ rfl
    have h2 : IsREIn A' fun v : (ℕ × (ℕ × ℚ)) × (ℕ × BitString) ↦ EO (v.2.2, v.1.2) :=
      hEO.comp ((Computable.snd.comp Computable.snd).pair
        (Computable.snd.comp Computable.fst)).computableIn
    exact (h1.and h2).exists
  let U : ℕ → Set X := fun n ↦ ⋃ b ∈ {b | EU (n, b)}, basicBall P b
  have hUO : ∀ n, U n = ⋃ i, (f n i).elim ∅ O := by
    intro n
    ext y
    simp only [U, EU, Set.mem_iUnion, Set.mem_ofPred_eq, exists_prop]
    constructor
    · rintro ⟨b, ⟨⟨i, σ⟩, hfi, hb⟩, hyb⟩
      refine ⟨i, ?_⟩
      rw [hfi, Option.elim_some, hOE σ]
      exact Set.mem_iUnion₂.mpr ⟨b, hb, hyb⟩
    · rintro ⟨i, hy⟩
      cases hfi : f n i with
      | none => simp [hfi] at hy
      | some σ =>
        rw [hfi, Option.elim_some, hOE σ] at hy
        obtain ⟨b, hb, hyb⟩ := Set.mem_iUnion₂.mp hy
        exact ⟨b, ⟨(i, σ), hfi, hb⟩, hyb⟩
  have hμU : ∀ n, μ (U n) ≤ (2 : ℝ≥0∞)⁻¹ ^ n := by
    intro n
    have hsub : U n ⊆ itinerary B ⁻¹' V n := by
      rw [hUO n, hVf n, Set.preimage_iUnion]
      refine Set.iUnion_mono fun i ↦ ?_
      cases f n i with
      | none => exact Set.empty_subset _
      | some σ => exact hOsub σ
    calc μ (U n) ≤ μ (itinerary B ⁻¹' V n) := measure_mono hsub
      _ = μ.map (itinerary B) (V n) :=
        (Measure.map_apply hφ (IsUniformlyEffectiveOpenIn.measurableSet hV.1 n)).symm
      _ ≤ (2 : ℝ≥0∞)⁻¹ ^ n := (hV.2 n).trans_eq (dyadicValue_one n)
  obtain ⟨n, hn⟩ := hx U ⟨⟨EU, hEU, fun n ↦ rfl⟩, hμU⟩
  have hxVn := Set.mem_iInter.mp hxV n
  rw [hVf n, Set.mem_iUnion] at hxVn
  obtain ⟨i, hi⟩ := hxVn
  apply hn
  rw [hUO n, Set.mem_iUnion]
  refine ⟨i, ?_⟩
  cases hfi : f n i with
  | none => simp [hfi] at hi
  | some σ =>
    rw [hfi] at hi
    exact hOmem σ hi

/-- **Transfer of randomness.** For an almost decidable basis `B` relative to `A` for `μ` and every
oracle `A'` above `A`, a point is `μ`-random relative to `A'` exactly when its itinerary is random
relative to `A'` for the image of `μ` under the itinerary map, provided the presentation has a
metric table computable relative to `A`. No computability of `μ` is used. The metric table is
needed only for "random point ⇒ random itinerary": without it the direction fails (ideal points
`q` and `Ω + q` of `ℝ`; the itinerary of `Ω / 2` is caught by a test while `Ω / 2` is random).
Blueprint node `vlm:transfer`. -/
theorem IsAlmostDecidableBasisIn.mem_randomPoints_iff [OpensMeasurableSpace X]
    (hB : IsAlmostDecidableBasisIn P A μ B) (hP : ComputablePresentationIn P A) {A' : Set ℕ}
    (hAA' : charOracle A ≤ᵀ charOracle A') {x : X} :
    x ∈ randomPoints P A' μ ↔ IsMartinLofRandomIn A' (μ.map (itinerary B)) (itinerary B x) :=
  ⟨isMartinLofRandomIn_of_mem_randomPoints hB hP hAA',
    mem_randomPoints_of_isMartinLofRandomIn hB hAA'⟩

/-! ### The image measure -/

/-- The sibling of `σ` at position `k`: the first `k` bits of `σ` followed by the opposite of bit
`k`. The cylinders of the siblings at the positions `k < |σ|` partition the complement of the
cylinder of `σ`. -/
private def sibling (σ : BitString) (k : ℕ) : BitString := σ.take k ++ [!σ.getD k false]

/-- The sibling map is computable. -/
private lemma computable_sibling : Computable fun v : BitString × ℕ ↦ sibling v.1 v.2 :=
  (Primrec.list_append.comp (Primrec.list_take.comp Primrec.snd Primrec.fst)
    (Primrec.list_cons.comp (Primrec.not.comp ((Primrec.list_getD false).comp Primrec.fst
      Primrec.snd)) (Primrec.const []))).to_comp

/-- The mass of a cylinder plus the masses of its siblings is the total mass. -/
private lemma cantorMass_add_sum_sibling (ν : Measure CantorSeq) (σ : BitString) :
    cantorMass ν σ + ∑ k ∈ Finset.range σ.length, cantorMass ν (sibling σ k) = ν Set.univ := by
  induction σ using List.reverseRecOn with
  | nil =>
    have hcyl : cantorCylinder [] = Set.univ := by
      ext w
      simp [cantorCylinder, IsCantorPrefix]
    simp [cantorMass, hcyl]
  | append_singleton σ b ih =>
    have hsib : ∀ k ∈ Finset.range σ.length, sibling (σ ++ [b]) k = sibling σ k := by
      intro k hk
      have hk' : k < σ.length := Finset.mem_range.mp hk
      simp only [sibling]
      rw [List.take_append_of_le_length hk'.le, List.getD_append _ _ _ _ hk']
    have hlast : sibling (σ ++ [b]) σ.length = σ ++ [!b] := by
      simp only [sibling]
      rw [List.take_left' rfl, List.getD_append_right _ _ _ _ le_rfl]
      simp
    rw [List.length_append, List.length_singleton, Finset.sum_range_succ,
      Finset.sum_congr rfl fun k hk ↦ by rw [hsib k hk], hlast, ← ih, cantorMass_add ν σ]
    cases b <;> simp only [Bool.not_false, Bool.not_true] <;> ring

/-- Cylinder masses of a finite measure are finite. -/
private lemma cantorMass_ne_top (ν : Measure CantorSeq) [IsFiniteMeasure ν] (σ : BitString) :
    cantorMass ν σ ≠ ⊤ :=
  measure_ne_top _ _

/-- The partial sums `∑_{k < n} l_k` of a list of rationals (entries past the end count `0`). -/
private def listSum (l : List ℚ) : ℕ → ℚ
  | 0 => 0
  | n + 1 => listSum l n + l.getD n 0

/-- The partial sums of a list, as a real sum. -/
private lemma listSum_cast (l : List ℚ) (n : ℕ) :
    (listSum l n : ℝ) = ∑ k ∈ Finset.range n, (l.getD k 0 : ℝ) := by
  induction n with
  | zero => simp [listSum]
  | succ n ih => rw [listSum, Rat.cast_add, ih, Finset.sum_range_succ]

/-- The sum of a list of rationals is computable. -/
private lemma computable_listSum : Computable fun l : List ℚ ↦ listSum l l.length := by
  have hh : Computable₂ fun (l : List ℚ) (p : ℕ × ℚ) ↦ p.2 + l.getD p.1 0 :=
    (computable₂_ratAdd.comp (Computable.snd.comp Computable.snd)
      ((Primrec.list_getD 0).to_comp.comp Computable.fst
        (Computable.fst.comp Computable.snd))).to₂
  have key : ∀ (l : List ℚ) (n : ℕ),
      Nat.rec (motive := fun _ ↦ ℚ) 0 (fun y ih ↦ ih + l.getD y 0) n = listSum l n := by
    intro l n
    induction n with
    | zero => rfl
    | succ n ih =>
      simp only [listSum]
      exact congrArg (fun z ↦ z + l.getD n 0) ih
  exact (Computable.nat_rec Primrec.list_length.to_comp (Computable.const 0) hh).of_eq
    fun l ↦ key l l.length

/-- The rational `2^{-p}`, cast to the reals. -/
private lemma rat_inv_two_pow_cast (p : ℕ) : (((2 ^ p : ℚ)⁻¹ : ℚ) : ℝ) = (2 : ℝ)⁻¹ ^ p := by
  push_cast
  rw [inv_pow]

/-- A dyadic value as the extended real of a real quotient. -/
private lemma dyadicValue_eq_ofReal (n s : ℕ) :
    dyadicValue n s = ENNReal.ofReal ((n : ℝ) / 2 ^ s) := by
  rw [dyadicValue, ENNReal.ofReal_div_of_pos (by positivity), ENNReal.ofReal_natCast,
    ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_ofNat]

/-- For a finite measure `μ` computable relative to `A` with total mass computable relative to `A`,
the image of `μ` under the itinerary map of an almost decidable basis is computable relative to
`A` on Cantor space. Blueprint node `vlm:itinerary-measure`. -/
theorem IsAlmostDecidableBasisIn.isComputableCantorMeasureIn_map [BorelSpace X]
    [IsFiniteMeasure μ] (hB : IsAlmostDecidableBasisIn P A μ B) (hμ : IsComputableMeasureIn P A μ)
    (hmass : IsComputableRealFamilyIn A fun _ : Unit => (μ Set.univ).toReal) :
    IsComputableCantorMeasureIn A (μ.map (itinerary B)) := by
  classical
  obtain ⟨D, W, hDo, -, hDW⟩ := hB.exists_exterior
  have hφ := hB.measurable_itinerary
  set ν := μ.map (itinerary B) with hν
  have : IsFiniteMeasure ν := Measure.isFiniteMeasure_map μ _
  -- `C σ` is c.e. open and, up to a null set, the complement of the preimage of `[σ]`
  set C : BitString → Set X := fun σ ↦
    ⋃ k ∈ List.range σ.length, if σ.getD k false = true then D k else B k with hCdef
  have hCo : IsCeOpenFamilyIn P A C := isCeOpenFamilyIn_cylCompl hB.isCeOpenFamilyIn hDo
  have hCm : ∀ σ, MeasurableSet (C σ) := fun σ ↦ (isOpen_of_isCeOpenFamilyIn hCo σ).measurableSet
  have hnull : μ (⋃ k, (B k ∪ D k)ᶜ) = 0 := by
    refine measure_iUnion_null fun k ↦ ?_
    by_contra hne
    obtain ⟨n, hn⟩ := ENNReal.exists_inv_two_pow_lt hne
    exact (hn.trans_le ((measure_mono ((hDW k).2 n).1).trans ((hDW k).2 n).2)).false
  have hmassC : ∀ σ, cantorMass ν σ + μ (C σ) = μ Set.univ := by
    intro σ
    have hpre : cantorMass ν σ = μ (itinerary B ⁻¹' cantorCylinder σ) :=
      Measure.map_apply hφ (measurableSet_cantorCylinder σ)
    have hdisj : Disjoint (itinerary B ⁻¹' cantorCylinder σ) (C σ) := by
      rw [Set.disjoint_left]
      intro x hx hxC
      simp only [hCdef, Set.mem_iUnion, List.mem_range, exists_prop] at hxC
      obtain ⟨k, hk, hxk⟩ := hxC
      have hbit : itinerary B x k = σ.getD k false := by
        rw [List.getD_eq_getElem _ _ hk]
        exact hx k hk
      by_cases hσk : σ.getD k false = true
      · simp only [hσk, ↓reduceIte] at hxk
        rw [hσk] at hbit
        have hxB : x ∈ B k := by simpa [itinerary] using hbit
        exact Set.disjoint_left.mp (hDW k).1 hxB hxk
      · simp only [hσk] at hxk
        have h1 : itinerary B x k = true := by simpa [itinerary] using hxk
        exact hσk (hbit ▸ h1)
    have hcover : (itinerary B ⁻¹' cantorCylinder σ ∪ C σ)ᶜ ⊆ ⋃ k, (B k ∪ D k)ᶜ := by
      intro x hx
      simp only [Set.mem_compl_iff, Set.mem_union, not_or] at hx
      obtain ⟨hxP, hxC⟩ := hx
      by_contra hxN
      simp only [Set.mem_iUnion, Set.mem_compl_iff, not_exists, not_not] at hxN
      apply hxP
      change IsCantorPrefix σ (itinerary B x)
      intro i hi
      have hCi : x ∉ (if σ.getD i false = true then D i else B i) := fun h ↦
        hxC (Set.mem_biUnion (List.mem_range.mpr hi) h)
      rw [← List.getD_eq_getElem σ false hi]
      by_cases hσi : σ.getD i false = true
      · simp only [hσi, ↓reduceIte] at hCi
        rw [hσi]
        have h1 : x ∈ B i := (hxN i).resolve_right hCi
        simpa [itinerary] using h1
      · simp only [hσi] at hCi
        rw [Bool.not_eq_true] at hσi
        rw [hσi]
        simpa [itinerary] using hCi
    rw [hpre, ← measure_union hdisj (hCm σ)]
    refine le_antisymm (measure_mono (Set.subset_univ _)) ?_
    calc μ Set.univ
        = μ ((itinerary B ⁻¹' cantorCylinder σ ∪ C σ) ∪
            (itinerary B ⁻¹' cantorCylinder σ ∪ C σ)ᶜ) := by rw [Set.union_compl_self]
      _ ≤ μ (itinerary B ⁻¹' cantorCylinder σ ∪ C σ) +
            μ (itinerary B ⁻¹' cantorCylinder σ ∪ C σ)ᶜ := measure_union_le _ _
      _ = μ (itinerary B ⁻¹' cantorCylinder σ ∪ C σ) := by
          rw [measure_mono_null hcover hnull, add_zero]
  -- the cylinder masses `m σ`, the measures `c σ`, the total mass `M`
  set M : ℝ := (μ Set.univ).toReal with hM
  let m : BitString → ℝ := fun σ ↦ (cantorMass ν σ).toReal
  let c : BitString → ℝ := fun σ ↦ (μ (C σ)).toReal
  have hmc : ∀ σ, m σ + c σ = M := by
    intro σ
    simp only [m, c, hM]
    rw [← ENNReal.toReal_add (cantorMass_ne_top ν σ) (measure_ne_top _ _), hmassC]
  have htel : ∀ σ, m σ + ∑ k ∈ Finset.range σ.length, m (sibling σ k) = M := by
    intro σ
    have h := cantorMass_add_sum_sibling ν σ
    have hu : ν Set.univ = μ Set.univ := by
      rw [hν, Measure.map_apply hφ MeasurableSet.univ, Set.preimage_univ]
    rw [hu] at h
    simp only [m, hM, ← h]
    rw [ENNReal.toReal_add (cantorMass_ne_top ν σ)
      (ENNReal.sum_ne_top.mpr fun k _ ↦ cantorMass_ne_top ν _),
      ENNReal.toReal_sum fun k _ ↦ cantorMass_ne_top ν _]
  have hm0 : ∀ σ, 0 ≤ m σ := fun σ ↦ ENNReal.toReal_nonneg
  obtain ⟨qm, hqm, hqmb⟩ := hmass
  have hqm' : ComputableIn {charOracle A} fun p : ℕ ↦ qm ((), p) :=
    hqm.comp ((ComputableIn.const ()).pair ComputableIn.id)
  have hlowC := hμ.lowerSemicomputable_ceOpen hCo
  -- upper semicomputability of the cylinder masses: `m σ = M - c σ`
  have hup : IsREIn A fun w : BitString × ℚ ↦ m w.1 < w.2 := by
    have h1 : IsREIn A fun v : (BitString × ℚ) × (ℕ × ℚ) ↦
        qm ((), v.2.1) + (2 ^ v.2.1 : ℚ)⁻¹ - v.1.2 < v.2.2 := by
      refine isREIn_of_computableIn_decide A _ ?_
      have ha := (computable₂_ratAdd.computableIn₂ (O := {charOracle A})).comp
        (hqm'.comp (ComputableIn.fst.comp ComputableIn.snd :
          ComputableIn {charOracle A} fun v : (BitString × ℚ) × (ℕ × ℚ) ↦ v.2.1))
        ((computable_rat_inv_two_pow.comp (Computable.fst.comp Computable.snd :
          Computable fun v : (BitString × ℚ) × (ℕ × ℚ) ↦ v.2.1)).computableIn)
      have hs := (computable₂_ratSub.computableIn₂ (O := {charOracle A})).comp ha
        (ComputableIn.snd.comp ComputableIn.fst)
      exact ((computable₂_ratLt.computableIn₂ (O := {charOracle A})).comp hs
        (ComputableIn.snd.comp ComputableIn.snd)).of_eq fun v ↦ rfl
    have h2 : IsREIn A fun v : (BitString × ℚ) × (ℕ × ℚ) ↦ (v.2.2 : ℝ) < c v.1.1 :=
      hlowC.comp ((Computable.fst.comp Computable.fst).pair
        (Computable.snd.comp Computable.snd)).computableIn
    have heq : (fun w : BitString × ℚ ↦ m w.1 < w.2) = fun w ↦ ∃ v : ℕ × ℚ,
        qm ((), v.1) + (2 ^ v.1 : ℚ)⁻¹ - w.2 < v.2 ∧ (v.2 : ℝ) < c w.1 := by
      funext w
      refine propext ⟨fun hw ↦ ?_, fun ⟨⟨p, r⟩, hpr, hrc⟩ ↦ ?_⟩
      · obtain ⟨p, hp⟩ := exists_two_mul_inv_two_pow_lt (w.2 - m w.1) (by linarith)
        have hb := hqmb () p
        rw [abs_lt] at hb
        have hpow : (2 : ℝ)⁻¹ ^ p = (2 ^ p : ℝ)⁻¹ := inv_pow _ _
        obtain ⟨r, hr1, hr2⟩ := exists_rat_btwn (show
          (qm ((), p) : ℝ) + (2 ^ p : ℝ)⁻¹ - w.2 < c w.1 by linarith [hmc w.1])
        refine ⟨(p, r), ?_, hr2⟩
        have : ((qm ((), p) + (2 ^ p : ℚ)⁻¹ - w.2 : ℚ) : ℝ) < r := by push_cast; exact hr1
        exact_mod_cast this
      · have hb := hqmb () p
        rw [abs_lt] at hb
        have hpr' : ((qm ((), p) + (2 ^ p : ℚ)⁻¹ - w.2 : ℚ) : ℝ) < r := by exact_mod_cast hpr
        rw [Rat.cast_sub, Rat.cast_add, rat_inv_two_pow_cast] at hpr'
        linarith [hmc w.1]
    rw [heq]
    exact (h1.and h2).exists
  -- lower semicomputability: `m σ = M - ∑_{k < |σ|} m (sibling σ k)`
  have hlo : IsREIn A fun w : BitString × ℚ ↦ (w.2 : ℝ) < m w.1 := by
    have hF : IsREIn A fun v : BitString × ℕ × ℚ ↦ m (sibling v.1 v.2.1) < v.2.2 :=
      hup.comp ((computable_sibling.comp (Computable.fst.pair
        (Computable.fst.comp Computable.snd))).pair
        (Computable.snd.comp Computable.snd)).computableIn
    have h1 : IsREIn A fun v : (BitString × ℚ) × (List ℚ × ℕ) ↦
        ∀ k (h : k < v.2.1.length), m (sibling v.1.1 k) < v.2.1.get ⟨k, h⟩ :=
      (IsREIn.list_forall_get hF).comp ((Computable.fst.comp Computable.fst).pair
        (Computable.fst.comp Computable.snd)).computableIn
    have h2 : IsREIn A fun v : (BitString × ℚ) × (List ℚ × ℕ) ↦
        v.2.1.length = v.1.1.length :=
      isREIn_of_computable_decide (Primrec.eq.comp
        (Primrec.list_length.comp (Primrec.fst.comp Primrec.snd))
        (Primrec.list_length.comp (Primrec.fst.comp Primrec.fst))).decide.to_comp
    have h3 : IsREIn A fun v : (BitString × ℚ) × (List ℚ × ℕ) ↦
        v.1.2 + listSum v.2.1 v.2.1.length < qm ((), v.2.2) - (2 ^ v.2.2 : ℚ)⁻¹ := by
      refine isREIn_of_computableIn_decide A _ ?_
      have hl : Computable fun v : (BitString × ℚ) × (List ℚ × ℕ) ↦
          v.1.2 + listSum v.2.1 v.2.1.length :=
        computable₂_ratAdd.comp (Computable.snd.comp Computable.fst)
          (computable_listSum.comp (Computable.fst.comp Computable.snd))
      have hr := (computable₂_ratSub.computableIn₂ (O := {charOracle A})).comp
        (hqm'.comp (ComputableIn.snd.comp ComputableIn.snd :
          ComputableIn {charOracle A} fun v : (BitString × ℚ) × (List ℚ × ℕ) ↦ v.2.2))
        ((computable_rat_inv_two_pow.comp (Computable.snd.comp Computable.snd :
          Computable fun v : (BitString × ℚ) × (List ℚ × ℕ) ↦ v.2.2)).computableIn)
      exact ((computable₂_ratLt.computableIn₂ (O := {charOracle A})).comp hl.computableIn hr).of_eq
        fun v ↦ rfl
    have heq : (fun w : BitString × ℚ ↦ (w.2 : ℝ) < m w.1) = fun w ↦ ∃ v : List ℚ × ℕ,
        (v.1.length = w.1.length ∧
          ∀ k (h : k < v.1.length), m (sibling w.1 k) < v.1.get ⟨k, h⟩) ∧
        w.2 + listSum v.1 v.1.length < qm ((), v.2) - (2 ^ v.2 : ℚ)⁻¹ := by
      funext w
      obtain ⟨σ, q⟩ := w
      refine propext ⟨fun hw ↦ ?_, fun ⟨⟨rs, p⟩, ⟨hlen, hrs⟩, hsum⟩ ↦ ?_⟩
      · set n := σ.length with hn
        set δ : ℝ := m σ - q with hδ
        have hδ0 : 0 < δ := by simp only at hw; linarith
        set ε : ℝ := δ / (2 * (n + 1)) with hε
        have hε0 : 0 < ε := by positivity
        have hr : ∀ k, ∃ r : ℚ, m (sibling σ k) < r ∧ (r : ℝ) < m (sibling σ k) + ε :=
          fun k ↦ exists_rat_btwn (lt_add_of_pos_right _ hε0)
        choose r hr1 hr2 using hr
        obtain ⟨p, hp⟩ := exists_two_mul_inv_two_pow_lt (δ / 2) (by positivity)
        have hb := hqmb () p
        rw [abs_lt] at hb
        have hpow : (2 : ℝ)⁻¹ ^ p = (2 ^ p : ℝ)⁻¹ := inv_pow _ _
        refine ⟨((List.range n).map r, p), ⟨by simp [hn], fun k hk ↦ ?_⟩, ?_⟩
        · simp only [List.get_eq_getElem, List.getElem_map, List.getElem_range]
          exact hr1 k
        · have hget : ∀ k ∈ Finset.range n, ((((List.range n).map r).getD k 0 : ℚ) : ℝ) =
              (r k : ℝ) := by
            intro k hk
            rw [List.getD_eq_getElem _ _ (by simpa using hk)]
            simp
          have hsum' : ((listSum ((List.range n).map r) ((List.range n).map r).length : ℚ) : ℝ)
              ≤ ∑ k ∈ Finset.range n, m (sibling σ k) + n * ε := by
            rw [listSum_cast, List.length_map, List.length_range, Finset.sum_congr rfl hget]
            calc ∑ k ∈ Finset.range n, (r k : ℝ)
                ≤ ∑ k ∈ Finset.range n, (m (sibling σ k) + ε) :=
                  Finset.sum_le_sum fun k _ ↦ (hr2 k).le
              _ = ∑ k ∈ Finset.range n, m (sibling σ k) + n * ε := by
                  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          have hnε : (n : ℝ) * ε < δ / 2 := by
            rw [hε, mul_div_assoc']
            rw [div_lt_div_iff₀ (by positivity) (by norm_num)]
            nlinarith
          have htσ := htel σ
          have : ((q + listSum ((List.range n).map r) ((List.range n).map r).length : ℚ) : ℝ) <
              ((qm ((), p) - (2 ^ p : ℚ)⁻¹ : ℚ) : ℝ) := by
            rw [Rat.cast_add, Rat.cast_sub, rat_inv_two_pow_cast]
            linarith
          exact_mod_cast this
      · have hb := hqmb () p
        rw [abs_lt] at hb
        have hsum' : ((q + listSum rs rs.length : ℚ) : ℝ) <
            ((qm ((), p) - (2 ^ p : ℚ)⁻¹ : ℚ) : ℝ) := by
          exact_mod_cast hsum
        rw [Rat.cast_add, Rat.cast_sub, rat_inv_two_pow_cast, listSum_cast] at hsum'
        have hle : ∑ k ∈ Finset.range σ.length, m (sibling σ k) ≤
            ∑ k ∈ Finset.range rs.length, (rs.getD k 0 : ℝ) := by
          rw [hlen]
          refine Finset.sum_le_sum fun k hk ↦ ?_
          have hk' : k < rs.length := by rw [hlen]; exact Finset.mem_range.mp hk
          rw [List.getD_eq_getElem _ _ hk']
          exact (hrs k hk').le
        have htσ := htel σ
        change (q : ℝ) < m σ
        linarith
    rw [heq]
    exact ((h2.and h1).and h3).exists
  -- choose a rational `q` with `m σ - 2^{-(s+1)} < q < m σ`
  have hG : IsREIn A fun v : (BitString × ℕ) × ℚ ↦
      (v.2 : ℝ) < m v.1.1 ∧ m v.1.1 < ((v.2 + (2 ^ (v.1.2 + 1) : ℚ)⁻¹ : ℚ) : ℝ) := by
    have hmap : Computable fun v : (BitString × ℕ) × ℚ ↦
        (v.1.1, v.2 + (2 ^ (v.1.2 + 1) : ℚ)⁻¹) :=
      (Computable.fst.comp Computable.fst).pair (computable₂_ratAdd.comp Computable.snd
        (computable_rat_inv_two_pow.comp (Computable.succ.comp
          (Computable.snd.comp Computable.fst))))
    exact (hlo.comp ((Computable.fst.comp Computable.fst).pair
      Computable.snd).computableIn).and (hup.comp hmap.computableIn)
  have htot : ∀ a : BitString × ℕ, ∃ q : ℚ,
      (q : ℝ) < m a.1 ∧ m a.1 < ((q + (2 ^ (a.2 + 1) : ℚ)⁻¹ : ℚ) : ℝ) := by
    intro a
    have hpos : (0 : ℝ) < (((2 ^ (a.2 + 1) : ℚ)⁻¹ : ℚ) : ℝ) := by
      rw [rat_inv_two_pow_cast]
      positivity
    obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show m a.1 - (((2 ^ (a.2 + 1) : ℚ)⁻¹ : ℚ) : ℝ) <
      m a.1 by linarith)
    exact ⟨q, hq2, by push_cast at hq1 ⊢; linarith⟩
  obtain ⟨g, hg, hgG⟩ := IsREIn.exists_computableIn_choice hG htot
  refine ⟨fun σ s ↦ ratDyadicFloor (g (σ, s) + (2 ^ (s + 1) : ℚ)⁻¹) s, ?_, fun σ s ↦ ?_⟩
  · have ht := (computable₂_ratAdd.computableIn₂ (O := {charOracle A})).comp hg
      ((computable_rat_inv_two_pow.comp (Computable.succ.comp Computable.snd)).computableIn)
    exact ComputableIn₂.mk (((computable_ratDyadicFloor.computableIn₂
      (O := {charOracle A})).comp ht ComputableIn.snd).of_eq fun v ↦ rfl)
  · obtain ⟨hq1, hq2⟩ := hgG (σ, s)
    set t : ℚ := g (σ, s) + (2 ^ (s + 1) : ℚ)⁻¹ with ht
    have hmσ : cantorMass ν σ = ENNReal.ofReal (m σ) :=
      (ENNReal.ofReal_toReal (cantorMass_ne_top ν σ)).symm
    have ht0 : 0 ≤ t * (2 ^ s : ℕ) := by
      have : (0 : ℝ) ≤ (t : ℝ) := (hm0 σ).trans hq2.le
      have : (0 : ℚ) ≤ t := by exact_mod_cast this
      positivity
    have hfl1 : ((ratDyadicFloor t s : ℕ) : ℚ) ≤ t * (2 ^ s : ℕ) := by
      rw [ratDyadicFloor_eq_floor]
      exact Nat.floor_le ht0
    have hfl2 : t * (2 ^ s : ℕ) < (ratDyadicFloor t s : ℚ) + 1 := by
      rw [ratDyadicFloor_eq_floor]
      exact Nat.lt_floor_add_one _
    have hfl1' : ((ratDyadicFloor t s : ℕ) : ℝ) ≤ (t : ℝ) * 2 ^ s := by
      exact_mod_cast hfl1
    have hfl2' : (t : ℝ) * 2 ^ s < (ratDyadicFloor t s : ℝ) + 1 := by
      exact_mod_cast hfl2
    have hq1' : (g (σ, s) : ℝ) < m σ := hq1
    have htcast : (t : ℝ) = g (σ, s) + (2 : ℝ)⁻¹ ^ (s + 1) := by
      rw [ht, Rat.cast_add, rat_inv_two_pow_cast]
    have hq2' : m σ < (t : ℝ) := hq2
    have h2s : (0 : ℝ) < 2 ^ s := by positivity
    have hpow : (2 : ℝ)⁻¹ ^ (s + 1) = 1 / 2 ^ s / 2 := by
      rw [pow_succ, inv_pow]
      field_simp
    have h1s : (0 : ℝ) < 1 / 2 ^ s := by positivity
    rw [hmσ, dyadicValue_eq_ofReal, dyadicValue_eq_ofReal, Nat.cast_one,
      ← ENNReal.ofReal_add (hm0 σ) h1s.le, ← ENNReal.ofReal_add (by positivity) h1s.le]
    constructor
    · refine ENNReal.ofReal_le_ofReal ?_
      have : ((ratDyadicFloor t s : ℕ) : ℝ) / 2 ^ s ≤ t := by
        rw [div_le_iff₀ h2s]
        exact hfl1'
      linarith
    · refine ENNReal.ofReal_le_ofReal ?_
      have : (t : ℝ) < ((ratDyadicFloor t s : ℕ) : ℝ) / 2 ^ s + 1 / 2 ^ s := by
        rw [← add_div, lt_div_iff₀ h2s]
        exact hfl2'
      linarith

end Kolmogorov.PointToSet
