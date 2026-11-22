/-
Copyright (c) 2026 Emma Dinowitz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emma Dinowitz
-/
import KolmogorovMathlib.PointToSet.Measure.Ergodic.TypicalPoints
import KolmogorovMathlib.PointToSet.Measure.Ergodic.BlockCoding

/-!
# Theorem 1(a): the upper bound

Theorem 1(a) of the note *Orbit complexity of Martin-Löf random points equals entropy*: on a
compact space, for an `A`-represented ergodic map `T` and an `A`-computable invariant probability
measure `μ`, at every `μ`-random point `x` relative to `A` and every `ε > 0`,
`limsup_n K_n^A(x, T, ε) / n ≤ h_μ(T)`.

Proof. Take an `A`-computable partition `U_1, …, U_p` of diameter `< ε` (Lemma 2) with its
measurable partition `Q`, and `ω = φ(x)` (Lemma 3). The partial `A`-computable map that, on a
word `w`, enumerates `O_w = ⋂_{k<n} T^{-k} U_{w_k}` as a union of ideal balls and outputs the index
`i_w` of the centre of the first ball gives `K^A(i_w) ≤ K^A(w) + O(1)`; for `w = ω↾n`, `x` and
`x_{i_w}` lie in `O_w`, whose `n` cells have diameter `< ε`, so `x_{i_w} ∈ B_n(x, T, ε)` and
`K_n^A(x, T, ε) ≤ K^A(ω↾n) + O(1)`. Then `limsup_n K^A(ω↾n)/n ≤ h_ν(σ)` (`ω` is generic,
`isGenericPoint_symbolicCode`, and `limsup_wordComplexity_le_shiftEntropy`), `h_ν(σ) = h_μ(T, Q)`
(`shiftEntropy_codedMeasure`) and `h_μ(T, Q) ≤ h_μ(T)` (`entropyRate_le_ksEntropy`).

The cells `O_w` are shown to be c.e. open uniformly in `w` with the chains of basic balls of
`BowenCeOpen` (`isCeOpenFamilyIn_bowenChainSet`); the search is `IsREIn.exists_partrecIn_choice`
and the invariance of complexity is `oracle_tuple_bounds_composition`.

Blueprint node `erg:theorem-one`.
-/

namespace Kolmogorov.PointToSet

open Filter Set MeasureTheory
open scoped Topology ENNReal Computability

variable {X : Type*} [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]

/-! ### The coding step -/

omit [CompactSpace X] [MeasurableSpace X] [BorelSpace X] in
/-- The cells `O_w = ⋂_{k<|w|} T^{-k} U_{w_k}` of the words `w` over a c.e. open family `U` form
a c.e. open family, uniformly in `w`: an `A`-c.e. relation `E` lists, for each word, basic balls
whose union is `O_w`. -/
private theorem exists_isREIn_wordCell {p : ℕ} [NeZero p] (P : Presentation X) (T : X → X)
    (A : Set ℕ) (hP : ComputablePresentationIn P A) (hTA : IsRepresentedMapIn P P A T)
    {U : Fin p → Set X} (hU : IsCeOpenFamilyIn P A U) :
    ∃ E : List (Fin p) × (ℕ × ℚ) → Prop, IsREIn A E ∧ ∀ (w : List (Fin p)) (y : X),
      (∃ b, E (w, b) ∧ y ∈ basicBall P b) ↔ ∀ k < w.length, T^[k] y ∈ U (w.getD k 0) := by
  obtain ⟨EU, hEU, hUeq⟩ := hU
  obtain ⟨R', hR're, hR's, hR'small⟩ := exists_bowenChainRep P T A hP hTA
  have hlt := birkhoff_computableIn_lt A _ hP
  -- step condition at time `k` for the word `w`: the ball lies, with a rational certificate,
  -- inside a listed ball of `U_{w_k}`
  let C : (List (Fin p) × ℕ) × (ℕ × ℚ) → Prop := fun v ↦
    0 < v.2.2 ∧ ∃ c : ℕ × ℚ, EU (v.1.1.getD v.1.2 0, c) ∧
      dist (P.ι c.1) (P.ι v.2.1) < ((c.2 - v.2.2 : ℚ) : ℝ)
  have hCre : IsREIn A C := by
    have h0 : IsREIn A fun v : (List (Fin p) × ℕ) × (ℕ × ℚ) ↦ (0 : ℚ) < v.2.2 :=
      isREIn_of_computable_decide (computable₂_ratLt.comp (Computable.const 0)
        (Computable.snd.comp Computable.snd))
    have h1 : IsREIn A fun v : ((List (Fin p) × ℕ) × (ℕ × ℚ)) × (ℕ × ℚ) ↦
        EU (v.1.1.1.getD v.1.1.2 0, v.2) :=
      hEU.comp ((((Primrec.list_getD (0 : Fin p)).to_comp : Computable₂ _).comp
        (Computable.fst.comp (Computable.fst.comp Computable.fst))
        (Computable.snd.comp (Computable.fst.comp Computable.fst))).pair
          Computable.snd).computableIn
    have h2 : IsREIn A fun v : ((List (Fin p) × ℕ) × (ℕ × ℚ)) × (ℕ × ℚ) ↦
        dist (P.ι v.2.1) (P.ι v.1.2.1) < ((v.2.2 - v.1.2.2 : ℚ) : ℝ) :=
      hlt.comp (((Computable.fst.comp Computable.snd).pair
        (Computable.fst.comp (Computable.snd.comp Computable.fst))).pair
        (computable₂_ratSub.comp (Computable.snd.comp Computable.snd)
          (Computable.snd.comp (Computable.snd.comp Computable.fst)))).computableIn
    exact h0.and (h1.and h2).exists
  have hCloc : ∀ a k c z, C ((a, k), c) → z ∈ basicBall P c → ∃ δ : ℝ, 0 < δ ∧
      ∀ c' : ℕ × ℚ, 0 < c'.2 → (c'.2 : ℝ) < δ → z ∈ basicBall P c' → C ((a, k), c') := by
    rintro a k c z ⟨_, c₀, hc₀, hd⟩ hz
    obtain ⟨δ, hδ, hsmall⟩ := bowenStep_small_lt (P := P) (bowenStep_dist_lt hd hz)
    exact ⟨δ, hδ, fun c' hc'0 _ hzc' ↦ ⟨hc'0, c₀, hc₀, hsmall c' ‹_› hzc'⟩⟩
  obtain ⟨E, hE, hEq⟩ :=
    isCeOpenFamilyIn_bowenChainSet P T A hR're hR's hR'small hCre hCloc
  have key : ∀ (w : List (Fin p)) (y : X), y ∈ bowenChainSet P T C w w.length ↔
      ∀ k < w.length, T^[k] y ∈ U (w.getD k 0) := by
    intro w y
    constructor
    · intro hy k hk
      obtain ⟨c, ⟨_, c₀, hc₀, hd⟩, hyc⟩ := hy k hk
      rw [hUeq]
      refine Set.mem_iUnion₂.mpr ⟨c₀, hc₀, ?_⟩
      have h := bowenStep_dist_lt hd hyc
      rw [dist_comm] at h
      exact h
    · intro hy k hk
      have hk' := hy k hk
      rw [hUeq] at hk'
      obtain ⟨c₀, hc₀, hyc₀⟩ := Set.mem_iUnion₂.mp hk'
      have hd : dist (P.ι c₀.1) (T^[k] y) < (c₀.2 : ℝ) := by
        rw [dist_comm]
        exact hyc₀
      obtain ⟨δ, hδ, hsmall⟩ := bowenStep_small_lt (P := P) hd
      obtain ⟨c, hc0, hcδ, hyc⟩ := bowenChain_exists_small_ball P (T^[k] y) hδ
      exact ⟨c, ⟨hc0, c₀, hc₀, hsmall c hcδ hyc⟩, hyc⟩
  refine ⟨fun wb ↦ E ((wb.1, wb.1.length), wb.2), hE.comp ((Computable.fst.pair
    (Primrec.list_length.to_comp.comp Computable.fst)).pair Computable.snd).computableIn,
    fun w y ↦ ?_⟩
  have h := hEq (w, w.length)
  dsimp only at h
  rw [← key, h]
  simp only [Set.mem_iUnion₂, Set.mem_ofPred_eq, exists_prop]

omit [MeasurableSpace X] [BorelSpace X] in
/-- The coding step `K_n^A(x, T, ε) ≤ K^A(ω↾n) + O(1)`: for a c.e. open family `U` refining
a family `Q` of cells of diameter `< ε`, there is a constant `c` such that, whenever the orbit of
`x` follows the itinerary `ω` through `U`, every Bowen ball `B_n(x, T, ε)` contains an ideal
point `x_i` with `K^A(i) ≤ K^A(ω↾n) + c`. The index `i` is the centre of the first basic ball
found in the c.e. open cell `O_{ω↾n}`. -/
theorem orbitUpper_exists_orbitCode_le {p : ℕ} [NeZero p] (P : Presentation X) (T : X → X)
    (A : Set ℕ) (hP : ComputablePresentationIn P A) (hTA : IsRepresentedMapIn P P A T)
    {U Q : Fin p → Set X} (hU : IsCeOpenFamilyIn P A U) (hUQ : ∀ j, U j ⊆ Q j) {ε : ℝ}
    (hdiam : ∀ j, Metric.diam (Q j) < ε) :
    ∃ c : ℕ, ∀ (x : X) (ω : ℕ → Fin p), (∀ k, T^[k] x ∈ U (ω k)) → ∀ n, ∃ i,
      P.ι i ∈ bowenBall T n x ε ∧ oracleNatComplexity A i ≤ wordComplexity A ω n + c := by
  obtain ⟨EO, hEO, hEOiff⟩ := exists_isREIn_wordCell P T A hP hTA hU
  let G : List (Fin p) × (ℕ × ℚ) → Prop := fun wb ↦ EO wb ∧ 0 < wb.2.2
  have hG : IsREIn A G := hEO.and (isREIn_of_computable_decide
    (computable₂_ratLt.comp (Computable.const 0) (Computable.snd.comp Computable.snd)))
  obtain ⟨g, hg, hgdom, hgsound⟩ := hG.exists_partrecIn_choice
  let F : ℕ →. ℕ := fun m ↦
    (g ((Encodable.decode m : Option (List (Fin p))).getD [])).map Prod.fst
  have hdec : Computable fun m : ℕ ↦ (Encodable.decode m : Option (List (Fin p))).getD [] :=
    Computable.option_getD Computable.decode (Computable.const [])
  have hF : PartrecIn {charOracle A} F :=
    (hg.comp hdec.computableIn).map (Computable.fst.comp Computable.snd).computableIn.to₂
  obtain ⟨c, hc⟩ := exists_natComplexity_le_of_partrecIn A F hF
  refine ⟨c, fun x ω hxω n ↦ ?_⟩
  set w := wordPrefix ω n with hw
  have hwlen : w.length = n := List.length_ofFn
  have hwget : ∀ k < w.length, w.getD k 0 = ω k := by
    intro k hk
    rw [List.getD_eq_getElem _ _ hk]
    simp only [hw, wordPrefix, List.getElem_ofFn]
  have hxcell : ∀ k < w.length, T^[k] x ∈ U (w.getD k 0) := by
    intro k hk
    rw [hwget k hk]
    exact hxω k
  obtain ⟨b, hEb, hxb⟩ := (hEOiff w x).mpr hxcell
  have hb0 : 0 < b.2 := by
    have h : dist x (P.ι b.1) < (b.2 : ℝ) := hxb
    exact_mod_cast (dist_nonneg.trans_lt h)
  have hdom : (g w).Dom := (hgdom w).mpr ⟨b, hEb, hb0⟩
  have hb' : G (w, (g w).get hdom) := hgsound w _ (Part.get_mem hdom)
  have hcenter : P.ι ((g w).get hdom).1 ∈ basicBall P ((g w).get hdom) :=
    Metric.mem_ball_self (by exact_mod_cast hb'.2)
  have hicell := (hEOiff w _).mp ⟨_, hb'.1, hcenter⟩
  have hbdd : ∀ j, Bornology.IsBounded (Q j) := fun j ↦
    isCompact_univ.isBounded.subset (Set.subset_univ _)
  refine ⟨((g w).get hdom).1, ?_, ?_⟩
  · rw [mem_bowenBall_iff]
    intro k hk
    have hk' : k < w.length := hwlen ▸ hk
    exact (Metric.dist_le_diam_of_mem (hbdd _) (hUQ _ (hxcell k hk'))
      (hUQ _ (hicell k hk'))).trans_lt (hdiam _)
  · have hFm : ((g w).get hdom).1 ∈ F (Encodable.encode w) := by
      simp only [F, Encodable.encodek, Option.getD_some]
      exact Part.mem_map _ (Part.get_mem hdom)
    exact hc _ _ hFm

omit [CompactSpace X] [MeasurableSpace X] [BorelSpace X] in
/-- At order `n ≥ 1`, the finite-scale orbit cost is at most `K^A(i) / n` for every ideal point
`x_i` of the Bowen ball `B_n(x, T, ε)`. -/
theorem finiteScaleBSCost_one_le (P : Presentation X) (T : X → X) (A : Set ℕ) (x : X)
    {n : ℕ} (hn : 1 ≤ n) {ε : ℝ} {i : ℕ} (hi : P.ι i ∈ bowenBall T n x ε) :
    finiteScaleBSCost P T (fun _ ↦ 1) A x n ε ≤ (oracleNatComplexity A i : ℝ≥0∞) / n := by
  have hsum : birkhoffSum T (fun _ ↦ (1 : ℝ)) n (P.ι i) = n := by
    simp only [birkhoffSum, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
  have hpos : 0 < birkhoffSum T (fun _ ↦ (1 : ℝ)) n (P.ι i) := by
    rw [hsum]
    exact_mod_cast hn
  unfold finiteScaleBSCost
  simp only [show n ≠ 0 by omega, ↓reduceIte]
  refine (iInf_le _ i).trans ((iInf_le _ hi).trans ((iInf_le _ hpos).trans ?_))
  rw [hsum, ENNReal.ofReal_natCast]

/-! ### Theorem 1(a) -/

/-- Theorem 1(a), at a fixed scale: `limsup_n K_n^A(x, T, ε) / n ≤ h_μ(T)` at every `μ`-random
point. Blueprint node `erg:theorem-one`. -/
theorem orbitComplexityAt_snd_le_ksEntropy (P : Presentation X) (T : X → X)
    (hT : Continuous T) (A : Set ℕ) (μ : Measure X) [IsProbabilityMeasure μ]
    (hA : IsMeasureAdmissible P T μ A) (herg : Ergodic T μ) {x : X}
    (hx : x ∈ randomPoints P A μ) {ε : ℝ} (hε : 0 < ε) :
    (orbitComplexityAt P T A x ε).2 ≤ Ergodic.ksEntropy μ T := by
  have : Nonempty X := ⟨x⟩
  obtain ⟨p, U, Q, hp, hU, hQ, hUQ, hdiam⟩ :=
    exists_computablePartition P A μ hA.1 hA.2.2 hε
  have : NeZero p := ⟨hp.ne'⟩
  have hTm : MeasurePreserving T μ μ := herg.toMeasurePreserving
  have hdom : x ∈ codingDomain T U := randomPoints_subset_codingDomain hA hTm hU hx
  set ω := symbolicCode T U x with hω
  obtain ⟨c, hc⟩ := orbitUpper_exists_orbitCode_le P T A hA.1 hA.2.1 hU.1 hUQ hdiam
  have hcost : ∀ n, 1 ≤ n → finiteScaleBSCost P T (fun _ ↦ 1) A x n ε ≤
      (wordComplexity A ω n : ℝ≥0∞) / n + (c : ℝ≥0∞) / n := by
    intro n hn
    obtain ⟨i, hi, hK⟩ := hc x ω (iterate_mem_symbolicCode hU.2.1 hdom) n
    refine (finiteScaleBSCost_one_le P T A x hn hi).trans ?_
    rw [← ENNReal.add_div]
    gcongr
    exact_mod_cast hK
  have := isProbabilityMeasure_codedMeasure hT.measurable hU
  have hgen := isGenericPoint_symbolicCode P T A μ hA herg hU hx
  have hlim := limsup_wordComplexity_le_shiftEntropy A (codedMeasure μ T U)
    (ergodic_codedMeasure herg hU).toMeasurePreserving hgen
  rw [shiftEntropy_codedMeasure hTm hU hQ hUQ] at hlim
  have hc0 : Tendsto (fun n : ℕ ↦ (c : ℝ≥0∞) / n) atTop (𝓝 0) := by
    have h := ENNReal.Tendsto.const_mul ENNReal.tendsto_inv_nat_nhds_zero
      (Or.inr (ENNReal.natCast_ne_top c))
    rw [mul_zero] at h
    simpa only [div_eq_mul_inv] using h
  calc (orbitComplexityAt P T A x ε).2
      ≤ limsup (fun n : ℕ ↦ (wordComplexity A ω n : ℝ≥0∞) / n + (c : ℝ≥0∞) / n) atTop :=
        limsup_le_limsup (eventually_atTop.mpr ⟨1, hcost⟩)
    _ = limsup (fun n : ℕ ↦ (wordComplexity A ω n : ℝ≥0∞) / n) atTop :=
        ENNReal.limsup_add_of_right_tendsto_zero hc0 _
    _ ≤ Ergodic.entropyRate μ T Q := hlim
    _ ≤ Ergodic.ksEntropy μ T := Ergodic.entropyRate_le_ksEntropy μ T hQ

/-- Theorem 1(a): `K̄^A(x, T) ≤ h_μ(T)` at every `μ`-random point.
Blueprint node `erg:theorem-one`. -/
theorem upperOrbitComplexity_le_ksEntropy (P : Presentation X) (T : X → X)
    (hT : Continuous T) (A : Set ℕ) (μ : Measure X) [IsProbabilityMeasure μ]
    (hA : IsMeasureAdmissible P T μ A) (herg : Ergodic T μ) {x : X}
    (hx : x ∈ randomPoints P A μ) :
    (orbitComplexities P T A x).2 ≤ Ergodic.ksEntropy μ T := by
  rw [orbitComplexities_eq_iSup_orbitComplexityAt]
  exact iSup_le fun q ↦
    orbitComplexityAt_snd_le_ksEntropy P T hT A μ hA herg hx (dyadicRadius_pos q)

end Kolmogorov.PointToSet
