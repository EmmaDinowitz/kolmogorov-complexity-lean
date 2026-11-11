/-
Copyright (c) 2026 Emma Dinowitz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emma Dinowitz
-/
import KolmogorovMathlib.PointToSet.Measure.EffectiveNull
import KolmogorovMathlib.PointToSet.Measure.EntropyLaw

/-!
# Feng–Huang entropies and essential bounds of the local entropies (§4.1, §4.2)

Let `μ` be a Borel probability measure and `A` an oracle admissible for `(X, d, T, μ)`
(E. Dinowitz, *Entropy of non-invariant measures and orbit complexity of random points*, §4).

* `measureEntropy_eq_lintegral_orbitComplexities` (Proposition 4.1): the Feng–Huang entropies
  are the `μ`-integrals of the orbit complexities.
* Theorem 4.3(a), for every admissible `A`:
  `ess sup h̲_μ = sup_{x ∈ R_A} K̲^A(x) = h̲(R_A, T) = inf {h̲(Z, T) : μ(Z) = 1}`
  (`iSup_randomPoints_orbitComplexities_fst`, `lowerEntropy_randomPoints`,
  `essSup_lowerLocalEntropy_eq_iInf_lowerEntropy`). The upper bound uses that the exceptional
  set is a countable union of `μ`-null effectively closed sets, which contain no random point.
* Theorem 4.3(b): `ess sup h̄_μ = min_B sup_{x ∈ R_B} K̄^B(x) = inf {h̄(Z, T) : μ(Z) = 1}`, the
  minimum over admissible oracles being attained on an upper cone
  (`essSup_upperLocalEntropy_le_iSup_randomPoints`, `exists_cone_iSup_randomPoints_snd`,
  `essSup_upperLocalEntropy_eq_iInf_oracle`, `essSup_upperLocalEntropy_eq_iInf_upperEntropy`).
* Theorem 4.3(c): `ess inf h̲_μ = max_B inf_{x ∈ R_B} K̲^B(x) = inf {h̲(Z, T) : μ(Z) > 0}`, and
  the same with the upper quantities (`iInf_randomPoints_orbitComplexities_le_essInf`,
  `exists_cone_iInf_randomPoints`, `essInf_localEntropy_eq_iSup_oracle`,
  `essInf_localEntropy_eq_iInf_entropy`).

Auxiliary results: `measure_randomPoints_eq_one` (`μ(R_A) = 1` as an outer measure), the
general lower bounds `essSup_lowerLocalEntropy_le_lowerEntropy` and
`essSup_upperLocalEntropy_le_upperEntropy` (`ess sup ≤ h(Z, T)` whenever `μ(Z) = 1`), and the
effective scale-wise bound `orbitComplexityAt_fst_le_essSup_of_mem_randomPoints`.

Sets `Z` are arbitrary; `μ Z` is the outer measure.

Blueprint nodes `meas:feng-huang`, `meas:essential`.
-/

namespace Kolmogorov.PointToSet

open Filter Set MeasureTheory
open scoped Topology ENNReal Computability

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

/-! ### Auxiliary facts -/

/-- The random points have full outer measure: `μ(R_A) = 1`. -/
theorem measure_randomPoints_eq_one (P : Presentation X) (A : Set ℕ) (μ : Measure X)
    [IsProbabilityMeasure μ] : μ (randomPoints P A μ) = 1 := by
  refine le_antisymm prob_le_one ?_
  calc (1 : ℝ≥0∞) = μ univ := measure_univ.symm
    _ ≤ μ (randomPoints P A μ) + μ (randomPoints P A μ)ᶜ := by
        rw [← union_compl_self (randomPoints P A μ)]
        exact measure_union_le _ _
    _ = μ (randomPoints P A μ) := by rw [measure_compl_randomPoints, add_zero]

omit [MetricSpace X] [BorelSpace X] in
/-- A set of positive measure meets every set of full outer measure in a set of positive
outer measure. -/
private lemma measure_inter_ne_zero {μ : Measure X} [IsProbabilityMeasure μ] {Z E : Set X}
    (hZ : μ Z = 1) (hE : MeasurableSet E) (hE0 : μ E ≠ 0) : μ (Z ∩ E) ≠ 0 := by
  intro h0
  have h1 : μ Z ≤ μ (Z ∩ E) + μ Eᶜ := by
    refine (measure_mono fun x hx ↦ ?_).trans (measure_union_le _ _)
    by_cases hxE : x ∈ E
    · exact Or.inl ⟨hx, hxE⟩
    · exact Or.inr hxE
  rw [h0, zero_add, prob_compl_eq_one_sub hE, hZ] at h1
  exact absurd h1 (not_le.2 (ENNReal.sub_lt_self ENNReal.one_ne_top one_ne_zero hE0))

/-- General lower bound: if `μ(Z) = 1` (outer measure) and a quantity `H` equals the supremum
over `Z` of functions `g D` on an upper cone of oracles, where `g D` agrees with `f` at the
points random relative to every admissible `D`, then `ess sup f ≤ H`. -/
private lemma essSup_le_of_cone (P : Presentation X) (T : X → X) (hT : Continuous T)
    (μ : Measure X) [IsProbabilityMeasure μ] {f : X → ℝ≥0∞} (hf : Measurable f)
    (g : Set ℕ → X → ℝ≥0∞)
    (hg : ∀ D, IsMeasureAdmissible P T μ D → ∀ x ∈ randomPoints P D μ, g D x = f x)
    {Z : Set X} (hZ : μ Z = 1) {H : ℝ≥0∞}
    (hcone : ∃ B : Set ℕ, ∀ D : Set ℕ, charOracle B ≤ᵀ charOracle D → H = ⨆ x ∈ Z, g D x) :
    essSup f μ ≤ H := by
  obtain ⟨B, hB⟩ := hcone
  obtain ⟨C, hC⟩ := exists_measureAdmissible_base P T hT μ
  have hD := hC (oracleJoin B C) (oracle_joins_right B C)
  rw [hB _ (oracle_joins B C)]
  refine le_of_forall_lt_imp_le_of_dense fun s hs ↦ ?_
  have hE : MeasurableSet {x | s < f x} := measurableSet_lt measurable_const hf
  have hE0 : μ {x | s < f x} ≠ 0 := by
    intro h0
    have : essSup f μ ≤ s := essSup_le_of_ae_le s (by
      rw [EventuallyLE, ae_iff]
      simpa only [not_le] using h0)
    exact absurd hs (not_lt.2 this)
  obtain ⟨x, hxZE, hxR⟩ := exists_mem_randomPoints_of_measure_pos P (oracleJoin B C) μ
    (measure_inter_ne_zero hZ hE hE0)
  calc s ≤ f x := hxZE.2.le
    _ = g (oracleJoin B C) x := (hg _ hD x hxR).symm
    _ ≤ ⨆ y ∈ Z, g (oracleJoin B C) y :=
        le_iSup₂ (f := fun y _ ↦ g (oracleJoin B C) y) x hxZE.1

/-- On the random points relative to an admissible `D`, the lower orbit complexity is the
lower local entropy. -/
private lemma orbitComplexities_fst_eq (P : Presentation X) (T : X → X) (hT : Continuous T)
    (μ : Measure X) [IsProbabilityMeasure μ] :
    ∀ D, IsMeasureAdmissible P T μ D → ∀ x ∈ randomPoints P D μ,
      (orbitComplexities P T D x).1 = (localEntropy μ T x).1 := fun D hD _ hx ↦ by
  rw [orbitComplexities_eq_localEntropy P T hT D μ hD hx]

/-- On the random points relative to an admissible `D`, the upper orbit complexity is the
upper local entropy. -/
private lemma orbitComplexities_snd_eq (P : Presentation X) (T : X → X) (hT : Continuous T)
    (μ : Measure X) [IsProbabilityMeasure μ] :
    ∀ D, IsMeasureAdmissible P T μ D → ∀ x ∈ randomPoints P D μ,
      (orbitComplexities P T D x).2 = (localEntropy μ T x).2 := fun D hD _ hx ↦ by
  rw [orbitComplexities_eq_localEntropy P T hT D μ hD hx]

/-- General lower bound, lower version: if `μ(Z) = 1` then `ess sup h̲_μ ≤ h̲(Z, T)`. -/
theorem essSup_lowerLocalEntropy_le_lowerEntropy (P : Presentation X) (T : X → X)
    (hT : Continuous T) (μ : Measure X) [IsProbabilityMeasure μ] {Z : Set X} (hZ : μ Z = 1) :
    essSup (fun x ↦ (localEntropy μ T x).1) μ ≤ lowerEntropy T Z :=
  essSup_le_of_cone P T hT μ (measurable_localEntropy μ hT).fst
    (fun D x ↦ (orbitComplexities P T D x).1) (orbitComplexities_fst_eq P T hT μ) hZ
    (entropy_effectiveCharacterization_allOracles_cone P T hT Z)

/-- General lower bound, upper version: if `μ(Z) = 1` then `ess sup h̄_μ ≤ h̄(Z, T)`. -/
theorem essSup_upperLocalEntropy_le_upperEntropy (P : Presentation X) (T : X → X)
    (hT : Continuous T) (μ : Measure X) [IsProbabilityMeasure μ] {Z : Set X} (hZ : μ Z = 1) :
    essSup (fun x ↦ (localEntropy μ T x).2) μ ≤ upperEntropy P T Z :=
  essSup_le_of_cone P T hT μ (measurable_localEntropy μ hT).snd
    (fun D x ↦ (orbitComplexities P T D x).2) (orbitComplexities_snd_eq P T hT μ) hZ
    (upperEntropy_pointToSet_cone P T hT Z)

omit [MeasurableSpace X] [BorelSpace X] in
/-- The union of the Bowen balls `B_n(ι i, r)` with `N₀ ≤ n`, `1 ≤ n` and `K^A(i) < q n` is
`A`-c.e. open. -/
private lemma isCeOpenIn_cheapBalls (P : Presentation X) (T : X → X) (A : Set ℕ)
    (hP : ComputablePresentationIn P A) (hTA : IsRepresentedMapIn P P A T) (N₀ : ℕ)
    (q r : ℚ) :
    IsCeOpenIn P A (⋃ k ∈ {k : ℕ × ℕ | N₀ ≤ k.1 ∧ 1 ≤ k.1 ∧
        (oracleNatComplexity A k.2 : ℝ) < ((q * k.1 : ℚ) : ℝ)},
      bowenBall T k.1 (P.ι k.2) (r : ℝ)) := by
  have hU := isCeOpenFamilyIn_bowenBall P T A hP hTA
  have hg : Computable fun d : ℕ × ℕ ↦ (d.1, d.2, r) :=
    Computable.fst.pair (Computable.snd.pair (Computable.const r))
  have hV := hU.comp hg
  have hn : Primrec fun w : Unit × (ℕ × ℕ) ↦ w.2.1 := Primrec.fst.comp Primrec.snd
  have hi : Primrec fun w : Unit × (ℕ × ℕ) ↦ w.2.2 := Primrec.snd.comp Primrec.snd
  have h₁ : IsREIn A fun w : Unit × (ℕ × ℕ) ↦ N₀ ≤ w.2.1 :=
    isREIn_of_computable_decide (Primrec.nat_le.comp (Primrec.const N₀) hn).decide.to_comp
  have h₂ : IsREIn A fun w : Unit × (ℕ × ℕ) ↦ 1 ≤ w.2.1 :=
    isREIn_of_computable_decide (Primrec.nat_le.comp (Primrec.const 1) hn).decide.to_comp
  have hm : Computable fun w : Unit × (ℕ × ℕ) ↦ q * (w.2.1 : ℚ) :=
    computable₂_ratMul.comp (Computable.const q)
      (ComputableReals.computable_natCastRat.comp hn.to_comp)
  have h₃ : IsREIn A fun w : Unit × (ℕ × ℕ) ↦
      (oracleNatComplexity A w.2.2 : ℝ) < ((q * w.2.1 : ℚ) : ℝ) :=
    (isREIn_oracleNatComplexity_lt A).comp
      (f := fun w : Unit × (ℕ × ℕ) ↦ (w.2.2, q * (w.2.1 : ℚ))) (hi.to_comp.pair hm).computableIn
  obtain ⟨E, hE, hEq⟩ := hV.iUnion_of_isREIn (h₁.and (h₂.and h₃))
  have hc : Computable fun b : ℕ × ℚ ↦ ((), b) := (Computable.const ()).pair Computable.id
  refine ⟨fun b ↦ E ((), b), hE.comp hc.computableIn, ?_⟩
  rw [← hEq ()]

/-- Theorem 4.3(a), the effective upper bound at a fixed dyadic scale: at every point random
relative to an admissible `A`, the lower orbit complexity rate at scale `2^{-p}` is at most
`ess sup h̲_μ`. The exceptional set is covered by the complements of `A`-c.e. open sets of full
measure, which contain all random points. -/
theorem orbitComplexityAt_fst_le_essSup_of_mem_randomPoints (P : Presentation X) (T : X → X)
    (hT : Continuous T) (A : Set ℕ) (μ : Measure X) [IsProbabilityMeasure μ]
    (hA : IsMeasureAdmissible P T μ A) {x : X} (hx : x ∈ randomPoints P A μ) (p : ℕ) :
    (orbitComplexityAt P T A x (dyadicRadius p)).1 ≤
      essSup (fun x ↦ (localEntropy μ T x).1) μ := by
  set S := essSup (fun x ↦ (localEntropy μ T x).1) μ with hS
  by_contra hlt
  rw [not_le] at hlt
  obtain ⟨q, hq0, hSq, hqa⟩ := ENNReal.lt_iff_exists_rat_btwn.1 hlt
  change S < ENNReal.ofReal q at hSq
  change ENNReal.ofReal q < _ at hqa
  set r : ℚ := (2 : ℚ)⁻¹ ^ p with hr
  have hrd : ((r : ℚ) : ℝ) = dyadicRadius p := by simp [hr, dyadicRadius]
  have hr0 : (0 : ℝ) < (r : ℝ) := hrd ▸ dyadicRadius_pos p
  -- the exceptional set is null
  have hN : μ {y | ¬ (orbitComplexities P T A y).1 ≤ S} = 0 := by
    rw [← ae_iff]
    filter_upwards [ae_orbitComplexities_eq_localEntropy P T hT A μ hA,
      ENNReal.ae_le_essSup (μ := μ) fun x ↦ (localEntropy μ T x).1] with y hy hyS
    rw [hy]
    exact hyS
  -- the cheap balls
  set U : ℕ → Set X := fun N₀ ↦ ⋃ k ∈ {k : ℕ × ℕ | N₀ ≤ k.1 ∧ 1 ≤ k.1 ∧
      (oracleNatComplexity A k.2 : ℝ) < ((q * k.1 : ℚ) : ℝ)},
      bowenBall T k.1 (P.ι k.2) (r : ℝ) with hU
  have hUc : ∀ N₀, (U N₀)ᶜ ⊆ {y | ¬ (orbitComplexities P T A y).1 ≤ S} := by
    intro N₀ y hy
    simp only [mem_ofPred_eq, not_le]
    refine hSq.trans_le ?_
    refine le_trans ?_ (orbitComplexityAt_le_orbitComplexities P T A y hr0).1
    refine le_liminf_of_le (by isBoundedDefault) ?_
    filter_upwards [eventually_ge_atTop (max N₀ 1)] with n hn
    have hn1 : 1 ≤ n := le_of_max_le_right hn
    obtain ⟨i, hi, heq⟩ := entropiesAndOrbitComplexities_attained P T hT A y n hn1 _ hr0
    rw [entropiesAndOrbitComplexities_rate P T hT A y n hn1 _ hr0]
    have hK : orbitComplexityNat P T A y n r = oracleNatComplexity A i := by
      simp [orbitComplexityNat, heq]
    have hge : (q : ℝ) * n ≤ oracleNatComplexity A i := by
      by_contra hcon
      rw [not_le] at hcon
      refine hy (mem_biUnion (x := (n, i)) ⟨le_of_max_le_left hn, hn1, ?_⟩
        (mem_bowenBall_symm hi))
      push_cast
      exact hcon
    rw [hK, ENNReal.le_div_iff_mul_le (Or.inl (by exact_mod_cast (by omega : n ≠ 0)))
      (Or.inl (ENNReal.natCast_ne_top n))]
    rw [← ENNReal.ofReal_natCast n, ← ENNReal.ofReal_mul (by exact_mod_cast hq0),
      ← ENNReal.ofReal_natCast]
    exact ENNReal.ofReal_le_ofReal hge
  -- the random point lies in every `U N₀`
  have hxU : ∀ N₀, x ∈ U N₀ := fun N₀ ↦
    randomPoints_subset_of_isCeOpenIn P A μ hA.1 hA.2.2
      (isCeOpenIn_cheapBalls P T A hA.1 hA.2.1 N₀ q r) (measure_mono_null (hUc N₀) hN) hx
  have hfreq : ∃ᶠ n in atTop,
      finiteScaleBSCost P T (fun _ ↦ 1) A x n (dyadicRadius p) ≤ ENNReal.ofReal q := by
    refine frequently_atTop.2 fun N₀ ↦ ?_
    obtain ⟨⟨n, i⟩, ⟨hnN, hn1, hKi⟩, hxi⟩ := mem_iUnion₂.1 (hxU N₀)
    refine ⟨n, hnN, ?_⟩
    rw [← hrd, entropiesAndOrbitComplexities_rate P T hT A x n hn1 _ hr0]
    have hle := orbitComplexityNat_le_of_mem P T A (x := x) (n := n) (r := (r : ℝ))
      (mem_bowenBall_symm hxi)
    refine ENNReal.div_le_of_le_mul ?_
    rw [← ENNReal.ofReal_natCast n, ← ENNReal.ofReal_mul (by exact_mod_cast hq0),
      ← ENNReal.ofReal_natCast]
    refine ENNReal.ofReal_le_ofReal ?_
    have : ((orbitComplexityNat P T A x n r : ℕ) : ℝ) ≤ oracleNatComplexity A i := by
      exact_mod_cast hle
    push_cast at hKi
    linarith
  exact absurd (liminf_le_of_frequently_le' hfreq) (not_le.2 hqa)

/-- Proposition 4.1: the Feng–Huang entropies are the integrals of the orbit complexities
relative to an admissible oracle. Blueprint node `meas:feng-huang`. -/
theorem measureEntropy_eq_lintegral_orbitComplexities (P : Presentation X) (T : X → X)
    (hT : Continuous T) (A : Set ℕ) (μ : Measure X) [IsProbabilityMeasure μ]
    (hA : IsMeasureAdmissible P T μ A) :
    (measureEntropy μ T).1 = ∫⁻ x, (orbitComplexities P T A x).1 ∂μ ∧
      (measureEntropy μ T).2 = ∫⁻ x, (orbitComplexities P T A x).2 ∂μ := by
  have h := ae_orbitComplexities_eq_localEntropy P T hT A μ hA
  exact ⟨lintegral_congr_ae (h.mono fun _ hx ↦ (congrArg Prod.fst hx).symm),
    lintegral_congr_ae (h.mono fun _ hx ↦ (congrArg Prod.snd hx).symm)⟩

/-! ### Theorem 4.3(a) -/

/-- Theorem 4.3(a): for every admissible oracle the supremum of the lower orbit complexity
over the random points is the essential supremum of the lower local entropy.
Blueprint node `meas:essential`. -/
theorem iSup_randomPoints_orbitComplexities_fst (P : Presentation X) (T : X → X)
    (hT : Continuous T) (A : Set ℕ) (μ : Measure X) [IsProbabilityMeasure μ]
    (hA : IsMeasureAdmissible P T μ A) :
    ⨆ x ∈ randomPoints P A μ, (orbitComplexities P T A x).1 =
      essSup (fun x ↦ (localEntropy μ T x).1) μ := by
  refine le_antisymm (iSup₂_le fun x hx ↦ ?_) (essSup_le_of_ae_le _ ?_)
  · rw [orbitComplexities_eq_iSup_orbitComplexityAt]
    exact iSup_le fun p ↦
      orbitComplexityAt_fst_le_essSup_of_mem_randomPoints P T hT A μ hA hx p
  · filter_upwards [ae_mem_randomPoints P A μ] with x hx
    rw [← orbitComplexities_fst_eq P T hT μ A hA x hx]
    exact le_iSup₂ (f := fun y _ ↦ (orbitComplexities P T A y).1) x hx

/-- Theorem 4.3(a): the Bowen entropy of the set of random points relative to an admissible
oracle is the essential supremum of the lower local entropy.
Blueprint node `meas:essential`. -/
theorem lowerEntropy_randomPoints (P : Presentation X) (T : X → X) (hT : Continuous T)
    (A : Set ℕ) (μ : Measure X) [IsProbabilityMeasure μ] (hA : IsMeasureAdmissible P T μ A) :
    lowerEntropy T (randomPoints P A μ) = essSup (fun x ↦ (localEntropy μ T x).1) μ := by
  refine le_antisymm ?_ (essSup_lowerLocalEntropy_le_lowerEntropy P T hT μ
    (measure_randomPoints_eq_one P A μ))
  rw [entropy_effectiveCharacterization_allOracles_pointToSet P T hT,
    ← iSup_randomPoints_orbitComplexities_fst P T hT A μ hA]
  exact iInf_le _ A

/-- Theorem 4.3(a): `ess sup h̲_μ = inf {h̲(Z, T) : μ(Z) = 1}`.
Blueprint node `meas:essential`. -/
theorem essSup_lowerLocalEntropy_eq_iInf_lowerEntropy (P : Presentation X) (T : X → X)
    (hT : Continuous T) (μ : Measure X) [IsProbabilityMeasure μ] :
    essSup (fun x ↦ (localEntropy μ T x).1) μ =
      ⨅ (Z : Set X) (_ : μ Z = 1), lowerEntropy T Z := by
  refine le_antisymm (le_iInf₂ fun Z hZ ↦ essSup_lowerLocalEntropy_le_lowerEntropy P T hT μ hZ)
    ?_
  obtain ⟨C, hC⟩ := exists_measureAdmissible_base P T hT μ
  have hA := hC C (TuringReducible.refl _)
  rw [← lowerEntropy_randomPoints P T hT C μ hA]
  exact iInf₂_le (f := fun (Z : Set X) (_ : μ Z = 1) ↦ lowerEntropy T Z) _
    (measure_randomPoints_eq_one P C μ)

/-! ### Theorem 4.3(b) -/

/-- Theorem 4.3(b): for every admissible oracle the supremum of the upper orbit complexity
over the random points is at least the essential supremum of the upper local entropy.
Blueprint node `meas:essential`. -/
theorem essSup_upperLocalEntropy_le_iSup_randomPoints (P : Presentation X) (T : X → X)
    (hT : Continuous T) (B : Set ℕ) (μ : Measure X) [IsProbabilityMeasure μ]
    (hB : IsMeasureAdmissible P T μ B) :
    essSup (fun x ↦ (localEntropy μ T x).2) μ ≤
      ⨆ x ∈ randomPoints P B μ, (orbitComplexities P T B x).2 := by
  refine essSup_le_of_ae_le _ ?_
  filter_upwards [ae_mem_randomPoints P B μ] with x hx
  rw [← orbitComplexities_snd_eq P T hT μ B hB x hx]
  exact le_iSup₂ (f := fun y _ ↦ (orbitComplexities P T B y).2) x hx

/-- Theorem 4.3(b): on an upper cone of admissible oracles the supremum of the upper orbit
complexity over the random points equals the essential supremum of the upper local entropy.
Blueprint node `meas:essential`. -/
theorem exists_cone_iSup_randomPoints_snd (P : Presentation X) (T : X → X)
    (hT : Continuous T) (μ : Measure X) [IsProbabilityMeasure μ] :
    ∃ C : Set ℕ, ∀ B : Set ℕ, charOracle C ≤ᵀ charOracle B →
      IsMeasureAdmissible P T μ B ∧
        ⨆ x ∈ randomPoints P B μ, (orbitComplexities P T B x).2 =
          essSup (fun x ↦ (localEntropy μ T x).2) μ := by
  set S := essSup (fun x ↦ (localEntropy μ T x).2) μ
  have hN : μ {x | ¬ (localEntropy μ T x).2 ≤ S} = 0 :=
    ae_iff.1 (ENNReal.ae_le_essSup (μ := μ) fun x ↦ (localEntropy μ T x).2)
  obtain ⟨C₁, hC₁⟩ := exists_oracle_randomPoints_disjoint P μ hN
  obtain ⟨C₂, hC₂⟩ := exists_measureAdmissible_base P T hT μ
  refine ⟨oracleJoin C₁ C₂, fun B hB ↦ ?_⟩
  have hBa := hC₂ B ((oracle_joins_right C₁ C₂).trans hB)
  refine ⟨hBa, le_antisymm (iSup₂_le fun x hx ↦ ?_)
    (essSup_upperLocalEntropy_le_iSup_randomPoints P T hT B μ hBa)⟩
  rw [orbitComplexities_snd_eq P T hT μ B hBa x hx]
  have := Set.disjoint_left.1 (hC₁ B ((oracle_joins C₁ C₂).trans hB)) hx
  simpa using this

/-- Theorem 4.3(b): `ess sup h̄_μ = min_B sup_{x ∈ R_B} K̄^B(x)` over admissible oracles.
Blueprint node `meas:essential`. -/
theorem essSup_upperLocalEntropy_eq_iInf_oracle (P : Presentation X) (T : X → X)
    (hT : Continuous T) (μ : Measure X) [IsProbabilityMeasure μ] :
    essSup (fun x ↦ (localEntropy μ T x).2) μ =
      ⨅ (B : Set ℕ) (_ : IsMeasureAdmissible P T μ B),
        ⨆ x ∈ randomPoints P B μ, (orbitComplexities P T B x).2 := by
  refine le_antisymm (le_iInf₂ fun B hB ↦
    essSup_upperLocalEntropy_le_iSup_randomPoints P T hT B μ hB) ?_
  obtain ⟨C, hC⟩ := exists_cone_iSup_randomPoints_snd P T hT μ
  obtain ⟨hCa, hCeq⟩ := hC C (TuringReducible.refl _)
  exact (iInf₂_le C hCa).trans hCeq.le

/-- Theorem 4.3(b): `ess sup h̄_μ = inf {h̄(Z, T) : μ(Z) = 1}`.
Blueprint node `meas:essential`. -/
theorem essSup_upperLocalEntropy_eq_iInf_upperEntropy (P : Presentation X) (T : X → X)
    (hT : Continuous T) (μ : Measure X) [IsProbabilityMeasure μ] :
    essSup (fun x ↦ (localEntropy μ T x).2) μ =
      ⨅ (Z : Set X) (_ : μ Z = 1), upperEntropy P T Z := by
  refine le_antisymm (le_iInf₂ fun Z hZ ↦ essSup_upperLocalEntropy_le_upperEntropy P T hT μ hZ)
    ?_
  obtain ⟨C, hC⟩ := exists_cone_iSup_randomPoints_snd P T hT μ
  obtain ⟨_, hCeq⟩ := hC C (TuringReducible.refl _)
  refine (iInf₂_le (f := fun (Z : Set X) (_ : μ Z = 1) ↦ upperEntropy P T Z) _
    (measure_randomPoints_eq_one P C μ)).trans ?_
  rw [upperEntropy_pointToSet P T hT, ← hCeq]
  exact iInf_le _ C

/-! ### Theorem 4.3(c) -/

/-- Theorem 4.3(c): for every admissible oracle the infima of the orbit complexities over the
random points are at most the essential infima of the local entropies.
Blueprint node `meas:essential`. -/
theorem iInf_randomPoints_orbitComplexities_le_essInf (P : Presentation X) (T : X → X)
    (hT : Continuous T) (B : Set ℕ) (μ : Measure X) [IsProbabilityMeasure μ]
    (hB : IsMeasureAdmissible P T μ B) :
    ⨅ x ∈ randomPoints P B μ, (orbitComplexities P T B x).1 ≤
        essInf (fun x ↦ (localEntropy μ T x).1) μ ∧
      ⨅ x ∈ randomPoints P B μ, (orbitComplexities P T B x).2 ≤
        essInf (fun x ↦ (localEntropy μ T x).2) μ := by
  refine ⟨le_essInf_of_ae_le _ ?_, le_essInf_of_ae_le _ ?_⟩ <;>
    filter_upwards [ae_mem_randomPoints P B μ] with x hx
  · rw [← orbitComplexities_fst_eq P T hT μ B hB x hx]
    exact iInf₂_le (f := fun y _ ↦ (orbitComplexities P T B y).1) x hx
  · rw [← orbitComplexities_snd_eq P T hT μ B hB x hx]
    exact iInf₂_le (f := fun y _ ↦ (orbitComplexities P T B y).2) x hx

/-- Theorem 4.3(c): on an upper cone of admissible oracles the infima of the orbit
complexities over the random points equal the essential infima of the local entropies.
Blueprint node `meas:essential`. -/
theorem exists_cone_iInf_randomPoints (P : Presentation X) (T : X → X) (hT : Continuous T)
    (μ : Measure X) [IsProbabilityMeasure μ] :
    ∃ C : Set ℕ, ∀ B : Set ℕ, charOracle C ≤ᵀ charOracle B →
      IsMeasureAdmissible P T μ B ∧
        ⨅ x ∈ randomPoints P B μ, (orbitComplexities P T B x).1 =
          essInf (fun x ↦ (localEntropy μ T x).1) μ ∧
        ⨅ x ∈ randomPoints P B μ, (orbitComplexities P T B x).2 =
          essInf (fun x ↦ (localEntropy μ T x).2) μ := by
  set S₁ := essInf (fun x ↦ (localEntropy μ T x).1) μ
  set S₂ := essInf (fun x ↦ (localEntropy μ T x).2) μ
  have hN₁ : μ {x | ¬ S₁ ≤ (localEntropy μ T x).1} = 0 :=
    ae_iff.1 (ae_essInf_le (μ := μ) (f := fun x ↦ (localEntropy μ T x).1))
  have hN₂ : μ {x | ¬ S₂ ≤ (localEntropy μ T x).2} = 0 :=
    ae_iff.1 (ae_essInf_le (μ := μ) (f := fun x ↦ (localEntropy μ T x).2))
  obtain ⟨C₁, hC₁⟩ := exists_oracle_randomPoints_disjoint P μ hN₁
  obtain ⟨C₂, hC₂⟩ := exists_oracle_randomPoints_disjoint P μ hN₂
  obtain ⟨C₃, hC₃⟩ := exists_measureAdmissible_base P T hT μ
  refine ⟨oracleJoin C₁ (oracleJoin C₂ C₃), fun B hB ↦ ?_⟩
  have h₁ : charOracle C₁ ≤ᵀ charOracle B := (oracle_joins _ _).trans hB
  have h₂₃ : charOracle (oracleJoin C₂ C₃) ≤ᵀ charOracle B := (oracle_joins_right _ _).trans hB
  have h₂ : charOracle C₂ ≤ᵀ charOracle B := (oracle_joins _ _).trans h₂₃
  have hBa := hC₃ B ((oracle_joins_right _ _).trans h₂₃)
  have hle := iInf_randomPoints_orbitComplexities_le_essInf P T hT B μ hBa
  refine ⟨hBa, le_antisymm hle.1 (le_iInf₂ fun x hx ↦ ?_),
    le_antisymm hle.2 (le_iInf₂ fun x hx ↦ ?_)⟩
  · rw [orbitComplexities_fst_eq P T hT μ B hBa x hx]
    simpa using Set.disjoint_left.1 (hC₁ B h₁) hx
  · rw [orbitComplexities_snd_eq P T hT μ B hBa x hx]
    simpa using Set.disjoint_left.1 (hC₂ B h₂) hx

/-- Theorem 4.3(c): `ess inf h̲_μ = max_B inf_{x ∈ R_B} K̲^B(x)` over admissible oracles, and
the same with the upper quantities. Blueprint node `meas:essential`. -/
theorem essInf_localEntropy_eq_iSup_oracle (P : Presentation X) (T : X → X)
    (hT : Continuous T) (μ : Measure X) [IsProbabilityMeasure μ] :
    essInf (fun x ↦ (localEntropy μ T x).1) μ =
        ⨆ (B : Set ℕ) (_ : IsMeasureAdmissible P T μ B),
          ⨅ x ∈ randomPoints P B μ, (orbitComplexities P T B x).1 ∧
      essInf (fun x ↦ (localEntropy μ T x).2) μ =
        ⨆ (B : Set ℕ) (_ : IsMeasureAdmissible P T μ B),
          ⨅ x ∈ randomPoints P B μ, (orbitComplexities P T B x).2 := by
  obtain ⟨C, hC⟩ := exists_cone_iInf_randomPoints P T hT μ
  obtain ⟨hCa, hC₁, hC₂⟩ := hC C (TuringReducible.refl _)
  refine ⟨le_antisymm ?_ (iSup₂_le fun B hB ↦
      (iInf_randomPoints_orbitComplexities_le_essInf P T hT B μ hB).1),
    le_antisymm ?_ (iSup₂_le fun B hB ↦
      (iInf_randomPoints_orbitComplexities_le_essInf P T hT B μ hB).2)⟩
  · exact hC₁.symm.le.trans (le_iSup₂ (f := fun B (_ : IsMeasureAdmissible P T μ B) ↦
      ⨅ x ∈ randomPoints P B μ, (orbitComplexities P T B x).1) C hCa)
  · exact hC₂.symm.le.trans (le_iSup₂ (f := fun B (_ : IsMeasureAdmissible P T μ B) ↦
      ⨅ x ∈ randomPoints P B μ, (orbitComplexities P T B x).2) C hCa)

/-- Theorem 4.3(c): `ess inf h̲_μ = inf {h̲(Z, T) : μ(Z) > 0}` and
`ess inf h̄_μ = inf {h̄(Z, T) : μ(Z) > 0}`. Blueprint node `meas:essential`. -/
theorem essInf_localEntropy_eq_iInf_entropy (P : Presentation X) (T : X → X)
    (hT : Continuous T) (μ : Measure X) [IsProbabilityMeasure μ] :
    essInf (fun x ↦ (localEntropy μ T x).1) μ =
        ⨅ (Z : Set X) (_ : μ Z ≠ 0), lowerEntropy T Z ∧
      essInf (fun x ↦ (localEntropy μ T x).2) μ =
        ⨅ (Z : Set X) (_ : μ Z ≠ 0), upperEntropy P T Z := by
  obtain ⟨C, hC⟩ := exists_cone_iInf_randomPoints P T hT μ
  -- the sets where a local entropy is below a level above its essential infimum
  have hpos : ∀ (f : X → ℝ≥0∞) (s : ℝ≥0∞), essInf f μ < s → μ {x | f x < s} ≠ 0 := by
    intro f s hs h0
    have : s ≤ essInf f μ := le_essInf_of_ae_le s (by
      rw [EventuallyLE, ae_iff]
      simpa only [not_le] using h0)
    exact absurd hs (not_lt.2 this)
  refine ⟨le_antisymm (le_iInf₂ fun Z hZ ↦ ?_) ?_, le_antisymm (le_iInf₂ fun Z hZ ↦ ?_) ?_⟩
  · obtain ⟨B, hB⟩ := entropy_effectiveCharacterization_allOracles_cone P T hT Z
    obtain ⟨_, hD, -⟩ := hC (oracleJoin B C) (oracle_joins_right B C)
    obtain ⟨x, hxZ, hx⟩ := exists_mem_randomPoints_of_measure_pos P (oracleJoin B C) μ hZ
    rw [hB _ (oracle_joins B C), ← hD]
    exact (iInf₂_le (f := fun y _ ↦ (orbitComplexities P T (oracleJoin B C) y).1) x hx).trans
      (le_iSup₂ (f := fun y _ ↦ (orbitComplexities P T (oracleJoin B C) y).1) x hxZ)
  · refine le_of_forall_gt_imp_ge_of_dense fun s hs ↦ ?_
    exact iInf₂_le_of_le _ (hpos _ s hs) (lowerEntropy_le_of_localEntropy_le P T hT μ _ s
      fun x hx ↦ le_of_lt hx)
  · obtain ⟨B, hB⟩ := upperEntropy_pointToSet_cone P T hT Z
    obtain ⟨_, -, hD⟩ := hC (oracleJoin B C) (oracle_joins_right B C)
    obtain ⟨x, hxZ, hx⟩ := exists_mem_randomPoints_of_measure_pos P (oracleJoin B C) μ hZ
    rw [hB _ (oracle_joins B C), ← hD]
    exact (iInf₂_le (f := fun y _ ↦ (orbitComplexities P T (oracleJoin B C) y).2) x hx).trans
      (le_iSup₂ (f := fun y _ ↦ (orbitComplexities P T (oracleJoin B C) y).2) x hxZ)
  · refine le_of_forall_gt_imp_ge_of_dense fun s hs ↦ ?_
    exact iInf₂_le_of_le _ (hpos _ s hs) (upperEntropy_le_of_localEntropy_le P T hT μ _ s
      fun x hx ↦ le_of_lt hx)

end Kolmogorov.PointToSet
